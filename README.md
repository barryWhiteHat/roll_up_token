# roll_up token: Snark based multi-ERC20 side chain
A merkle tree is used to track accounts and balances. Multiple tokens are supported but each token requires a seperate account. The owner of a balance can sign a transaction to transfer part or all of the balance to another account, these transactions are batched via snark to prove that the state transition was correct. 

We maintain data availability by making sure that each zkSNARK proof must reveal a list of leaves that were changed and the amount that was transferred inside the EVM. We rely on Ethereum for data availability guarantees. 

The merkle tree is depth 24, which supports 2^24 accounts. Each account can only hold a single token. The system supports multiple tokens.

## Glossary of terms/variables:

 * roll up: a method of aggragateing multiple signatures and/or merkle tree updates inside a snark. 
 * Operator: The party aggragets many signatures into a single snark transaction. 
 * Circuit: The code that defines what the snark allows.
 * Block: ethereum block
 * Epoch: roll_up block which is a single snark proof of a state transition which containts many transactions.
 * account tree this is the merkle tree that stores a mapping between accounts and balances
 * account_tree_depth (24) this is the number of layers in the account merkle tree

### Tree leaf format

Each account is represented by a single leaf in the balance tree. It is calculated by hashing the following components in the following order;
```python
leaf = H(pubkey_x, pubkey_y, balance, nonce, token)
```

#### Inputs
 * public key X (254 bits)
 * public key Y (254 bits) 
 * token (16 bits)
 * nonce (32 bits)
 * balance (128 bits) 

### New token addition
Each token needs to be added before it can be transfered. The EVM maintains a list of 2^16 to tokens. The deposits, transfers, and withdraws reference a token index in this list. Anyone can add a new token by calling the `add_token` function on the smart contract. 

To prevent squating attacks, users need to burn 1 ether in order to add a new token.

#### Pseudo code

##### Smart contract

```javascript
    // Add a new token
    function add_token() {
    
    }
```

### Deposits
Deposits and account creation use the same mechanism. Deposits create a new account with an initial balance, and account creation without a deposit leaves the balance at zero. These deposits get added to deposit lists that are ordered by fee.

Deposits are made directly to the smart contract, they are queued up in a 'deposit block'. They are aggregated into a sha256 merkle tree. The operator then makes a snark that translates this merkle tree into a pedersen commitment merkle tree. Which is then appended to the account merkle tree. 

It is also possible for zero value deposits to avoid the fee queue for deposit. Which allows operators to add users who don't have gas to pay for fees. 

1. User deposits `amount` of`token` to the smart contract
2. Smart contract verifies that the tokens have been transferred. 
3. Smart contract saves this in the same format as the transfer data to, from, amount which is saved in a list by fee per token executed in the same way operators order transfers.
4. deposit_list[fee_eth].append(deposit)
5. Once the block is full a depositor can add it to the tree.

Alternatively, depositors can specify multiple zero balance leaves and bypass the token transfer check and fee payment. After enough transactions have been batched, the operator can execute them together exactly the same as the fee queue.

#### Sudo code

##### Smart contract

```javascript
    // deposit with fee
    function deposit_fee(owner, token, amount, fee) {
        require(token.transfer(amount + fee, this));
        deposit_block_fee[fee].append(merkle_tree_append_sha256(owner.pubkey_x, owner.pubkey_y, balance, 0, token_addr));
    }

    // deposit with no fee
    function deposit_no_fee(owner, token) {
        deposit_block_no_fee[msg.sender].append(merkle_tree_append_sha256(owner.pubkey_x, owner.pubkey_y, 0, 0, token));
    }

    function deposit_fee(proof, fee) {
        require(deposit_block_fee[fee].full == true);
        validate_proof(proof, block[fee].root, account_offset);
        token.send(msg.sender, fee*blocksize);
        account_offset += tree_size;
    }
    
    function deposit_no_fee(proof) {
        require(deposit_block_no_fee[msg.sender].full == true);
        validate_proof(proof, deposit_block_no_fee[msg.sender].root, account_offset);
        account_offset += tree_size;
    }         
        
    function validate_snark(proof, address) {
        require(deposit_block[msg.sender].full == true);
        validate_proof(proof, block[msg.sender].root, account_offset);
        token.send(msg.sender, fee*blocksize);
        account_offset += tree_size;
    }
```

##### Snark 
```javascript
    // append account to existing account merkle tree.
    function add_accounts(deposit_tree_sha256, account_tree, account_offset ) {
    
        to_pedersen(deposit_tree_sha256)
        * account offset is the first leaf in the merke tree that is zero
        * At this leaf make a merkle proof of the for the zero element
        * Take N steps up the tree from this leaf
        * Where n is the depth of hte deposit_tree
        * Insert the deposit_tree_pedersen here.
        * return this merkle root
        
    }
```

### Withdraw mechanism
Leaves can be withdrawn as follows. 

The transaction format is 10 bytes:
 
   * 3 bytes `from`
   * 3 bytes `to`
   * 2 bytes `amount`
   * 2 bytes `token`

The `to` address of `0` is a special address, it is the 'Withdraw' address. Any balance you send to leaf index `0` has a special meaning. The public key for leaf zero does not exit.

When the zkSNARK proof is submitted by the operator, if the destination is `0` the on-chain 'withdrawable balance' for the `from` leaf index is incremented by the amount, the amount needs converting from floating point to Wei unsigned integer.

The `from` address must have added a `withdraw_address` anyone can then send a transaction that sends the funds to this address.

The `withdraw_address` can be set by creating a snark that validates a signature and merkle tree proof for any previous state of the snark where the signatures nominates a `withdraw_address` which is permenently saved in the smart contract.

Transfers to the zero address should avoid the token type check.


#### Sudo Code
##### Smart contract 
```javascript
    function withdraw(uint epoch, uint i) {
        // make sure you cannot withdraw until proof has been provided
        require(blocks[epoch].finalized == true);
        transcation = withdraw[epoch][i];
        address = withdraw_address[transaction.from];
        token withdraw_token[withdraw_address[transaction.from]];
        address.send(token, to_256_bit_number(transaction.amount));
    }
    
    function nominate_withdraw_address(proof_of_membership, leaf_address, nominate_withdraw_address) {
        snark_verify(proof_of_membership);
        // don't let us update this
        require(withdraw_address[leaf_address] == 0);
        withdraw_address[leaf_address] = nominate_withdraw_address;    
    }
```

##### snark
``` javascript
    proof_of_membership()
        public address
        public nominated_withdraw_addrss
        public merkle_root
        leaf = leaves[address]
        merkle_proof(leaf, merkle_tree, address)
        signatures_validate(sig, nominated_withdraw_addrss)
```

### Data availablity

This approach is based [upon](https://ethresear.ch/t/on-chain-scaling-to-potentially-500-tx-sec-through-mass-tx-validation/3477)

Each transaction record is 10 bytes, and consists of:

1. `from` leaf (3 bytes)
2. `to` leaf   (3 bytes)
3. `amount`    (2 bytes) 
4. `token`     (2 bytes)

For each batch, the records are concatenated together and then hashed to produce a single digest. This digest is passed as a public input to the zkSNARK circuit to ensure that the on-chain and in-circuit data match.

The `from` and `to` offsets specify the leaves within the tree, the size required for the offset depends on the depth of the tree. $TreeCapacity = 2^{tree\_depth}$, offset size in bits is $log_2(tree\_depth)$.


### Dependent Payments

We want to allow for dependent payments. This allows us to do atomic swaps at almost no cost in terms of constraints.

The user can signal that their transaction is dependent upon a previous one 
by signaling via signature. These fields in the signature format are 
`"dependent_payments": [[to,from,amount], [to,from,amount]]`. Where `to`, `from`, `amount` define the transaction that this one depends upon. 

Then the snark confirms that each transaction has its dependecies included. 

#### Snark sudo-code
```javascript
// checks if this tx depends upon the previous tx
if (signature[i].dependent_payment[0] != 0) {
    require(signature[i].dependent_payment[0].to == signature[i-1].to);
    require(signature[i].dependent_payment[0].from == signature[i-1].from);
    require(signature[i].dependent_payment[0].amount == signature[i-1].amount);
    
}
// checks if this tx depends upon the next tx
if (signature[i].dependent_payment[1] != 0) {
    require(signature  require(signature[i].dependent_payment[1].to == signature[1+1].to);
    require(signature[i].dependent_payment[1].from == signature[i+1].from);
    require(signature[i].dependent_payment[1].amount == signature[i+1].amount);s[i] == signature[i+1]);
}
```
### Atomic Swaps
We can use this to do atomic swaps where
Alice has 10 tokens A 
Bob has 1 token B 
They can trade trustlessly by creating dependent transactions by doing the following 
1. Bob and Alice agree to trade 1 token B for 10 token A. 
2. Bob creates a transaction that sends 1 token B to Alice. That is dependent upon Alice sending 10 token A to bob. 
3. Alice creates a transction that sends 10 token A to bob that is dependent upon a transfer to 1 token B to alice. 
4. They share their transactions with each other and broadcast them to the operator.

We can only do pairwise dependent transactions here.

## Transaction Fees

We need to pay fees so the operator is incentivized to create blocks and process transactions. We could use the naive approach and allow the operator to use conditional payments to get their transactions included in a block. However this is expensive and halves the throughput of our system. 

Its also important that users can pay for fees in different tokens. This allows us to batch together more transactions in each block. As we have a larger pool we can include we can make blocks faster.

So we force the operator to commit to the fees in the EVM and then validate this is correct in the snark.


### Fee calcultaion
At commitment time the EVM can calculate how much fees are owed to the operator by taking the number of tokens of each token type and multiplying this by that tokens fee type. 

If the operator did not include that token in their fee commitment they recive a fee of zero. 

## Transaction Format


### Snark Transactions

EdDSA signatures are used by users to send transactions. The operator uses these transactions to make a snark proof.

These are provided to the operator in the off-chain transaction. The transaction is represented as a JSON document:

```json
{
   "tx": {
      "from": nnn,
      "nonce": nnn,
      "to": nnn,
      "amount": nnn,
      "fee": nnn, 
      "dependent_payments": [[to, from, amount], [to, from, amount]]
      "hash_to_from_amount": nnn
   }
   "sig": {
       "A": [pubkey.x, pubkey.y],
       "R": [R.x, R.y],
       "s": nnn
   }
}
```

To verify the transaction:

```python
m = H(tx.from, tx.to, tx.amount, tx.fee)

assert True == eddsa_verify(m, sig.A, sig.R, sig.s)
```

Fields:

 * `tx` - Dictionary with transaction details
   * `from` - Leaf index (account_tree_depth bit unsigned) of sending account
   * `nonce` - account_tree_depth bit Nonce, to prevent transaction replays
   * `to` - Leaf index (24 bit unsigned) of receiving account
   * `amount` - Balance to transfer (16 bit unsigned)
   * `fee` - The fee to pay the operator
 * `sig` - Dictionary containing signature
   * `A` - Public point of signers key
   * `R` - Public point for EdDSA signature
   * `s` - Scalar for EdDSA signature (254bit in $\mathbb{F}_p$)



## The zkSNARK circuit
### Circuit Pseudocode
> [name=barryWhiteHat] Include fee logic, conditional transactions
```python
Account = namedtuple('Account', ('pubkey', 'token', 'balance', 'nonce'))

Signature = namedtuple('Signature', ('A', 'R', 's'))
Transaction = namedtuple('Transaction', ('from', 'to', 'amount', 'nonce'))
Record = namedtuple('Record', ('tx', 'sig', 'from_path', 'to_path'))

tree = list() # of Account type


NONCE_MAX_VALUE = ((1<<32) - 1)

def circuit(merkle_root, transactions):
	for record in transactions:
		# record is of 'Record type'
		sig = record.sig # sig of Signature type
		tx = record.tx   # tx of Transaction type

		# TODO: Verify account details provided match the merkle path provided
		assert(merkle_is_member(from_account, record.from_path, merkle_root))
		assert(merkle_is_member(to_account, record.from_path, merkle_root))
        
		# 7. Check the input leaf is a member of the merkle tree

		from_account = tree[tx.from] # of Account type
		to_account = tree[tx.to]     # of Account type

		# 1. check that `tx.from.pubkey == sig.pubkey`
		assert from_account.pubkey == sig.A

		# 2. check the `tx.from.nonce + 1 == sig.nonce`
		# Ensure Nonce doesn't overflow maxi
		assert from_account.nonce != NOCE_MAX_VALUE
		assert from_account.nonce == tx.nonce

		# 4. check the `tx.from.balance >= sig.amount`
		assert from_account.balnce >= tx.amount + tx.fee
		assert to_account.balance + tx.amount > to_account.balance

		# 5. validate the signature
		M = H(tx.from, tx.to, tx.amount, tx.nonce)
		assert eddsa_verify(M, A, R, s)

		assert from_account.token == to_account.token
        
            // checks if this tx depends upon the previous tx
            if (signature[i].dependent_payment[0] != 0) {
                require(signature[i].dependent_payment[0].to == signature[i-1].to);
                require(signature[i].dependent_payment[0].from == signature[i-1].from);
                require(signature[i].dependent_payment[0].amount == signature[i-1].amount);
    
            }
            // checks if this tx depends upon the next tx
            if (signature[i].dependent_payment[1] != 0) {
                require(signature  require(signature[i].dependent_payment[1].to == signature[1+1].to);
                require(signature[i].dependent_payment[1].from == signature[i+1].from);
                require(signature[i].dependent_payment[1].amount == signature[i+1].amount);s[i] == signature[i+1]);
            }

		new_from = Account(from_account.pubkey, from_account.token, from_account.balance - tx.amount - tx.fee, from_account.nonce + 1)
		new_to = Account(to_account.pubkey, to_account.token, to_account.balance + tx.amount, to_account.nonce)


		merkle_root = merkle_update(merkle_root, record.from_path, new_from)
		merkle_root = merkle_update(merkle_root, record.to_path, new_to)

```


# Operator selection mechanisim

Operators are staked. 
1. Their probability of being selected to produce a block is proportional to their stake.
2. We use the hash of the block hash as our randomness beacon. This can be biased but at some cost to the miners. Since we don't really need to worry about attacks because a malicious miner can process transactions and probably get much less reward than the block reward. 
3. As soon as this is commited, a new operator is selected who has 5 blocks to commit to a block. 
4. If they do not commit in this time a new opeartor is selected. This is repeated until a new block is commited to. 
5. We only ever have `proof_time/blocktime` blocks in progress.

If an operator fails to produce a block they have commited to in `proof_time` they are slashed, all future commitments are cancelled, and we begin again with a new operator. 

``` javascript
contract operator_orderer {
    uint epoch = 0;
    uint min_deposit = 64 ether;
    uint no_operators = 0;
    uint max_parallel_proofs = (proof_time/15) + (proof_time/15)*0.5;
    uint count_parallel_proofs = 0;

    function deposit() payable {
        require(msg.value >= min_deposit);
        operators.append(msg.sender);
    }

    function request_withdraw() {
        require(operators.indexOf(msg.sender) != -1);
        //move operator to end of list
        //reduce the number of operators by 1
        //set time limit for 1 day in the future
        //to make sure they are not about to get slashed
    }

    function confirm_withdraw() {
        operators.delete(msg.sender);
        // check they have waited 10 days 
        // since requesting withdraw
        msg.sender.send(min_deposit);
    }
    
    function commit_to_transactions(transactions, transaction_list) {
        require(msg.sender == operator_orderer);
        hash = "0x0"; 
        epoch += 1;
        for (transaction in transactions) {
            // we can pack here more efficiently
            hash = sha256(hash, transaction.to, transaction.from, transaction.amount);
            if (transaction.to == 0) { 
                withdraws[epoch].append((transaction.from, transaction.amount));
            }
        }
                
    }

    function commit_to_deposit() { 

    }
    
    
    function commit_to_block(transactions, transaction_list) {

    }

    function prove_block () { 
        //finalize withdraws()
        roll_up.prove_transtion(i, block);
        count_parallel_proofs--;
    }

    function revert_commit() {

    }

    //slash an operator for failing to create a proof
    function slash() {
        //if the operator has waiting too long
        //to make a proof slash them

    }
```


## Operator selection in parallel
[This spreadsheet](https://docs.google.com/spreadsheets/d/1bT3MSgZ2_rs-MRrrMrs5NhuXqG_jmr5Qrhzkde_Tb30/edit#gid=0) shows how blocks of transactions are aggregated and processed in parallel.

![Parallel proving ](https://i.imgur.com/F3frJ3b.png)

Stages:

 1. Collect Transactions
 2. Pick & Process a block of transactions
 3. Submit commitment to block of transactions to Ethereum
 4. Generate zkSNARK proof
 5. Submit proof to Ethereum

Once a block of transactions has been picked, and the commitment submitted to Ethereum, then the next 'Epoch' begins while the previous is being proven.

As soon as someone commits to a block we open a new auction. But we limit the number of open auctions/unproven commitments at `proving_time/blocktime` so that we can be making proofs to fill every block but not more than that. 

After the operator has commited they have `proving_time` to provide the proof. If they fail to provide the proof in this time they are slashed. 
We revert all commitments after this time and start the auction again. 

## Committing a block
```
event BlockCommitted(
    uint256 blockNumber
);

function commitBlock(
    bytes32 newBalancesRoot,
    bytes transactions
);
```

When an operator commits a block, it will provide a batch `transactions` along with `newBalancesRoot`. Based on the current on-chain balances root, all full clients and verify that the batch `transactions` are valid state transitions from the current balances root to `newBalancesRoot`. `H(transactions)` is stored in the contract so that the digest can be compared to the transactions included by the operator when proving the block later - the operator must use the same batch of transactions when committing and proving a given block. The operator will also provide a deposit.

## Proving a block

```
event BlockProved(
    uint256 blockNum
);

function proveBlock(
    uint256 blockNum,
    bytes proof,
    bytes transactions
);
```

When an operator proves a block, it will reference the previously committed block by number to first check that the digest produced by `H(transactions)` matches the digest stored for the commited block and will then retrieve the necessary on-chain data (i.e. accounts root, balances root) to be used for zkSNARK verification along with `proof` and the sequentially hashed output created for `transactions` (so that we can check that the transactions provided on-chain match the transactions used in the circuit).


# Appendix
## EdDSA parameters

See: [EdDSA for more curves](https://ed25519.cr.yp.to/eddsa-20150704.pdf)

* q = 21888242871839275222246405745257275088548364400416034343698204186575808495617

* b = 255
* Encoding GF\(p\): 254-bit little-endian encoding of {0..q-1} for Fq elements
* `H` : with 2b-bit output, can be implementation specific
* c = 3
* n = 254
* a = 168700
* d = 168696
* l = 21888242871839275222246405745257275088614511777268538073601725287587578984328
* B (base point)
  * x = 16540640123574156134436876038791482806971768689494387082833631921987005038935
  *  y = 20819045374670962167435360035096875258406992893633759881276124905556507972311
* Prehash function `H'` : *"ZCash Pedersen Hash"* scheme for `M = H(m)` and `H(R,A,M)`

The base point `B` is derived deterministically from the curve parameters using the following Sage math script: https://github.com/HarryR/ethsnarks/blob/master/.appendix/ejubjub.sage#L29

> [name=HaRold] XXX: this multiplies the base point by the cofactor, as per 'safe curves'? Which requires two points - base point and a generator.

## Pedersen commitment generator points

A reference implementation of the ZCash Pedersen hash scheme is implemented at:

 * [pedersen_hash_zcash_windows](https://github.com/HarryR/ethsnarks/blob/master/ethsnarks/pedersen.py#L103)
 * [pedersen_hash_basepoint](https://github.com/HarryR/ethsnarks/blob/master/ethsnarks/pedersen.py#L50)
 * [Point.from_hash](https://github.com/HarryR/ethsnarks/blob/master/ethsnarks/jubjub.py#L180)
 * [Point.from_y](https://github.com/HarryR/ethsnarks/blob/master/ethsnarks/jubjub.py#L143)

The `Point.from_y` method always returns the lexographically 'positive' point, meaning that if `x = x if -x < x else -x`. The `y` coordinate is incremented until a square `x` is recoverable, the resulting point is multiplied by the cofactor to ensure it is on the prime-ordered sub group (see `l` parameter above).

Base points are generated by hashing the 'personalisation string', which is the name in ASCII padded to 28 bytes, which prefixes the 16bit sequence number in upper-case hexadecimal.

```python
def pedersen_hash_basepoint(name, i):
    return Point.from_hash(b"%-28s%04X" % (name, i))
    
examples = [
    b'EdDSA_Verify.M              0001',
    b'EdDSA_Verify.RAM            35FE'
]
```

The string is then hashed using `SHA2-256`, and interpreted as a big-endian integer modulo `q` (see parameters above).

### EdDSA Verify `M = H(m)`

Personalisation string: `EdDSA_Verify.M`

```python
>>> from ethsnarks.pedersen import pedersen_hash_basepoint
>>> pedersen_hash_basepoint('EdDSA_Verify.M', 0)
Point(x=17808570483557114489501396356938072119849137096361887143136482272618515234401, y=17337153808050624319843135536866909465945363115819089726728943275668486202454)
>>> pedersen_hash_basepoint('EdDSA_Verify.M', 1)
Point(x=7661873644262973996516205872885137924192216722997724525912587418249205764216, y=521599936517143450773883437386797268960733771999550537025155877758843725572)
```

### EdDSA Verify `H(R,A,M)`

Personalisation string: `EdDSA_Verify.RAM`

```python
>>> from ethsnarks.pedersen import pedersen_hash_basepoint
>>> pedersen_hash_basepoint('EdDSA_Verify.RAM', 0)
Point(x=17434558536782967610340762605448133754549234172198748128207635616973179917758, y=13809929214859773185494095338070573446620668786591540427529120055108311408601)
>>> pedersen_hash_basepoint('EdDSA_Verify.RAM', 1)
Point(x=20881191793028387546033104172192345421491262837680372142491907592652070161952, y=5075784556128217284685225562241792312450302661801014564715596050958001884858)
>>> pedersen_hash_basepoint('EdDSA_Verify.RAM', 2)
Point(x=8520090440088786753637148399502745058630978778520003292078671435389456269403, y=19065955179398565181112355398967936758982488978618882004783674372269664446856)
>>> pedersen_hash_basepoint('EdDSA_Verify.RAM', 3)
Point(x=8252178246422932554470545827089444002049004598962888144864423033128179910983, y=15651909989309155104946748757069215505870124528799433233405947236802744549198)
```

## Test Vectors

### Pedersen Hash

```python
pedersen_hash_zcash_bytes(b'test', b"abc")
Point(
    x=9869277320722751484529016080276887338184240285836102740267608137843906399765, 
    y=19790690237145851554496394080496962351633528315779989340140084430077208474328)
```

```python
pedersen_hash_zcash_bytes(b'test', b"abcdefghijklmnopqrstuvwx")
Point(
    x=3966548799068703226441887746390766667253943354008248106643296790753369303077,
    y=12849086395963202120677663823933219043387904870880733726805962981354278512988)
```

```python
pedersen_hash_zcash_bits('EdDSA_Verify.RAM', '101100110011111001100100101100010100011010100100001011101001000100100000001111101101111001001010111011101101011010010101101101101000000010000000101010110100011110101110111100111100011110110011100101011000000000110101111001110000101011011110100100011110010000110111010011000001000100101100101111001100100010110101100010001000000101111011011010010011110001110111101011110001111111100010010000110101000001010111000111011110111010010010000101110000011001111000101010001101100000110111111110011001110101011000110010111111000101001100010001011011101010101011101010110000111100101000000110011000011001101000001010110110010000110101011111100010111011100110111101110111011001001110100100110010100111001000001010101010010100010100101101000010100010000111110101111000101110')

Point(
    x=16391910732431349989910402670442677728780476741314399751389577385062806845560,
    y=9557600014660247419117975756584483223203707451467643504980876223495155042156)
```

### EdDSA Verify

```python
B = Point(
    x=21609035313031231356478892405209584931807557563713540183143349090940105307553, 
    y=845281570263603011277359323511710394920357596931617398831207691379369851278)
    
A = Point(
    x=5616630816018221659484394091994939318481030030481519242876140465113436048304,
    y=8476221375891900895034976644661703008703725320613595264559419965669922411183)
    
R = Point(
    x=17883110238616315155327756854433987355427639458557188556819876765548551765197,
    y=11833558192785987866925773659755699683735551950878443451361314529874236222818)

s = 9920504625278683304895036460477595239370241328717115039061027107077120437288

m = b'abc'

M = eddsa_hash_message(m)

assert M == Point(
    x=13171389818020282873381565105042152142789296552115650373722989062014195935485,
    y=21138773071827505936030575211328278572604363646033964129713244144182196908321)
```# roll_up token: Snark based multi-ERC20 side chain
A merkle tree is used to track accounts and balances. Multiple tokens are supported but each token requires a seperate account. The owner of a balance can sign a transaction to transfer part or all of the balance to another account, these transactions are batched via snark to prove that the state transition was correct. 

We maintain data availability by making sure that each zkSNARK proof must reveal a list of leaves that were changed and the amount that was transferred inside the EVM. We rely on Ethereum for data availability guarantees. 

The merkle tree is depth 24, which supports 2^24 accounts. Each account can only hold a single token. The system supports multiple tokens.

## Glossary of terms/variables:

 * roll up: a method of aggragateing multiple signatures and/or merkle tree updates inside a snark. 
 * Operator: The party aggragets many signatures into a single snark transaction. 
 * Circuit: The code that defines what the snark allows.
 * Block: ethereum block
 * Epoch: roll_up block which is a single snark proof of a state transition which containts many transactions.
 * account tree this is the merkle tree that stores a mapping between accounts and balances
 * account_tree_depth (24) this is the number of layers in the account merkle tree

### Tree leaf format

Each account is represented by a single leaf in the balance tree. It is calculated by hashing the following components in the following order;
```python
leaf = H(pubkey_x, pubkey_y, balance, nonce, token)
```

#### Inputs
 * public key X (254 bits)
 * public key Y (254 bits) 
 * token (16 bits)
 * nonce (32 bits)
 * balance (128 bits) 

### New token addition
Each token needs to be added before it can be transfered. The EVM maintains a list of 2^16 to tokens. The deposits, transfers, and withdraws reference a token index in this list. Anyone can add a new token by calling the `add_token` function on the smart contract. 

To prevent squating attacks, users need to burn 1 ether in order to add a new token.

#### Sudo code

##### Smart contract

```javascript
    // Add a new token
    function add_token() {
    
    }
```

### Deposits
Deposits and account creation use the same mechanism. Deposits create a new account with an initial balance, and account creation without a deposit leaves the balance at zero. These deposits get added to deposit lists that are ordered by fee.

Deposits are made directly to the smart contract, they are queued up in a 'deposit block'. They are aggregated into a sha256 merkle tree. The operator then makes a snark that translates this merkle tree into a pedersen commitment merkle tree. Which is then appended to the account merkle tree. 

It is also possible for zero value deposits to avoid the fee queue for deposit. Which allows operators to add users who don't have gas to pay for fees. 

1. User deposits `amount` of`token` to the smart contract
2. Smart contract verifies that the tokens have been transferred. 
3. Smart contract saves this in the same format as the transfer data to, from, amount which is saved in a list by fee per token executed in the same way operators order transfers.
4. deposit_list[fee_eth].append(deposit)
5. Once the block is full a depositor can add it to the tree.

Alternatively, depositors can specify multiple zero balance leaves and bypass the token transfer check and fee payment. After enough transactions have been batched, the operator can execute them together exactly the same as the fee queue.

#### Sudo code

##### Smart contract

```javascript
    // deposit with fee
    function deposit_fee(owner, token, amount, fee) {
        require(token.transfer(amount + fee, this));
        deposit_block_fee[fee].append(merkle_tree_append_sha256(owner.pubkey_x, owner.pubkey_y, balance, 0, token_addr));
    }

    // deposit with no fee
    function deposit_no_fee(owner, token) {
        deposit_block_no_fee[msg.sender].append(merkle_tree_append_sha256(owner.pubkey_x, owner.pubkey_y, 0, 0, token));
    }

    function deposit_fee(proof, fee) {
        require(deposit_block_fee[fee].full == true);
        validate_proof(proof, block[fee].root, account_offset);
        token.send(msg.sender, fee*blocksize);
        account_offset += tree_size;
    }
    
    function deposit_no_fee(proof) {
        require(deposit_block_no_fee[msg.sender].full == true);
        validate_proof(proof, deposit_block_no_fee[msg.sender].root, account_offset);
        account_offset += tree_size;
    }         
        
    function validate_snark(proof, address) {
        require(deposit_block[msg.sender].full == true);
        validate_proof(proof, block[msg.sender].root, account_offset);
        token.send(msg.sender, fee*blocksize);
        account_offset += tree_size;
    }
```

##### Snark 
```javascript
    // append account to existing account merkle tree.
    function add_accounts(deposit_tree_sha256, account_tree, account_offset ) {
    
        to_pedersen(deposit_tree_sha256)
        * account offset is the first leaf in the merke tree that is zero
        * At this leaf make a merkle proof of the for the zero element
        * Take N steps up the tree from this leaf
        * Where n is the depth of hte deposit_tree
        * Insert the deposit_tree_pedersen here.
        * return this merkle root
        
    }
```

### Withdraw mechanism
Leaves can be withdrawn as follows. 

The transaction format is 10 bytes:
 
   * 3 bytes `from`
   * 3 bytes `to`
   * 2 bytes `amount`
   * 2 bytes `token`

The `to` address of `0` is a special address, it is the 'Withdraw' address. Any balance you send to leaf index `0` has a special meaning. The public key for leaf zero does not exit.

When the zkSNARK proof is submitted by the operator, if the destination is `0` the on-chain 'withdrawable balance' for the `from` leaf index is incremented by the amount, the amount needs converting from floating point to Wei unsigned integer.

The `from` address must have added a `withdraw_address` anyone can then send a transaction that sends the funds to this address.

The `withdraw_address` can be set by creating a snark that validates a signature and merkle tree proof for any previous state of the snark where the signatures nominates a `withdraw_address` which is permenently saved in the smart contract.

Transfers to the zero address should avoid the token type check.


#### Sudo Code
##### Smart contract 
```javascript
    function withdraw(uint epoch, uint i) {
        // make sure you cannot withdraw until proof has been provided
        require(blocks[epoch].finalized == true);
        transcation = withdraw[epoch][i];
        address = withdraw_address[transaction.from];
        token withdraw_token[withdraw_address[transaction.from]];
        address.send(token, to_256_bit_number(transaction.amount));
    }
    
    function nominate_withdraw_address(proof_of_membership, leaf_address, nominate_withdraw_address) {
        snark_verify(proof_of_membership);
        // don't let us update this
        require(withdraw_address[leaf_address] == 0);
        withdraw_address[leaf_address] = nominate_withdraw_address;    
    }
```

##### snark
``` javascript
    proof_of_membership()
        public address
        public nominated_withdraw_addrss
        public merkle_root
        leaf = leaves[address]
        merkle_proof(leaf, merkle_tree, address)
        signatures_validate(sig, nominated_withdraw_addrss)
```

### Data availablity

This approach is based [upon](https://ethresear.ch/t/on-chain-scaling-to-potentially-500-tx-sec-through-mass-tx-validation/3477)

Each transaction record is 10 bytes, and consists of:

1. `from` leaf (3 bytes)
2. `to` leaf   (3 bytes)
3. `amount`    (2 bytes) 
4. `token`     (2 bytes)

For each batch, the records are concatenated together and then hashed to produce a single digest. This digest is passed as a public input to the zkSNARK circuit to ensure that the on-chain and in-circuit data match.

The `from` and `to` offsets specify the leaves within the tree, the size required for the offset depends on the depth of the tree. $TreeCapacity = 2^{tree\_depth}$, offset size in bits is $log_2(tree\_depth)$.


### Dependent Payments

We want to allow for dependent payments. This allows us to do atomic swaps at almost no cost in terms of constraints.

The user can signal that their transaction is dependent upon a previous one 
by signaling via signature. These fields in the signature format are 
`"dependent_payments": [[to,from,amount], [to,from,amount]]`. Where `to`, `from`, `amount` define the transaction that this one depends upon. 

Then the snark confirms that each transaction has its dependecies included. 

#### Snark sudo-code
```javascript
// checks if this tx depends upon the previous tx
if (signature[i].dependent_payment[0] != 0) {
    require(signature[i].dependent_payment[0].to == signature[i-1].to);
    require(signature[i].dependent_payment[0].from == signature[i-1].from);
    require(signature[i].dependent_payment[0].amount == signature[i-1].amount);
    
}
// checks if this tx depends upon the next tx
if (signature[i].dependent_payment[1] != 0) {
    require(signature  require(signature[i].dependent_payment[1].to == signature[1+1].to);
    require(signature[i].dependent_payment[1].from == signature[i+1].from);
    require(signature[i].dependent_payment[1].amount == signature[i+1].amount);s[i] == signature[i+1]);
}
```
### Atomic Swaps
We can use this to do atomic swaps where
Alice has 10 tokens A 
Bob has 1 token B 
They can trade trustlessly by creating dependent transactions by doing the following 
1. Bob and Alice agree to trade 1 token B for 10 token A. 
2. Bob creates a transaction that sends 1 token B to Alice. That is dependent upon Alice sending 10 token A to bob. 
3. Alice creates a transction that sends 10 token A to bob that is dependent upon a transfer to 1 token B to alice. 
4. They share their transactions with each other and broadcast them to the operator.

We can only do pairwise dependent transactions here.

## Transaction Fees

We need to pay fees so the operator is incentivized to create blocks and process transactions. We could use the naive approach and allow the operator to use conditional payments to get their transactions included in a block. However this is expensive and halves the throughput of our system. 

Its also important that users can pay for fees in different tokens. This allows us to batch together more transactions in each block. As we have a larger pool we can include we can make blocks faster.

So we force the operator to commit to the fees in the EVM and then validate this is correct in the snark.


### Fee calcultaion
At commitment time the EVM can calculate how much fees are owed to the operator by taking the number of tokens of each token type and multiplying this by that tokens fee type. 

If the operator did not include that token in their fee commitment they recive a fee of zero. 

## Transaction Format


### Snark Transactions

EdDSA signatures are used by users to send transactions. The operator uses these transactions to make a snark proof.

These are provided to the operator in the off-chain transaction. The transaction is represented as a JSON document:

```json
{
   "tx": {
      "from": nnn,
      "nonce": nnn,
      "to": nnn,
      "amount": nnn,
      "fee": nnn, 
      "dependent_payments": [[to, from, amount], [to, from, amount]]
      "hash_to_from_amount": nnn
   }
   "sig": {
       "A": [pubkey.x, pubkey.y],
       "R": [R.x, R.y],
       "s": nnn
   }
}
```

To verify the transaction:

```python
m = H(tx.from, tx.to, tx.amount, tx.fee)

assert True == eddsa_verify(m, sig.A, sig.R, sig.s)
```

Fields:

 * `tx` - Dictionary with transaction details
   * `from` - Leaf index (account_tree_depth bit unsigned) of sending account
   * `nonce` - account_tree_depth bit Nonce, to prevent transaction replays
   * `to` - Leaf index (24 bit unsigned) of receiving account
   * `amount` - Balance to transfer (16 bit unsigned)
   * `fee` - The fee to pay the operator
 * `sig` - Dictionary containing signature
   * `A` - Public point of signers key
   * `R` - Public point for EdDSA signature
   * `s` - Scalar for EdDSA signature (254bit in $\mathbb{F}_p$)



## The zkSNARK circuit
### Circuit Pseudocode
> [name=barryWhiteHat] Include fee logic, conditional transactions
```python
Account = namedtuple('Account', ('pubkey', 'token', 'balance', 'nonce'))

Signature = namedtuple('Signature', ('A', 'R', 's'))
Transaction = namedtuple('Transaction', ('from', 'to', 'amount', 'nonce'))
Record = namedtuple('Record', ('tx', 'sig', 'from_path', 'to_path'))

tree = list() # of Account type


NONCE_MAX_VALUE = ((1<<32) - 1)

def circuit(merkle_root, transactions):
	for record in transactions:
		# record is of 'Record type'
		sig = record.sig # sig of Signature type
		tx = record.tx   # tx of Transaction type

		# TODO: Verify account details provided match the merkle path provided
		assert(merkle_is_member(from_account, record.from_path, merkle_root))
		assert(merkle_is_member(to_account, record.from_path, merkle_root))
        
		# 7. Check the input leaf is a member of the merkle tree

		from_account = tree[tx.from] # of Account type
		to_account = tree[tx.to]     # of Account type

		# 1. check that `tx.from.pubkey == sig.pubkey`
		assert from_account.pubkey == sig.A

		# 2. check the `tx.from.nonce + 1 == sig.nonce`
		# Ensure Nonce doesn't overflow maxi
		assert from_account.nonce != NOCE_MAX_VALUE
		assert from_account.nonce == tx.nonce

		# 4. check the `tx.from.balance >= sig.amount`
		assert from_account.balnce >= tx.amount + tx.fee
		assert to_account.balance + tx.amount > to_account.balance

		# 5. validate the signature
		M = H(tx.from, tx.to, tx.amount, tx.nonce)
		assert eddsa_verify(M, A, R, s)

		assert from_account.token == to_account.token
        
            // checks if this tx depends upon the previous tx
            if (signature[i].dependent_payment[0] != 0) {
                require(signature[i].dependent_payment[0].to == signature[i-1].to);
                require(signature[i].dependent_payment[0].from == signature[i-1].from);
                require(signature[i].dependent_payment[0].amount == signature[i-1].amount);
    
            }
            // checks if this tx depends upon the next tx
            if (signature[i].dependent_payment[1] != 0) {
                require(signature  require(signature[i].dependent_payment[1].to == signature[1+1].to);
                require(signature[i].dependent_payment[1].from == signature[i+1].from);
                require(signature[i].dependent_payment[1].amount == signature[i+1].amount);s[i] == signature[i+1]);
            }

		new_from = Account(from_account.pubkey, from_account.token, from_account.balance - tx.amount - tx.fee, from_account.nonce + 1)
		new_to = Account(to_account.pubkey, to_account.token, to_account.balance + tx.amount, to_account.nonce)


		merkle_root = merkle_update(merkle_root, record.from_path, new_from)
		merkle_root = merkle_update(merkle_root, record.to_path, new_to)

```


# Operator selection mechanisim

Operators are staked. 
1. Their probability of being selected to produce a block is proportional to their stake.
2. We use the hash of the block hash as our randomness beacon. This can be biased but at some cost to the miners. Since we don't really need to worry about attacks because a malicious miner can process transactions and probably get much less reward than the block reward. 
3. As soon as this is commited, a new operator is selected who has 5 blocks to commit to a block. 
4. If they do not commit in this time a new opeartor is selected. This is repeated until a new block is commited to. 
5. We only ever have `proof_time/blocktime` blocks in progress.

If an operator fails to produce a block they have commited to in `proof_time` they are slashed, all future commitments are cancelled, and we begin again with a new operator. 

``` javascript
contract operator_orderer {
    uint epoch = 0;
    uint min_deposit = 64 ether;
    uint no_operators = 0;
    uint max_parallel_proofs = (proof_time/15) + (proof_time/15)*0.5;
    uint count_parallel_proofs = 0;

    function deposit() payable {
        require(msg.value >= min_deposit);
        operators.append(msg.sender);
    }

    function request_withdraw() {
        require(operators.indexOf(msg.sender) != -1);
        //move operator to end of list
        //reduce the number of operators by 1
        //set time limit for 1 day in the future
        //to make sure they are not about to get slashed
    }

    function confirm_withdraw() {
        operators.delete(msg.sender);
        // check they have waited 10 days 
        // since requesting withdraw
        msg.sender.send(min_deposit);
    }
    
    function commit_to_transactions(transactions, transaction_list) {
        require(msg.sender == operator_orderer);
        hash = "0x0"; 
        epoch += 1;
        for (transaction in transactions) {
            // we can pack here more efficiently
            hash = sha256(hash, transaction.to, transaction.from, transaction.amount);
            if (transaction.to == 0) { 
                withdraws[epoch].append((transaction.from, transaction.amount));
            }
        }
                
    }

    function commit_to_deposit() { 

    }
    
    
    function commit_to_block(transactions, transaction_list) {

    }

    function prove_block () { 
        //finalize withdraws()
        roll_up.prove_transtion(i, block);
        count_parallel_proofs--;
    }

    function revert_commit() {

    }

    //slash an operator for failing to create a proof
    function slash() {
        //if the operator has waiting too long
        //to make a proof slash them

    }
```


## Operator selection in parallel
[This spreadsheet](https://docs.google.com/spreadsheets/d/1bT3MSgZ2_rs-MRrrMrs5NhuXqG_jmr5Qrhzkde_Tb30/edit#gid=0) shows how blocks of transactions are aggregated and processed in parallel.

![Parallel proving ](https://i.imgur.com/F3frJ3b.png)

Stages:

 1. Collect Transactions
 2. Pick & Process a block of transactions
 3. Submit commitment to block of transactions to Ethereum
 4. Generate zkSNARK proof
 5. Submit proof to Ethereum

Once a block of transactions has been picked, and the commitment submitted to Ethereum, then the next 'Epoch' begins while the previous is being proven.

As soon as someone commits to a block we open a new auction. But we limit the number of open auctions/unproven commitments at `proving_time/blocktime` so that we can be making proofs to fill every block but not more than that. 

After the operator has commited they have `proving_time` to provide the proof. If they fail to provide the proof in this time they are slashed. 
We revert all commitments after this time and start the auction again. 

## Committing a block
```
event BlockCommitted(
    uint256 blockNumber
);

function commitBlock(
    bytes32 newBalancesRoot,
    bytes transactions
);
```

When an operator commits a block, it will provide a batch `transactions` along with `newBalancesRoot`. Based on the current on-chain balances root, all full clients and verify that the batch `transactions` are valid state transitions from the current balances root to `newBalancesRoot`. `H(transactions)` is stored in the contract so that the digest can be compared to the transactions included by the operator when proving the block later - the operator must use the same batch of transactions when committing and proving a given block. The operator will also provide a deposit.

## Proving a block

```
event BlockProved(
    uint256 blockNum
);

function proveBlock(
    uint256 blockNum,
    bytes proof,
    bytes transactions
);
```

When an operator proves a block, it will reference the previously committed block by number to first check that the digest produced by `H(transactions)` matches the digest stored for the commited block and will then retrieve the necessary on-chain data (i.e. accounts root, balances root) to be used for zkSNARK verification along with `proof` and the sequentially hashed output created for `transactions` (so that we can check that the transactions provided on-chain match the transactions used in the circuit).


# Appendix
## EdDSA parameters

See: [EdDSA for more curves](https://ed25519.cr.yp.to/eddsa-20150704.pdf)

* q = 21888242871839275222246405745257275088548364400416034343698204186575808495617

* b = 255
* Encoding GF\(p\): 254-bit little-endian encoding of {0..q-1} for Fq elements
* `H` : with 2b-bit output, can be implementation specific
* c = 3
* n = 254
* a = 168700
* d = 168696
* l = 21888242871839275222246405745257275088614511777268538073601725287587578984328
* B (base point)
  * x = 16540640123574156134436876038791482806971768689494387082833631921987005038935
  *  y = 20819045374670962167435360035096875258406992893633759881276124905556507972311
* Prehash function `H'` : *"ZCash Pedersen Hash"* scheme for `M = H(m)` and `H(R,A,M)`

The base point `B` is derived deterministically from the curve parameters using the following Sage math script: https://github.com/HarryR/ethsnarks/blob/master/.appendix/ejubjub.sage#L29

> [name=HaRold] XXX: this multiplies the base point by the cofactor, as per 'safe curves'? Which requires two points - base point and a generator.

## Pedersen commitment generator points

A reference implementation of the ZCash Pedersen hash scheme is implemented at:

 * [pedersen_hash_zcash_windows](https://github.com/HarryR/ethsnarks/blob/master/ethsnarks/pedersen.py#L103)
 * [pedersen_hash_basepoint](https://github.com/HarryR/ethsnarks/blob/master/ethsnarks/pedersen.py#L50)
 * [Point.from_hash](https://github.com/HarryR/ethsnarks/blob/master/ethsnarks/jubjub.py#L180)
 * [Point.from_y](https://github.com/HarryR/ethsnarks/blob/master/ethsnarks/jubjub.py#L143)

The `Point.from_y` method always returns the lexographically 'positive' point, meaning that if `x = x if -x < x else -x`. The `y` coordinate is incremented until a square `x` is recoverable, the resulting point is multiplied by the cofactor to ensure it is on the prime-ordered sub group (see `l` parameter above).

Base points are generated by hashing the 'personalisation string', which is the name in ASCII padded to 28 bytes, which prefixes the 16bit sequence number in upper-case hexadecimal.

```python
def pedersen_hash_basepoint(name, i):
    return Point.from_hash(b"%-28s%04X" % (name, i))
    
examples = [
    b'EdDSA_Verify.M              0001',
    b'EdDSA_Verify.RAM            35FE'
]
```

The string is then hashed using `SHA2-256`, and interpreted as a big-endian integer modulo `q` (see parameters above).

### EdDSA Verify `M = H(m)`

Personalisation string: `EdDSA_Verify.M`

```python
>>> from ethsnarks.pedersen import pedersen_hash_basepoint
>>> pedersen_hash_basepoint('EdDSA_Verify.M', 0)
Point(x=17808570483557114489501396356938072119849137096361887143136482272618515234401, y=17337153808050624319843135536866909465945363115819089726728943275668486202454)
>>> pedersen_hash_basepoint('EdDSA_Verify.M', 1)
Point(x=7661873644262973996516205872885137924192216722997724525912587418249205764216, y=521599936517143450773883437386797268960733771999550537025155877758843725572)
```

### EdDSA Verify `H(R,A,M)`

Personalisation string: `EdDSA_Verify.RAM`

```python
>>> from ethsnarks.pedersen import pedersen_hash_basepoint
>>> pedersen_hash_basepoint('EdDSA_Verify.RAM', 0)
Point(x=17434558536782967610340762605448133754549234172198748128207635616973179917758, y=13809929214859773185494095338070573446620668786591540427529120055108311408601)
>>> pedersen_hash_basepoint('EdDSA_Verify.RAM', 1)
Point(x=20881191793028387546033104172192345421491262837680372142491907592652070161952, y=5075784556128217284685225562241792312450302661801014564715596050958001884858)
>>> pedersen_hash_basepoint('EdDSA_Verify.RAM', 2)
Point(x=8520090440088786753637148399502745058630978778520003292078671435389456269403, y=19065955179398565181112355398967936758982488978618882004783674372269664446856)
>>> pedersen_hash_basepoint('EdDSA_Verify.RAM', 3)
Point(x=8252178246422932554470545827089444002049004598962888144864423033128179910983, y=15651909989309155104946748757069215505870124528799433233405947236802744549198)
```

## Test Vectors

### Pedersen Hash

```python
pedersen_hash_zcash_bytes(b'test', b"abc")
Point(
    x=9869277320722751484529016080276887338184240285836102740267608137843906399765, 
    y=19790690237145851554496394080496962351633528315779989340140084430077208474328)
```

```python
pedersen_hash_zcash_bytes(b'test', b"abcdefghijklmnopqrstuvwx")
Point(
    x=3966548799068703226441887746390766667253943354008248106643296790753369303077,
    y=12849086395963202120677663823933219043387904870880733726805962981354278512988)
```

```python
pedersen_hash_zcash_bits('EdDSA_Verify.RAM', '101100110011111001100100101100010100011010100100001011101001000100100000001111101101111001001010111011101101011010010101101101101000000010000000101010110100011110101110111100111100011110110011100101011000000000110101111001110000101011011110100100011110010000110111010011000001000100101100101111001100100010110101100010001000000101111011011010010011110001110111101011110001111111100010010000110101000001010111000111011110111010010010000101110000011001111000101010001101100000110111111110011001110101011000110010111111000101001100010001011011101010101011101010110000111100101000000110011000011001101000001010110110010000110101011111100010111011100110111101110111011001001110100100110010100111001000001010101010010100010100101101000010100010000111110101111000101110')

Point(
    x=16391910732431349989910402670442677728780476741314399751389577385062806845560,
    y=9557600014660247419117975756584483223203707451467643504980876223495155042156)
```

### EdDSA Verify

```python
B = Point(
    x=21609035313031231356478892405209584931807557563713540183143349090940105307553, 
    y=845281570263603011277359323511710394920357596931617398831207691379369851278)
    
A = Point(
    x=5616630816018221659484394091994939318481030030481519242876140465113436048304,
    y=8476221375891900895034976644661703008703725320613595264559419965669922411183)
    
R = Point(
    x=17883110238616315155327756854433987355427639458557188556819876765548551765197,
    y=11833558192785987866925773659755699683735551950878443451361314529874236222818)

s = 9920504625278683304895036460477595239370241328717115039061027107077120437288

m = b'abc'

M = eddsa_hash_message(m)

assert M == Point(
    x=13171389818020282873381565105042152142789296552115650373722989062014195935485,
    y=21138773071827505936030575211328278572604363646033964129713244144182196908321)
```

### Floating point format

Theis is the way it's encoded a 3 and a half decimal digits in a 16 bits floating point. Lets name those bits from MSB to LSB

e4 e3 e2 e1 e0 m9 m8 m7 m6 m5 m4 m3 m2 m1 m0 d 

exp := e0 + e1*2 + e2*2^2 + e3*2^3 + e4*2^4

m := m0 + m1*2 + m2*2^2 + m3*2^3 + m4*2^4 + m5*2^5 + m6*2^6 + m7*2^7 + m8*2^8 + m9*2^9

V := m*10^exp + d* ( (10^exp) >> 1 )

This format allows to use decimal numbers where the 3  most signigicant digits can be any digit [0..9] The forth can be 0 or 5 and an exponent from 1 to 10^31

Example 1: 123000000   
m = 123 => 0x7b => 0b00 0111 1011
d = 0 (The forth digit is a 0)
exp = 6 => 0b00110
So the Floating point format would be 0b0011000011110110  = 0x30F6

Example 2:  454500
m = 454 => 0x1c6 => 0b0111000110
d =1 (The forth digit is a 5)
exp = 3 => 0x3 => 0b00011
So the Floating point format is 0b0001101110001101 =   0x1B8D


