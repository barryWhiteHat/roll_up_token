# `roll_up` token: SNARK-based multi-ERC20 side chain
A Merkle tree is used to track accounts and balances. Multiple tokens are supported but each token requires a separate account. The owner of a balance can sign a transaction to transfer part or all of the balance to another account, these transactions are batched via SNARK to prove that the state transition was correct. 

We maintain data availability by making sure that each zkSNARK proof must reveal a list of leaves that were changed and the amount that was transferred inside the EVM. We rely on Ethereum for data availability guarantees. 

The Merkle tree is depth 24, which supports 2^24 accounts. Each account can only hold a single token. Multiple tokens can be transferred and traded inside a single block.

## Glossary of terms/variables:

 * `roll_up`: a method of aggregating multiple signatures and/or Merkle tree updates inside a snark. 
 * Operator: the party aggregates many signatures into a single snark transaction. 
 * Circuit: the code that defines what the SNARK allows.
 * Block: Ethereum block
 * Epoch: `roll_up` block which is a single SNARK proof of a state transition which contains many transactions.
 * `account_tree`: the Merkle tree that stores a mapping between accounts and balances
 * `account_tree_depth` (24): the number of layers in the `account_tree`

### Tree leaf format

Each account is represented by a single leaf in the balance tree. It is calculated by hashing the following components in the following order;
```python
leaf = H(pubkey_x, pubkey_y, balance, nonce, token)
```

#### Inputs
 * public key X (253 bits)
 * public key Y (253 bits) 
 * token (32 bits)
 * nonce (32 bits)
 * balance (128 bits) 
 
<img src="https://raw.githubusercontent.com/barryWhiteHat/roll_up_token/master/images/database.png" width=75%>

### Deposits
Each deposit creates a leaf in the smart contract. The smart contract checks that the token type and balance are correct. 
Anyone can aggregate these deposits into a deposit tree. 

The operator can add these to the current balance tree by 

1. Proving that a leaf at the same depth as the deposit tree is zero
2. Replacing this leaf with the deposit tree 
3. Using the same merkle proof as the deposit tree to calculate the new root of the balance tree. 
![](https://raw.githubusercontent.com/barryWhiteHat/roll_up_token/master/images/deposit.pnghttps://raw.githubusercontent.com/barryWhiteHat/roll_up_token/master/images/deposit.png)

### Withdraw mechanism
Leaves can be withdrawn as follows. 

The transaction format is 8 bytes:
 
   * 3 bytes `from`
   * 3 bytes `to`
   * 2 bytes `nonce`
   * 2 bytes `amount`

The `to` address of `0` is a special address, it is the 'Withdraw' address. Any balance you send to leaf index `0` has a special meaning. The public key for leaf zero does not exist.

When the SNARK proof is submitted by the operator, if the destination is `0` the on-chain 'withdrawable balance' for the `from` leaf index is incremented by the amount, the amount needs converting from floating point to Wei unsigned integer.

The `from` address must have added a `withdraw_address` anyone can then send a transaction that sends the funds to this address.

Because any token type can be sent to the zero address. Transfers to the zero address should avoid the token type check.

Its important that no transfers are able to leave the zero address. 
1. The public key of the `0` leaf should be generated in such a way that no private key exists. 
2. The circuit logic should not allow leaf `0` to be the from address

#### Pseudocode
##### Smart contract 
```javascript
    function withdraw(uint epoch, uint i) {
        // make sure you cannot withdraw until proof has been provided
        require(blocks[epoch].finalized == true);
        transaction = withdraw[epoch][i];
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

##### SNARK
``` javascript
    proof_of_membership()
        public address
        public nominated_withdraw_address
        public merkle_root
        leaf = leaves[address]
        merkle_proof(leaf, merkle_tree, address)
        signatures_validate(sig, nominated_withdraw_address)
```

## Transfer mechanism
We have an `account_tree` with mapping of public key to nonce and balance of various tokens. We want to be able to transfer these tokens. The owner of a token creates a signature that signals their consent to update their balance. This signature contains the following fields:

* `from` - Leaf index (account_tree_depth bit unsigned) of sending account
   * `nonce` - `account_tree_depth` bit Nonce, to prevent transaction replays
   * `to` - Leaf index (24 bit unsigned) of receiving account
   * `amount` - Balance to transfer (16 bit unsigned)
   * `fee` - The fee to pay the operator
 * `sig` - Dictionary containing signature
   * `A` - Public point of signers key
   * `R` - Public point for EdDSA signature
   * `s` - Scalar for EdDSA signature (254bit in $\mathbb{F}_p$)

The SNARK then constrains the operator to processing these transactions in the following way:

1. Prove that `from` index has a certain public key with a Merkle proof
2. Prove that that public key matches the signature of the transaction
3. Reduce the balance of that leaf
4. Increment the nonce of that leaf
5. Replace the original leaf with this updated leaf, using the same Merkle proof to insert it into the old tree while keeping every other leaf constant. This Merkle root is called the `intermediate_merkle_root`
6. Using this `intermediate_merkle_root` prove that the the leaf `to` index is in the merkle tree. 
7. Check that `to.token_type == from.token_type`
8. Update the balance of the `to` leaf. 
9. Using the same merkle proof as the original proof of membership insert the new leaf into the tree calculating the new merkle root. 

If any of these steps fail the whole proof fails. 

This proof for a single transaction can be generalised to many transactions, as long as the appropriate `intermediate_merkle_roots` are pre-computed and provided as input to the circuit. 


## Transaction Fees

We need to pay fees so the operator is incentivized to create blocks and process transactions. Its important that users can pay for fees in different tokens. This allows us to batch together more transactions in each block. As we have a larger pool we can include we can make blocks faster.

So we force the operator to commit to the fees in the EVM and then validate this is correct in the SNARK. We use an all pay fee model where the operator commits to a fee and any fee transaction that specifies a fee more than or equal to this amount can be included and pays the fee that the operator commited to.

### Data availablity

#### Transactions
This approach is based [upon](https://ethresear.ch/t/on-chain-scaling-to-potentially-500-tx-sec-through-mass-tx-validation/3477)

Each transaction record is 8 bytes, and consists of:

1. `from` index (3 bytes)
2. `to` index   (3 bytes)
3. `amount`    (2 bytes) 


The `from` and `to` offsets specify the leaves within the tree, the size required for the offset depends on the depth of the tree. `TreeCapacity` $= 2^\texttt{tree\_depth}$, offset size in bits is $log_2(\texttt{tree\_depth})$.

#### Fees

The data provided above is not enough to ensure that all data is available. As the amount recived at the `to` leaf is actually `amount - fee[token]`. Therefore we also need the operator to commit on-chain to fees for 16 different token types. 

1. `token_type` 32 bits 
2. `fee` 2 bytes
3. `number_transaction_of_this_type` 12 bits

For each batch, the records are concatenated together and then hashed to produce a single digest. This digest is passed as a public input to the SNARK circuit to ensure that the on-chain and in-circuit data match.

Then the circuit processes these transactions and ensures that 

1. Each token type is in the token schedule or has zero fee. 
2. The `no_tx_of_this_type == no_tx_processed`

After a proof has been finalized the operator can include withdraw `fee * number_transaction_of_this_type` of each token type they have included. 

### Dependent Payments

We want to allow for dependent payments. This allows us to do atomic swaps at almost no cost in terms of constraints.

The user can signal that their transaction is dependent upon a previous one by signaling via signature. These fields in the signature format are `"dependent_payments": [[to,from,amount], [to,from,amount]]`, where `to`, `from`, `amount` define the transaction that this one depends upon. 

Then the SNARK confirms that each transaction has its dependencies included. 

#### SNARK pseudocode
```javascript
// look back , checks if this tx depends upon the previous tx
if (signature[i].dependent_payment[0] != 0) {
    require(signature[i].dependent_payment[0].to == signature[i-1].to);
    require(signature[i].dependent_payment[0].from == signature[i-1].from);
    require(signature[i].dependent_payment[0].amount == signature[i-1].amount);
    
}
// look forward, checks if this tx depends upon the next tx
if (signature[i].dependent_payment[1] != 0) {
    require(signature  require(signature[i].dependent_payment[1].to == signature[1+1].to);
    require(signature[i].dependent_payment[1].from == signature[i+1].from);
    require(signature[i].dependent_payment[1].amount == signature[i+1].amount);s[i] == signature[i+1]);
}
```

## New token addition

Each token needs to be added before it can be transferred. The EVM maintains a list of 2^32 tokens. The deposits, transfers, and withdraws reference a token index in this list. Anyone can add a new token by calling the add_token function on the smart contract.

To prevent squatting attacks, users need to burn 0.1 ether in order to add a new token.

Pseudo code
Smart contract

    // Add a new token
    function add_token() {
    
    }


# Operator selection mechanism

Operators are staked. 

1. Their probability of being selected to produce a block is proportional to their stake.
2. We use the hash of the block hash as our randomness beacon. This can be biased but at some cost to the miners. Since we don't really need to worry about attacks because a malicious miner can process transactions and probably get much less reward than the block reward. 
3. As soon as this is committed, a new operator is selected who has 5 blocks to commit to a batch of transactions. 
4. If they do not commit in this time a new operator is selected. This is repeated until a new batch of transactions is committed to. 
5. We only ever have `proof_time/blocktime` batches in progress.

If an operator fails to produce a proof for a batch of transactions they have commited to in `proof_time` they are slashed, all future commitments are cancelled, and we begin again with a new operator. 

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
    
    
    function commit_to_batch(transactions, transaction_list) {

    }

    function prove_batch () { 
        //finalize withdraws()
        roll_up.prove_transition(i, batch);
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
[This spreadsheet](https://docs.google.com/spreadsheets/d/1bT3MSgZ2_rs-MRrrMrs5NhuXqG_jmr5Qrhzkde_Tb30/edit#gid=0) shows how batches of transactions are aggregated and processed in parallel.

![Parallel proving ](https://i.imgur.com/F3frJ3b.png)

Stages:

 1. Collect transactions
 2. Pick & process a batch of transactions
 3. Submit commitment to batch of transactions to Ethereum
 4. Generate SNARK proof
 5. Submit proof to Ethereum

Once a batch of transactions has been picked, and the commitment submitted to Ethereum, then the next 'Epoch' begins while the previous is being proven.

As soon as someone commits to a batch we open a new auction. But we limit the number of open auctions/unproven commitments at `proving_time/blocktime` so that we can be making proofs to fill every block but not more than that. 

After the operator has committed they have `proving_time` to provide the proof. If they fail to provide the proof in this time they are slashed. 

We revert all commitments after this time and start the auction again. 

## Committing a batch
```
event BatchCommitted(
    uint256 batchNumber
);

function commitBatch(
    bytes32 newBalancesRoot,
    bytes transactions
);
```

When an operator commits a batch, it will provide a batch `transactions` along with `newBalancesRoot`. Based on the current on-chain balances root, all full clients and verify that the batch `transactions` are valid state transitions from the current balances root to `newBalancesRoot`. `H(transactions)` is stored in the contract so that the digest can be compared to the transactions included by the operator when proving the batch later - the operator must use the same batch of transactions when committing and proving a given batch. The operator will also provide a deposit.

## Proving a batch

```
event BatchProved(
    uint256 blockNum
);

function proveBatch(
    uint256 blockNum,
    bytes proof,
    bytes transactions
);
```

When an operator proves a batch, it will reference the previously committed batch by number to first check that the digest produced by `H(transactions)` matches the digest stored for the commited batch and will then retrieve the necessary on-chain data (i.e. accounts root, balances root) to be used for zkSNARK verification along with `proof` and the sequentially hashed output created for `transactions` (so that we can check that the transactions provided on-chain match the transactions used in the circuit).


## Transaction Format
### Snark Transactions

EdDSA signatures are used by users to send transactions. The operator uses these transactions to make a SNARK proof.

These are provided to the operator in the off-chain transaction. The transaction is represented as a JSON document:

```json
{
   "tx": {
      "from": index,
      "nonce": nnn,
      "to": public_key_x,
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


### Floating point format

This is the way it's encoded a 3 and a half decimal digits in a 16 bits floating point. Lets name those bits from MSB to LSB

e4 e3 e2 e1 e0 m9 m8 m7 m6 m5 m4 m3 m2 m1 m0 d 

exp := e0 + e1*2 + e2*2^2 + e3*2^3 + e4*2^4

m := m0 + m1*2 + m2*2^2 + m3*2^3 + m4*2^4 + m5*2^5 + m6*2^6 + m7*2^7 + m8*2^8 + m9*2^9

V := m*10^exp + d* ( (10^exp) >> 1 )

This format allows to use decimal numbers where the 3 most significant digits can be any digit [0..9] The fourth can be 0 or 5 and an exponent from 1 to 10^31

**Example 1: 123000000**

m = 123 => 0x7b => 0b00 0111 1011

d = 0 (The fourth digit is a 0)

exp = 6 => 0b00110

So the floating point format would be 0b0011000011110110  = 0x30F6

**Example 2:  454500**

m = 454 => 0x1c6 => 0b0111000110

d =1 (The fourth digit is a 5)

exp = 3 => 0x3 => 0b00011

So the floating point format is 0b0001101110001101 =   0x1B8D
