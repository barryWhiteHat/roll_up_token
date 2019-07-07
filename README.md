# roll_up token: Snark based multi-ERC20 side chain
A merkle tree is used to track accounts and balances. Multiple tokens are supported but each token requires a seperate account. The owner of a balance can sign a transaction to transfer part or all of the balance to another account, these transactions are batched via snark to prove that the state transition was correct. 

We maintain data availability by making sure that each zkSNARK proof must reveal a list of leaves that were changed and the amount that was transferred inside the EVM. We rely on Ethereum for data availability guarantees. 

The merkle tree is depth 24, which supports 2^24 accounts. Each account can only hold a single token. Multiple tokens can be transfered and traded inside a single block.

## Glossary of terms/variables:

 * roll up: a method of aggragateing multiple signatures and/or merkle tree updates inside a snark. 
 * Operator: The party aggragets many signatures into a single snark transaction. 
 * Circuit: The code that defines what the snark allows.
 * Block: ethereum block
 * Epoch: roll_up block which is a single snark proof of a state transition which contains many transactions.
 * account tree this is the merkle tree that stores a mapping between accounts and balances
 * account_tree_depth (24) this is the number of layers in the account merkle tree

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
![](https://raw.githubusercontent.com/barryWhiteHat/roll_up_token/master/images/database.png)

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
   * 2 bytes `amount`

The `to` address of `0` is a special address, it is the 'Withdraw' address. Any balance you send to leaf index `0` has a special meaning. The public key for leaf zero does not exit.

When the zkSNARK proof is submitted by the operator, if the destination is `0` the on-chain 'withdrawable balance' for the `from` leaf index is incremented by the amount, the amount needs converting from floating point to Wei unsigned integer.

The `from` address must have added a `withdraw_address` anyone can then send a transaction that sends the funds to this address.

Because any token type can be sent to the zero address. Transfers to the zero address should avoid the token type check.

Its important that no transfers are able to leave the zero address. 
1. The public key of the 0 leaf should be generated in such a way that no private key exists. 
2. The circuit logic should not allow leaf 0 to be the from address

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

## Transfer mechanism
We have a `balance_tree` with mapping of public key to balance of various tokens. We want to be able to transfer these tokens. The owner of a token creates a signature that signals their consent to update their balance. This signature constaints the following fields

* `from` - Leaf index (account_tree_depth bit unsigned) of sending account
   * `nonce` - account_tree_depth bit Nonce, to prevent transaction replays
   * `to` - Leaf index (24 bit unsigned) of receiving account
   * `amount` - Balance to transfer (16 bit unsigned)
   * `fee` - The fee to pay the operator
 * `sig` - Dictionary containing signature
   * `A` - Public point of signers key
   * `R` - Public point for EdDSA signature
   * `s` - Scalar for EdDSA signature (254bit in $\mathbb{F}_p$)

The snark then constraints the operator to processing these transactions in the following way. 

1. Prove that `from` index has a certin public key with a merkle proof
2. Prove that that public key matches the signature of the transaction
3. Reduce the balance of that leaf
4. Incrament the nonce of that leaf
5. Replace the orginal leaf with this update leaf, using the same merkle proof to insert it into the old tree while keeping every other leaf constant. This merkle root is called the intermediate merkle root
6. Using this intermediate merkle root prove that the the leaf `to` index is in the merkle tree. 
7. Check that `to.token_type == from.token_type`
8. Update teh balance of the `to` leaf. 
9. Using the same merkle proof as the original proof of membership insert the new leaf into the tree calculatieng the new merkle root. 

If any of these steps fail the whole proof fails. 

This is a single transaction in reality a proof contains many such transations. 


## Transaction Fees

We need to pay fees so the operator is incentivized to create blocks and process transactions. Its important that users can pay for fees in different tokens. This allows us to batch together more transactions in each block. As we have a larger pool we can include we can make blocks faster.

So we force the operator to commit to the fees in the EVM and then validate this is correct in the snark. We use an all pay fee modle. Where the operator commits to a fee and any fee transaction that specifies a fee less than or equal to this amount can be included and pays the fee that the operator commited to.

### Data availablity

#### Transactions
This approach is based [upon](https://ethresear.ch/t/on-chain-scaling-to-potentially-500-tx-sec-through-mass-tx-validation/3477)

Each transaction record is 8 bytes, and consists of:

1. `from` index (3 bytes)
2. `to` index   (3 bytes)
3. `amount`    (2 bytes) 


The `from` and `to` offsets specify the leaves within the tree, the size required for the offset depends on the depth of the tree. $TreeCapacity = 2^{tree\_depth}$, offset size in bits is $log_2(tree\_depth)$.

#### Fees

The data provided above is not enough to ensure that all data is available. As the amount recived at the to leaf is actually `amount - fee[token]`. Therefore we need the operator to commit to fee also for 16 different token types. 

1. `token_type` 32 bits 
2. `fee` 2 bytes
3. `number_transaction_of_this_type` 12 bits

For each batch, the records are concatenated together and then hashed to produce a single digest. This digest is passed as a public input to the zkSNARK circuit to ensure that the on-chain and in-circuit data match.

Then the circuit processes these transactions and ensures that 
1. Each token type is in the token schedual or has zero fee. 
2. The `no_tx_of_this_type == no_tx_processed`

After a proof has been finalized the operator can include withdraw `fee * number_transaction_of_this_type` of each token type they have included. 

### Dependent Payments

We want to allow for dependent payments. This allows us to do atomic swaps at almost no cost in terms of constraints.

The user can signal that their transaction is dependent upon a previous one 
by signaling via signature. These fields in the signature format are 
`"dependent_payments": [[to,from,amount], [to,from,amount]]`. Where `to`, `from`, `amount` define the transaction that this one depends upon. 

Then the snark confirms that each transaction has its dependecies included. 

#### Snark sudo-code
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

Each token needs to be added before it can be transfered. The EVM maintains a list of 2^32 to tokens. The deposits, transfers, and withdraws reference a token index in this list. Anyone can add a new token by calling the add_token function on the smart contract.

To prevent squating attacks, users need to burn 0.1 ether in order to add a new token.
Pseudo code
Smart contract

    // Add a new token
    function add_token() {
    
    }


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


## Transaction Format
### Snark Transactions

EdDSA signatures are used by users to send transactions. The operator uses these transactions to make a snark proof.

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

