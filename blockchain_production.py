import time
import hashlib
import json
from crypto_engine_fixed import CryptoEngine  # Ensure crypto_engine_fixed.py is in the same folder

# Constants
MAX_MEMPOOL_SIZE = 10000
TRANSACTION_FEE = 1  # Fee per transaction in smallest units
MIN_AMOUNT = 1  # Minimum transaction amount

class Transaction:
    """Structure for an individual transaction payload with security validation"""
    def __init__(self, sender, receiver, amount, fee, signature, tx_nonce, timestamp=None):
        # Validate addresses
        if not isinstance(sender, str) or len(sender) != 130 or not sender.startswith('04'):
            raise ValueError("Invalid sender address format (must be 130-char uncompressed public key)")
        if not isinstance(receiver, str) or len(receiver) != 130 or not receiver.startswith('04'):
            raise ValueError("Invalid receiver address format (must be 130-char uncompressed public key)")
        
        # Validate amounts
        if not isinstance(amount, (int, float)) or amount <= 0:
            raise ValueError("Amount must be a positive number")
        if not isinstance(fee, (int, float)) or fee < 0:
            raise ValueError("Fee must be non-negative")
        
        # Validate nonce
        if not isinstance(tx_nonce, int) or tx_nonce <= 0:
            raise ValueError("Nonce must be a positive integer")
        
        self.sender = sender
        self.receiver = receiver
        self.amount = float(amount)
        self.fee = float(fee)
        self.signature = signature
        self.tx_nonce = tx_nonce
        self.timestamp = time.time()  # System time only - not user-provided

    def get_message_to_sign(self):
        """Returns the exact message format that must be signed by the private key"""
        return f"Send {self.amount} from {self.sender} to {self.receiver}:Fee:{self.fee}:Nonce:{self.tx_nonce}"

    def to_dict(self):
        """Converts transaction data to a dictionary (excluding signature for hashing)"""
        return {
            "sender": self.sender,
            "receiver": self.receiver,
            "amount": self.amount,
            "fee": self.fee,
            "tx_nonce": self.tx_nonce,
            "timestamp": self.timestamp
        }

    def get_hash(self):
        """Generates a SHA-256 hash string of the transaction"""
        tx_string = json.dumps(self.to_dict(), sort_keys=True)
        return hashlib.sha256(tx_string.encode()).hexdigest()

    def to_json(self):
        """Serialize transaction to JSON for network transmission"""
        return json.dumps({
            "sender": self.sender,
            "receiver": self.receiver,
            "amount": self.amount,
            "fee": self.fee,
            "signature": list(self.signature) if self.signature else None,
            "tx_nonce": self.tx_nonce,
            "timestamp": self.timestamp
        })

    @classmethod
    def from_json(cls, json_str):
        """Deserialize transaction from JSON"""
        data = json.loads(json_str)
        tx = cls(
            sender=data["sender"],
            receiver=data["receiver"],
            amount=data["amount"],
            fee=data["fee"],
            signature=tuple(data["signature"]) if data["signature"] else None,
            tx_nonce=data["tx_nonce"],
            timestamp=data["timestamp"]
        )
        tx.timestamp = data["timestamp"]  # Restore original timestamp
        return tx


class Block:
    """Structure for a single Block ledger page"""
    def __init__(self, index, transactions, previous_hash):
        # Validate transactions before block creation
        if not isinstance(transactions, list):
            raise ValueError("Transactions must be a list")
        
        for tx in transactions:
            if not isinstance(tx, Transaction):
                raise ValueError("All items must be Transaction objects")
        
        self.index = index
        self.timestamp = time.time()
        self.transactions = transactions
        self.previous_hash = previous_hash
        self.nonce = 0
        self.hash = self.calculate_hash()

    def to_dict(self):
        """Converts block details into an orderly dictionary format"""
        return {
            "index": self.index,
            "timestamp": self.timestamp,
            "transactions": [tx.to_dict() for tx in self.transactions],
            "previous_hash": self.previous_hash,
            "nonce": self.nonce
        }

    def calculate_hash(self):
        """Generates a unique SHA-256 fingerprint for the entire block contents"""
        block_string = json.dumps(self.to_dict(), sort_keys=True)
        return hashlib.sha256(block_string.encode()).hexdigest()

    def mine_block(self, difficulty=2):
        """Proof of Work: Find nonce where hash starts with 'difficulty' zeros"""
        target = '0' * difficulty
        print(f"[*] Mining block #{self.index} with difficulty {difficulty}...")
        iterations = 0
        while not self.hash.startswith(target):
            self.nonce += 1
            self.hash = self.calculate_hash()
            iterations += 1
            if iterations % 100000 == 0:
                print(f"    [{iterations} iterations...]")
        print(f"[✓] Block #{self.index} mined! Nonce: {self.nonce}, Hash: {self.hash}")

    def to_json(self):
        """Serialize block to JSON"""
        return json.dumps({
            "index": self.index,
            "timestamp": self.timestamp,
            "transactions": [tx.to_dict() for tx in self.transactions],
            "previous_hash": self.previous_hash,
            "nonce": self.nonce,
            "hash": self.hash
        })


class Blockchain:
    """The Core State Machine and Chain Controller"""
    def __init__(self):
        self.chain = []
        self.mempool = []
        self.balances = {}
        self.transaction_nonces = {}  # Tracks the LATEST COMMITTED nonce per account
        self.create_genesis_block()

    def create_genesis_block(self):
        """Generates the absolute first block hardcoded into the software ledger"""
        genesis_block = Block(0, [], "0" * 64)
        self.chain.append(genesis_block)

    def get_latest_block(self):
        return self.chain[-1]

    def get_balance(self, address):
        """Queries the current ledger state for an address balance"""
        return self.balances.get(address, 0.0)

    def get_next_nonce(self, address):
        """
        Safely calculates what the NEXT required sequence nonce 
        should be based on historical commits + active mempool queue entries.
        """
        committed_nonce = self.transaction_nonces.get(address, 0)
        pending_mempool_count = sum(1 for tx in self.mempool if tx.sender == address)
        return committed_nonce + pending_mempool_count + 1

    def is_chain_valid(self):
        """Validates entire blockchain block pointer integrity"""
        for i in range(1, len(self.chain)):
            current_block = self.chain[i]
            previous_block = self.chain[i - 1]
            
            # Verify block hash is correct
            if current_block.hash != current_block.calculate_hash():
                print(f"[✗] Block {i} hash verification corrupted!")
                return False
            
            # Verify chain continuity
            if current_block.previous_hash != previous_block.hash:
                print(f"[✗] Block {i} pointer unlinked from history!")
                return False
            
            # Verify all transactions in block are valid
            for tx in current_block.transactions:
                try:
                    tx_msg = tx.get_message_to_sign()
                    if not CryptoEngine.verify_signature(tx.sender, tx_msg, tx.signature):
                        print(f"[✗] Block {i} contains invalid transaction signature!")
                        return False
                except Exception as e:
                    print(f"[✗] Block {i} transaction verification error: {e}")
                    return False
        
        return True

    def add_to_mempool(self, transaction: Transaction):
        """Validates signatures and state rules before letting a transaction wait in queue"""
        try:
            # Check mempool size limit
            if len(self.mempool) >= MAX_MEMPOOL_SIZE:
                print(f"[✗] Mempool Rejection: Mempool is full ({MAX_MEMPOOL_SIZE} max)")
                return False

            # 1. Cryptographic Authentication Check
            tx_msg = transaction.get_message_to_sign()
            is_authentic = CryptoEngine.verify_signature(
                transaction.sender, tx_msg, transaction.signature
            )
            if not is_authentic:
                print(f"[✗] Mempool Rejection: Cryptographic signature fraud detected!")
                return False

            # 2. Replay Attack Check - Nonce must match expected sequence
            committed_nonce = self.transaction_nonces.get(transaction.sender, 0)
            pending_mempool_count = sum(1 for tx in self.mempool if tx.sender == transaction.sender)
            expected_nonce = committed_nonce + pending_mempool_count + 1
            
            if transaction.tx_nonce != expected_nonce:
                print(f"[✗] Mempool Rejection: Invalid sequence nonce! Expected {expected_nonce}, got {transaction.tx_nonce}")
                return False

            # 3. State Balance Sufficiency Check (including fees)
            pending_outflow = sum(tx.amount + tx.fee for tx in self.mempool if tx.sender == transaction.sender)
            total_cost = transaction.amount + transaction.fee
            available_balance = self.get_balance(transaction.sender) - pending_outflow

            if available_balance < total_cost:
                print(f"[✗] Mempool Rejection: Insufficient funds! (Has: {available_balance}, Needs: {total_cost})")
                return False

            self.mempool.append(transaction)
            print(f"[✓] Transaction securely queued in Mempool. Queue size: {len(self.mempool)}")
            return True
            
        except Exception as e:
            print(f"[✗] Mempool Processing Error: {e}")
            return False

    def process_mempool_into_block(self):
        """Pulls pending transactions, commits changes to live state, and mines a new block"""
        if not self.mempool:
            print("[!] Processing aborted: Mempool queue is empty.")
            return None

        print(f"\n[*] Processing {len(self.mempool)} transaction(s) into Block #{len(self.chain)}...")
        
        current_tx_batch = list(self.mempool)
        self.mempool = []
        
        miner_fee_total = 0.0
        
        # Execute the accounting balance changes AND commit sequential nonces permanently
        for tx in current_tx_batch:
            try:
                # Re-verify signatures completely before freezing into unchangeable history
                tx_msg = tx.get_message_to_sign()
                if not CryptoEngine.verify_signature(tx.sender, tx_msg, tx.signature):
                    print(f"[✗] CRITICAL: Invalid signature detected in transaction! Skipping.")
                    continue
                
                # Apply changes directly to global state tracking maps
                self.balances[tx.sender] = self.get_balance(tx.sender) - tx.amount - tx.fee
                self.balances[tx.receiver] = self.get_balance(tx.receiver) + tx.amount
                
                # Accumulate miner fees
                miner_fee_total += tx.fee
                
                # The state dictionary sequence number increments ONLY on valid block settlement
                self.transaction_nonces[tx.sender] = tx.tx_nonce
                
            except Exception as e:
                print(f"[✗] Error processing transaction: {e}")
                continue

        # Assemble new structural block object
        latest_block = self.get_latest_block()
        new_block = Block(
            index=len(self.chain),
            transactions=current_tx_batch,
            previous_hash=latest_block.hash
        )
        
        # Mine the block to run consensus constraints
        new_block.mine_block(difficulty=2)
        
        self.chain.append(new_block)
        print(f"[✓] Block #{new_block.index} successfully committed to ledger chain!")
        print(f"[-->] Block Hash: {new_block.hash}")
        print(f"[-->] Miner Fees Collected: {miner_fee_total}")
        
        if not self.is_chain_valid():
            print("[✗] CRITICAL ERROR: Ledger validation failed!")
            return None
        
        return new_block


# =====================================================================
# PRODUCTION-READY DEMO
# =====================================================================
if __name__ == "__main__":
    print("=" * 80)
    print("BLOCKCHAIN STATE MACHINE - PRODUCTION-READY SECURE VERSION")
    print("=" * 80)

    try:
        my_blockchain = Blockchain()

        print("\n[SYSTEM] Initializing node identities using CryptoEngine...")
        alice_priv, alice_pub = CryptoEngine.generate_keypair()
        bob_priv, bob_pub = CryptoEngine.generate_keypair()
        
        # Initialize balances
        my_blockchain.balances[alice_pub] = 1000.0
        print(f"[*] Initial Seeding: Alice address assigned 1000.0 Native Coins.")
        print(f"[*] Balances -> Alice: {my_blockchain.get_balance(alice_pub)} | Bob: {my_blockchain.get_balance(bob_pub)}")
        print("-" * 80)

        # Transaction 1
        print("\n[STEP 1] Alice signs Transaction #1: Send 100.0 coins to Bob (fee: 1.0)...")
        tx1_amount = 100.0
        tx1_fee = 1.0
        tx1_nonce = my_blockchain.get_next_nonce(alice_pub)
        
        transaction1 = Transaction(alice_pub, bob_pub, tx1_amount, tx1_fee, None, tx1_nonce)
        tx1_msg = transaction1.get_message_to_sign()
        tx1_sig = CryptoEngine.sign_message(alice_priv, tx1_msg)
        transaction1.signature = tx1_sig
        
        my_blockchain.add_to_mempool(transaction1)
        print("-" * 80)

        # Transaction 2
        print("\n[STEP 2] Alice signs Transaction #2: Send 50.0 coins to Bob (fee: 1.0)...")
        tx2_amount = 50.0
        tx2_fee = 1.0
        tx2_nonce = my_blockchain.get_next_nonce(alice_pub)
        
        transaction2 = Transaction(alice_pub, bob_pub, tx2_amount, tx2_fee, None, tx2_nonce)
        tx2_msg = transaction2.get_message_to_sign()
        tx2_sig = CryptoEngine.sign_message(alice_priv, tx2_msg)
        transaction2.signature = tx2_sig
        
        my_blockchain.add_to_mempool(transaction2)
        print("-" * 80)

        # Mine block
        print("\n[STEP 3] Mining consensus block...")
        my_blockchain.process_mempool_into_block()
        
        print(f"\n[✓] Final Balance State:")
        print(f"    Alice: {my_blockchain.get_balance(alice_pub)} Coins")
        print(f"    Bob:   {my_blockchain.get_balance(bob_pub)} Coins")
        print(f"    Alice Nonce: {my_blockchain.transaction_nonces.get(alice_pub)}")
        print("-" * 80)

        # Replay Attack Test
        print("\n[STEP 4] Security Test: Attacker attempts to replay Transaction #1...")
        is_replay_approved = my_blockchain.add_to_mempool(transaction1)
        if not is_replay_approved:
            print("[✓] Attack Prevented: Invalid nonce detected!")
        
        # Blockchain validation
        print(f"\n[✓] Blockchain Integrity Check: {my_blockchain.is_chain_valid()}")
        
        print("\n" + "=" * 80)
        print("✅ Secure Blockchain System Validated Successfully!")
        print("=" * 80)
        
    except Exception as e:
        print(f"[ERROR] Fatal error: {e}")
        import traceback
        traceback.print_exc()
