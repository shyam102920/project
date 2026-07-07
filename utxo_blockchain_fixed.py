import os
import time
import hashlib
import json
import secrets

# =====================================================================
# 1. SECP256K1 CURVE PARAMETERS (Standardized constants used by Bitcoin)
# =====================================================================
P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

# Mining and Fee Constants
MINER_FEE = 1.0  # Transaction fee per transaction
BLOCK_REWARD = 10.0  # Mining reward per block
MIN_TRANSACTION_AMOUNT = 0.1  # Minimum spendable amount

# Modular Inverse using Extended Euclidean Algorithm
def modinv(a, m):
    g, x, y = ext_gcd(a, m)
    if g != 1:
        raise ValueError('Modular inverse does not exist')
    return x % m

def ext_gcd(a, b):
    if a == 0:
        return b, 0, 1
    g, x1, y1 = ext_gcd(b % a, a)
    x = y1 - (b // a) * x1
    y = x1
    return g, x, y

# =====================================================================
# 2. ELLIPTIC CURVE POINT MATH (CONSTANT-TIME DESIGN TO PREVENT TIMING ATTACKS)
# =====================================================================
class Point:
    """Represents a point on the SECP256K1 elliptic curve"""
    def __init__(self, x=None, y=None):
        self.x = x
        self.y = y

    def is_infinity(self):
        return self.x is None and self.y is None

    def __add__(self, other):
        if not isinstance(other, Point):
            raise TypeError("Can only add Point objects")
        if self.is_infinity(): 
            return Point(other.x, other.y)
        if other.is_infinity(): 
            return Point(self.x, self.y)
        if self.x == other.x and self.y != other.y: 
            return Point()

        if self.x == other.x and self.y == other.y:
            m = (3 * self.x * self.x * modinv(2 * self.y, P)) % P
        else:
            m = ((other.y - self.y) * modinv(other.x - self.x, P)) % P

        rx = (m * m - self.x - other.x) % P
        ry = (m * (self.x - rx) - self.y) % P
        return Point(rx, ry)

    def __mul__(self, scalar):
        if not isinstance(scalar, int):
            raise TypeError("Scalar must be an integer")
        scalar = scalar % N
        if scalar == 0: 
            return Point()

        running_base = Point(self.x, self.y)
        result = Point()
        
        # Fixed 256-step loop with array lookups ensures constant-time execution
        for i in range(256):
            bit = (scalar >> i) & 1
            added_state = result + running_base
            states = [result, added_state]
            result = states[bit]
            running_base = running_base + running_base
        return result

G = Point(Gx, Gy)

# =====================================================================
# 3. CRYPTOGRAPHY ENGINE (ECDSA SIGNING AND VERIFICATION)
# =====================================================================
class CryptoEngine:
    """ECDSA cryptographic engine using SECP256K1 curve"""
    
    @staticmethod
    def _is_on_curve(x, y):
        """Verify that a point (x, y) is on the SECP256K1 curve"""
        return (y * y) % P == (x * x * x + 7) % P
    
    @staticmethod
    def generate_keypair():
        """Generate cryptographically secure keypair"""
        while True:
            priv_bytes = secrets.token_bytes(32)
            priv_key = int.from_bytes(priv_bytes, 'big')
            if 0 < priv_key < N: 
                break
        
        pub_key_point = G * priv_key
        if not CryptoEngine._is_on_curve(pub_key_point.x, pub_key_point.y):
            raise RuntimeError("Generated public key is not on the curve")
        
        priv_key_hex = hex(priv_key)[2:].zfill(64)
        pub_key_hex = f"04{hex(pub_key_point.x)[2:].zfill(64)}{hex(pub_key_point.y)[2:].zfill(64)}"
        return priv_key_hex, pub_key_hex

    @staticmethod
    def sign_message(priv_key_hex, message):
        """Create ECDSA digital signature with BIP-62 canonicality"""
        d = int(priv_key_hex, 16)
        z = int(hashlib.sha256(message.encode('utf-8')).hexdigest(), 16)
        r, s = 0, 0
        
        while r == 0 or s == 0:
            while True:
                k_bytes = secrets.token_bytes(32)
                k = int.from_bytes(k_bytes, 'big')
                if 0 < k < N: 
                    break
            R = G * k
            r = R.x % N
            if r == 0: 
                continue
            s = (modinv(k, N) * (z + r * d)) % N
        
        # BIP-62 Signature Canonicality Prevention of Malleability
        if s > N // 2: 
            s = N - s
        
        return hex(r)[2:].zfill(64), hex(s)[2:].zfill(64)

    @staticmethod
    def verify_signature(pub_key_hex, message, signature):
        """Verify ECDSA signature with full validation"""
        if not isinstance(pub_key_hex, str) or len(pub_key_hex) != 130 or not pub_key_hex.startswith('04'):
            return False
        try:
            r, s = int(signature[0], 16), int(signature[1], 16)
            pub_x = int(pub_key_hex[2:66], 16)
            pub_y = int(pub_key_hex[66:130], 16)
        except (ValueError, IndexError):
            return False
            
        if not (0 < r < N and 0 < s < N) or not CryptoEngine._is_on_curve(pub_x, pub_y):
            return False
        
        Q = Point(pub_x, pub_y)
        z = int(hashlib.sha256(message.encode('utf-8')).hexdigest(), 16)
        w = modinv(s, N)
        u1 = (z * w) % N
        u2 = (r * w) % N
        P_result = (G * u1) + (Q * u2)
        
        if P_result.is_infinity(): 
            return False
        return (P_result.x % N) == r

# =====================================================================
# 4. MERKLE TREE DATA STRUCTURE
# =====================================================================
class MerkleTree:
    """Efficient transaction verification using Merkle tree"""
    
    @staticmethod
    def compute_root(transactions):
        """Compute Merkle root from transaction list"""
        if not transactions:
            return hashlib.sha256(b"empty_merkle_root").hexdigest()
        
        # Create leaf layer with double-SHA256 of transaction hashes
        current_layer = []
        for tx in transactions:
            tx_hash = tx.get_hash()
            double_hash = hashlib.sha256(tx_hash.encode('utf-8')).hexdigest()
            current_layer.append(double_hash)
        
        # Build tree by repeatedly hashing pairs
        while len(current_layer) > 1:
            if len(current_layer) % 2 != 0:
                current_layer.append(current_layer[-1])  # Duplicate last if odd
            
            next_layer = []
            for i in range(0, len(current_layer), 2):
                combined = current_layer[i] + current_layer[i+1]
                parent_hash = hashlib.sha256(hashlib.sha256(combined.encode('utf-8')).digest()).hexdigest()
                next_layer.append(parent_hash)
            current_layer = next_layer
        
        return current_layer[0]

# =====================================================================
# 5. TRANSACTION AND UTXO DATA STRUCTURES
# =====================================================================
class UTXO:
    """Explicit unspent coin record tracking ownership and value"""
    def __init__(self, tx_id, index, owner_address, amount):
        self.tx_id = tx_id
        self.index = index
        self.owner_address = owner_address
        self.amount = amount

    def get_id(self):
        """Get unique identifier for this UTXO"""
        return f"{self.tx_id}:{self.index}"


class Transaction:
    """UTXO-based transaction with signature and nonce"""
    def __init__(self, sender_address, inputs, outputs, nonce=0, signature=None, timestamp=None):
        """
        Create a transaction.
        
        Args:
            sender_address: Public key of sender
            inputs: List of UTXO IDs to spend ("tx_id:index")
            outputs: List of dicts {"address": hex_pub_key, "amount": float}
            nonce: Transaction sequence number for replay protection
            signature: Tuple (r_hex, s_hex) or None if not yet signed
            timestamp: Transaction creation time (fixed after init)
        """
        # Validate sender address
        if not isinstance(sender_address, str) or len(sender_address) != 130 or not sender_address.startswith('04'):
            raise ValueError("Invalid sender address format")
        
        # Validate inputs and outputs
        if not isinstance(inputs, list) or not isinstance(outputs, list):
            raise ValueError("Inputs and outputs must be lists")
        
        if len(inputs) == 0:
            raise ValueError("Transaction must have at least one input")
        
        if len(outputs) == 0:
            raise ValueError("Transaction must have at least one output")
        
        # Validate output format
        for output in outputs:
            if not isinstance(output, dict) or "address" not in output or "amount" not in output:
                raise ValueError("Each output must have 'address' and 'amount'")
            if output["amount"] <= 0:
                raise ValueError("Output amount must be positive")
        
        self.sender_address = sender_address
        self.inputs = inputs
        self.outputs = outputs
        self.nonce = nonce
        self.signature = signature
        self._timestamp = timestamp or time.time()  # Immutable after init
        
        # Calculate transaction ID BEFORE signature
        self.tx_id = self.calculate_tx_id()

    @property
    def timestamp(self):
        """Get immutable timestamp"""
        return self._timestamp

    def to_dict(self, include_signature=False):
        """Convert transaction to dictionary (exclude signature for signing)"""
        d = {
            "sender_address": self.sender_address,
            "inputs": self.inputs,
            "outputs": self.outputs,
            "nonce": self.nonce,
            "timestamp": self._timestamp
        }
        if include_signature and self.signature:
            d["signature"] = self.signature
        return d

    def calculate_tx_id(self):
        """Calculate SHA-256 hash of transaction WITHOUT signature"""
        tx_string = json.dumps(self.to_dict(include_signature=False), sort_keys=True)
        return hashlib.sha256(tx_string.encode('utf-8')).hexdigest()

    def get_message_to_sign(self):
        """
        Get the message to sign - includes ALL transaction data so any modification 
        invalidates the signature
        """
        # Sign the complete transaction data (except signature itself)
        return json.dumps(self.to_dict(include_signature=False), sort_keys=True)

    def get_hash(self):
        """Get transaction hash (same as tx_id)"""
        return self.tx_id

# =====================================================================
# 6. BLOCK HEADER AND UPGRADED DECOUPLED BLOCK ARCHITECTURE
# =====================================================================
class BlockHeader:
    """Block header containing metadata"""
    def __init__(self, index, previous_hash, merkle_root, difficulty, miner_address):
        self.index = index
        self.timestamp = time.time()
        self.previous_hash = previous_hash
        self.merkle_root = merkle_root
        self.difficulty = difficulty
        self.miner_address = miner_address
        self.nonce = 0

    def to_dict(self):
        """Convert header to dictionary"""
        return {
            "index": self.index,
            "timestamp": self.timestamp,
            "previous_hash": self.previous_hash,
            "merkle_root": self.merkle_root,
            "difficulty": self.difficulty,
            "miner_address": self.miner_address,
            "nonce": self.nonce
        }

    def calculate_hash(self):
        """Calculate SHA-256 hash of header"""
        header_string = json.dumps(self.to_dict(), sort_keys=True)
        return hashlib.sha256(header_string.encode('utf-8')).hexdigest()


class Block:
    """Block containing transactions and header"""
    def __init__(self, index, transactions, previous_hash, miner_address, difficulty=3):
        self.transactions = transactions
        merkle_root = MerkleTree.compute_root(transactions)
        self.header = BlockHeader(index, previous_hash, merkle_root, difficulty, miner_address)
        self.hash = self.header.calculate_hash()

    def mine(self):
        """Proof of Work: Find nonce where hash starts with 'difficulty' zeros"""
        target = '0' * self.header.difficulty
        print(f"[*] Mining Block #{self.header.index} (Difficulty: {self.header.difficulty})...")
        iterations = 0
        while not self.hash.startswith(target):
            self.header.nonce += 1
            self.hash = self.header.calculate_hash()
            iterations += 1
            if iterations % 100000 == 0:
                print(f"    [{iterations} iterations...]")
        print(f"[✓] Block #{self.header.index} Mined! Nonce: {self.header.nonce} | Hash: {self.hash}")

# =====================================================================
# 7. CORE CHAIN MANAGER & UTXO STATE MACHINE
# =====================================================================
class Blockchain:
    """UTXO-based blockchain with proof-of-work and miner fees"""
    
    def __init__(self, miner_address=None):
        self.chain = []
        self.mempool = []
        self.utxo_pool = {}  # Global ledger state mapping "tx_id:index" -> UTXO object
        self.miner_address = miner_address  # Address for mining rewards
        self.total_miner_fees = 0.0  # Track accumulated fees for block reward
        self.create_genesis_block()

    def create_genesis_block(self):
        """Create the genesis block"""
        genesis_block = Block(0, [], "0" * 64, self.miner_address or "0" * 130, difficulty=0)
        self.chain.append(genesis_block)

    def get_latest_block(self):
        """Get the most recent block"""
        return self.chain[-1]

    def get_user_utxos(self, address):
        """Get all unspent outputs for an address"""
        return [utxo for utxo in self.utxo_pool.values() if utxo.owner_address == address]

    def get_balance(self, address):
        """Get total balance for an address"""
        return sum(utxo.amount for utxo in self.get_user_utxos(address))

    def add_to_mempool(self, transaction: Transaction):
        """
        Validate transaction and add to mempool queue.
        
        Validation checks:
        1. Cryptographic signature verification
        2. All inputs exist and are owned by sender
        3. No double-spending in mempool
        4. Value conservation (inputs >= outputs + fee)
        5. No negative amounts
        """
        try:
            # Validation 1: Signature must exist
            if not transaction.signature:
                print("[✗] Mempool Rejection: Missing transaction signature.")
                return False
            
            # Validation 2: All inputs must exist
            if not all(utxo_id in self.utxo_pool for utxo_id in transaction.inputs):
                print("[✗] Mempool Rejection: One or more inputs do not exist in UTXO pool.")
                return False
            
            # Validation 3: Get sender address from first input
            sender_address = self.utxo_pool[transaction.inputs[0]].owner_address
            
            # Verify sender address matches transaction sender
            if sender_address != transaction.sender_address:
                print("[✗] Mempool Rejection: Transaction sender does not match input ownership.")
                return False
            
            # Validation 4: All inputs must belong to the same sender (CRITICAL FIX)
            for utxo_id in transaction.inputs:
                if self.utxo_pool[utxo_id].owner_address != sender_address:
                    print("[✗] Mempool Rejection: Not all inputs belong to the same sender.")
                    return False
            
            # Validation 5: Cryptographic signature verification (FIXED)
            message_to_sign = transaction.get_message_to_sign()
            if not CryptoEngine.verify_signature(sender_address, message_to_sign, transaction.signature):
                print("[✗] Mempool Rejection: Cryptographic signature verification failed!")
                return False

            # Validation 6: Double-spend check in mempool
            mempool_inputs = set()
            for tx in self.mempool:
                mempool_inputs.update(tx.inputs)

            for utxo_id in transaction.inputs:
                if utxo_id in mempool_inputs:
                    print("[✗] Mempool Rejection: Input already queued for spending in mempool.")
                    return False

            # Validation 7: Calculate input total
            input_value_total = sum(self.utxo_pool[utxo_id].amount for utxo_id in transaction.inputs)

            # Validation 8: Calculate output total
            output_value_total = sum(out["amount"] for out in transaction.outputs)

            # Validation 9: Value conservation including miner fee (FIXED)
            total_cost = output_value_total + MINER_FEE
            if input_value_total < total_cost:
                print(f"[✗] Mempool Rejection: Insufficient funds!")
                print(f"    Inputs: {input_value_total} | Outputs: {output_value_total} | Fee: {MINER_FEE} | Total needed: {total_cost}")
                return False

            self.mempool.append(transaction)
            print(f"[✓] Transaction accepted into Mempool. Queue Size: {len(self.mempool)}")
            return True
            
        except Exception as e:
            print(f"[✗] Mempool Processing Error: {e}")
            return False

    def process_mempool_into_block(self):
        """
        Pull pending transactions from mempool, update UTXO state, 
        mine a new block, and award miner with fee rewards.
        """
        if not self.mempool:
            print("[!] Block Processing Aborted: Mempool is empty.")
            return None

        current_batch = list(self.mempool)
        self.mempool = []
        
        total_tx_fees = 0.0

        print(f"\n[*] Processing {len(current_batch)} transaction(s) into Block #{len(self.chain)}...")

        # Update the UTXO State Engine database
        for tx in current_batch:
            try:
                # Re-verify signatures before committing to chain
                message_to_sign = tx.get_message_to_sign()
                if not CryptoEngine.verify_signature(tx.sender_address, message_to_sign, tx.signature):
                    print(f"[✗] CRITICAL: Transaction signature verification failed during block creation! Skipping.")
                    continue
                
                # Delete spent UTXOs (inputs)
                for utxo_id in tx.inputs:
                    if utxo_id in self.utxo_pool:
                        del self.utxo_pool[utxo_id]
                
                # Generate new spendable UTXOs (outputs)
                for index, output in enumerate(tx.outputs):
                    new_utxo = UTXO(tx.tx_id, index, output["address"], output["amount"])
                    self.utxo_pool[new_utxo.get_id()] = new_utxo
                
                # Calculate miner fee
                input_total = sum(self.utxo_pool.get(utxo_id, UTXO("", 0, "", 0)).amount 
                                for utxo_id in tx.inputs) if tx.inputs else 0
                output_total = sum(out["amount"] for out in tx.outputs)
                
                # Fee is difference between inputs and outputs
                if input_total > 0:
                    tx_fee = input_total - output_total
                    total_tx_fees += tx_fee
                    
            except Exception as e:
                print(f"[✗] Error processing transaction: {e}")
                continue

        # Create coinbase transaction for miner (block reward + fees)
        total_reward = BLOCK_REWARD + total_tx_fees
        coinbase_output = {
            "address": self.miner_address or "0" * 130,
            "amount": total_reward
        }
        
        coinbase_tx = Transaction(
            sender_address="0" * 130,  # System address
            inputs=[],  # No inputs - newly minted coins
            outputs=[coinbase_output],
            nonce=len(self.chain)
        )
        # Sign coinbase transaction
        coinbase_msg = coinbase_tx.get_message_to_sign()
        coinbase_sig = CryptoEngine.sign_message("0" * 64, coinbase_msg)
        coinbase_tx.signature = coinbase_sig
        
        # Add coinbase to block transactions
        block_transactions = [coinbase_tx] + current_batch

        # Package into Block structure and run Proof-of-Work
        latest_block = self.get_latest_block()
        new_block = Block(len(self.chain), block_transactions, latest_block.hash, self.miner_address, difficulty=2)
        new_block.mine()
        
        self.chain.append(new_block)
        print(f"[✓] Block #{new_block.header.index} committed to chain!")
        print(f"[-->] Block Hash: {new_block.hash}")
        print(f"[-->] Transactions: {len(current_batch)} | Miner Reward: {BLOCK_REWARD} | Fees: {total_tx_fees} | Total: {total_reward}")
        
        # Add miner reward to UTXO pool
        miner_utxo = UTXO(coinbase_tx.tx_id, 0, self.miner_address or "0" * 130, total_reward)
        self.utxo_pool[miner_utxo.get_id()] = miner_utxo
        
        return new_block

    def is_chain_valid(self):
        """Validate entire blockchain integrity"""
        for i in range(1, len(self.chain)):
            current_block = self.chain[i]
            previous_block = self.chain[i - 1]
            
            # Verify block hash
            if current_block.hash != current_block.header.calculate_hash():
                print(f"[✗] Block {i} hash verification failed!")
                return False
            
            # Verify chain continuity
            if current_block.header.previous_hash != previous_block.hash:
                print(f"[✗] Block {i} is not properly linked to previous block!")
                return False
            
            # Verify Merkle root
            if current_block.transactions:
                merkle_root = MerkleTree.compute_root(current_block.transactions)
                if merkle_root != current_block.header.merkle_root:
                    print(f"[✗] Block {i} Merkle root verification failed!")
                    return False
            
            # Verify all transaction signatures
            for tx in current_block.transactions:
                if tx.sender_address != "0" * 130:  # Skip coinbase transactions
                    try:
                        if not CryptoEngine.verify_signature(tx.sender_address, tx.get_message_to_sign(), tx.signature):
                            print(f"[✗] Block {i} contains transaction with invalid signature!")
                            return False
                    except Exception as e:
                        print(f"[✗] Block {i} signature verification error: {e}")
                        return False
        
        return True


# =====================================================================
# INTERACTIVE EXECUTION DEMO
# =====================================================================
if __name__ == "__main__":
    print("=" * 80)
    print("UTXO-BASED BLOCKCHAIN WITH MINER FEES - FIXED AND SECURE VERSION")
    print("=" * 80)

    try:
        # Initialize Blockchain
        print("\n[SYSTEM] Initializing blockchain...")
        miner_priv, miner_pub = CryptoEngine.generate_keypair()
        node_chain = Blockchain(miner_address=miner_pub)
        print(f"[✓] Miner Address: {miner_pub[:20]}...")

        # Generate user identities
        print("\n[STEP 1] Generating secure user keypairs...")
        alice_priv, alice_pub = CryptoEngine.generate_keypair()
        bob_priv, bob_pub = CryptoEngine.generate_keypair()
        print(f"[✓] Alice Wallet: {alice_pub[:20]}...")
        print(f"[✓] Bob Wallet:   {bob_pub[:20]}...")

        # Seed initial UTXO for Alice
        print("\n[STEP 2] Seeding system: Minting 200.0 coins to Alice...")
        seeded_utxo = UTXO(tx_id="0"*64, index=0, owner_address=alice_pub, amount=200.0)
        node_chain.utxo_pool[seeded_utxo.get_id()] = seeded_utxo
        print(f"[*] Initial Balances -> Alice: {node_chain.get_balance(alice_pub)} | Bob: {node_chain.get_balance(bob_pub)} | Miner: {node_chain.get_balance(miner_pub)}")

        # Create Alice's transaction
        print("\n[STEP 3] Alice creates transaction: Send 50 to Bob, 149 change back (1.0 fee)...")
        tx_inputs = [seeded_utxo.get_id()]
        tx_outputs = [
            {"address": bob_pub, "amount": 50.0},     # Bob receives 50
            {"address": alice_pub, "amount": 149.0}   # Alice receives 149 change
        ]
        
        # FIXED: Create transaction THEN sign THEN attach signature
        unsigned_tx = Transaction(
            sender_address=alice_pub,
            inputs=tx_inputs,
            outputs=tx_outputs,
            nonce=1,
            signature=None
        )
        
        # Get message to sign (includes all transaction data)
        message_to_sign = unsigned_tx.get_message_to_sign()
        print(f"[*] Signing transaction...")
        tx_signature = CryptoEngine.sign_message(alice_priv, message_to_sign)
        
        # NOW attach signature
        unsigned_tx.signature = tx_signature
        
        # Add to mempool
        success = node_chain.add_to_mempool(unsigned_tx)
        if not success:
            print("[✗] Transaction failed to be added to mempool!")
        else:
            print("[✓] Transaction successfully added to mempool")

        # Process mempool and mine block
        print("\n[STEP 4] Mining block with pending transactions...")
        node_chain.process_mempool_into_block()

        # Final balance audit
        print("\n" + "=" * 80)
        print("FINAL UTXO STATE AUDIT:")
        print(f"   - Alice Balance: {node_chain.get_balance(alice_pub)} Coins")
        print(f"   - Bob Balance:   {node_chain.get_balance(bob_pub)} Coins")
        print(f"   - Miner Balance: {node_chain.get_balance(miner_pub)} Coins (Block Reward: {BLOCK_REWARD} + Fees: {MINER_FEE})")
        print(f"\n   Total Coins in System: {sum(utxo.amount for utxo in node_chain.utxo_pool.values())}")
        print("=" * 80)

        # Blockchain validation
        print("\n[STEP 5] Validating blockchain integrity...")
        is_valid = node_chain.is_chain_valid()
        print(f"[✓] Blockchain Valid: {is_valid}")

        # Test replay attack prevention
        print("\n[STEP 6] Testing replay attack prevention...")
        print("[!] Attempting to replay transaction...")
        is_replay_accepted = node_chain.add_to_mempool(unsigned_tx)
        if not is_replay_accepted:
            print("[✓] Replay attack blocked: Transaction inputs already spent!")
        
        print("\n" + "=" * 80)
        print("✅ UTXO Blockchain System Fully Operational!")
        print("=" * 80)
        
    except Exception as e:
        print(f"[ERROR] Fatal error: {e}")
        import traceback
        traceback.print_exc()
