
import json
import logging
import socket
import struct
import hashlib
import threading
import time
import sys
import secrets
from cryptography.hazmat.primitives.asymmetric import ec
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives import serialization
import sqlite3

# --- GLOBAL CONFIGURATION CONSTANTS (Fix 57) ---
MAGIC_BYTES = b"\xF9\xBE\xB4\xD9"
MAX_MESSAGE_SIZE = 2 * 1024 * 1024  # 2MB
MAX_BLOCK_SIZE = 2 * 1024 * 1024    # 2MB
MAX_TX_SIZE = 100 * 1024            # 100KB
BLOCK_REWARD = 50_000_000_00        # 50 BTC in Satoshis
MAX_TARGET = 0x0000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
COINBASE_MATURITY = 100             # Maturity lock for coinbase outputs
MAX_PEERS = 32                      # Connection throttling protection boundary

# Hardening Limits
MAX_INPUT_COUNT = 1000              # (Fix 8)
MAX_OUTPUT_COUNT = 1000             # (Fix 8)
MAX_TX_COUNT_PER_BLOCK = 10000      # (Fix 33)
MAX_BLOCK_TX_SIZE_LIMIT = 5000      # (Fix 9)
MAX_ORPHANS = 1000                  # (Fix 18)
MAX_MEMPOOL_SIZE = 50000            # (Fix 21)
MAX_MERKLE_TREE_ELEMENTS = 100000   # (Fix 26)
MAX_FUTURE_BLOCK_TIME = 7200        # 2 Hours (Fix 3, 14)
MAX_MONEY = 21_000_000 * 100_000_000 # (Fix 37)
PEER_DISCOVERY_LIMIT = 100          # (Fix 41)
SOCKET_SEND_TIMEOUT = 5.0           # (Fix 43)
NETWORK_READ_TIMEOUT = 30.0         # (Fix 19)

BLOCK_HEADER_FMT = "!I32s32sdIII"
BLOCK_HEADER_SIZE = struct.calcsize(BLOCK_HEADER_FMT)

logger = logging.getLogger(__name__)

# --- CRYPTOGRAPHIC ENGINE ---
class CryptoEngine:
    @staticmethod
    def dsha256(data: bytes) -> bytes:
        """Executes double SHA-256 for proof-of-work and identification integrity."""
        return hashlib.sha256(hashlib.sha256(data).digest()).digest()

    @staticmethod
    def verify_ecdsa(public_key_hex: str, message: bytes, signature_hex: str) -> bool:
        """Validates SECP256K1 signatures with compressed public key enforcement."""
        try:
            # Fix 20: Validate compressed public key formats
            if len(public_key_hex) != 66:
                logger.debug("Public key verification failed: Invalid hex length.")
                return False
            if public_key_hex[:2] not in ("02", "03"):
                logger.debug("Public key verification failed: Non-compressed prefix.")
                return False

            pub_bytes = bytes.fromhex(public_key_hex)
            public_key = ec.EllipticCurvePublicKey.from_encoded_point(ec.SECP256K1(), pub_bytes)
            sig_bytes = bytes.fromhex(signature_hex)
            public_key.verify(sig_bytes, message, ec.ECDSA(hashes.SHA256()))
            return True
        except Exception:
            return False

    @staticmethod
    def bits_to_target(bits: int) -> int:
        """Converts compact difficulty bits representation to a 256-bit target integer."""
        exponent = (bits >> 24) & 0xFF
        mantissa = bits & 0x00FFFFFF
        if exponent <= 3:
            return mantissa >> (8 * (3 - exponent))
        return mantissa << (8 * (exponent - 3))

    @staticmethod
    def target_to_bits(target: int) -> int:
        """Converts a 256-bit target integer to compact difficulty bits format."""
        if target == 0:
            return 0
        size = (target.bit_length() + 7) // 8
        if size <= 3:
            mantissa = target << (8 * (3 - size))
            exponent = 3
        else:
            mantissa = target >> (8 * (size - 3))
            exponent = size
        if mantissa & 0x00800000:
            mantissa >>= 8
            exponent += 1
        return (exponent << 24) | (mantissa & 0x00FFFFFF)

    @staticmethod
    def bits_to_work(bits: int) -> int:
        """Translates compact target complexity parameter directly into a cumulative work allocation integer."""
        target = CryptoEngine.bits_to_target(bits)
        if target <= 0:
            return 0
        return (1 << 256) // (target + 1)

# --- WIRE FORMAT SERIALIZATION ENGINE ---
class CanonicalWireSerializer:
    TX_HEADER_FORMAT = "!33sQQII"
    TX_HEADER_SIZE = struct.calcsize(TX_HEADER_FORMAT)
    INPUT_SIZE = 36          
    OUTPUT_SIZE = 41         

    @staticmethod
    def serialize_tx(sender_hex: str, inputs: list, outputs: list, nonce: int, timestamp: int, signature_hex: str | None = None) -> bytes:
        sender_bytes = bytes.fromhex(sender_hex)
        # Fix 28: Verify sender public key format on serialization
        if len(sender_bytes) != 33:
            raise ValueError("Invalid public key length.")
        if sender_bytes[0] not in (2, 3) and sender_hex != "0" * 66:
            raise ValueError("Invalid compressed public key prefix.")

        header = struct.pack(
            CanonicalWireSerializer.TX_HEADER_FORMAT,
            sender_bytes, nonce, int(timestamp), len(inputs), len(outputs)
        )
        body = bytearray()
        for vin in inputs:
            txid, index = vin.split(":")
            body.extend(bytes.fromhex(txid))
            body.extend(struct.pack("!I", int(index)))
        for vout in outputs:
            # Fix 52: Reject empty addresses
            if not vout["address"]:
                raise ValueError("Empty address.")
            # Fix 35: Reject oversized or malformed output addresses
            if len(bytes.fromhex(vout["address"])) != 33:
                raise ValueError("Invalid address.")
            body.extend(bytes.fromhex(vout["address"]))
            body.extend(struct.pack("!Q", int(vout["amount"])))
        if signature_hex:
            sig = bytes.fromhex(signature_hex)
            body.extend(struct.pack("!B", len(sig)))
            body.extend(sig)
        else:
            body.extend(b"\x00")
        return header + bytes(body)

    @staticmethod
    def parse_tx(raw: bytes, offset: int = 0):
        start = offset
        if len(raw) - offset < CanonicalWireSerializer.TX_HEADER_SIZE:
            raise ValueError("Incomplete transaction header.")
        
        (sender, nonce, timestamp, input_count, output_count) = struct.unpack(
            CanonicalWireSerializer.TX_HEADER_FORMAT, raw[offset:offset + CanonicalWireSerializer.TX_HEADER_SIZE]
        )
        
        # Fix 28: Verify sender public key formatting elements during deserialization
        if sender.hex() != "0" * 66:
            if len(sender) != 33:
                raise ValueError("Invalid public key length.")
            if sender[0] not in (2, 3):
                raise ValueError("Invalid compressed public key.")

        # Fix 8: Enforce tight operational input/output boundary rules
        if input_count > MAX_INPUT_COUNT:
            raise ValueError("Too many inputs.")
        if output_count > MAX_OUTPUT_COUNT:
            raise ValueError("Too many outputs.")

        offset += CanonicalWireSerializer.TX_HEADER_SIZE

        min_expected_size = (input_count * CanonicalWireSerializer.INPUT_SIZE) + (output_count * CanonicalWireSerializer.OUTPUT_SIZE) + 1
        if min_expected_size > MAX_TX_SIZE:
            raise ValueError("Transaction parameters break size boundaries.")

        inputs = []
        for _ in range(input_count):
            if len(raw) - offset < CanonicalWireSerializer.INPUT_SIZE:
                raise ValueError("Incomplete transaction input stream.")
            txid = raw[offset:offset + 32].hex()
            index = struct.unpack("!I", raw[offset + 32:offset + 36])[0]
            inputs.append(f"{txid}:{index}")
            offset += CanonicalWireSerializer.INPUT_SIZE

        outputs = []
        for _ in range(output_count):
            if len(raw) - offset < CanonicalWireSerializer.OUTPUT_SIZE:
                raise ValueError("Incomplete transaction output stream.")
            address = raw[offset:offset + 33].hex()
            amount = struct.unpack("!Q", raw[offset + 33:offset + 41])[0]
            outputs.append({"address": address, "amount": amount})
            offset += CanonicalWireSerializer.OUTPUT_SIZE

        if len(raw) - offset < 1:
            raise ValueError("Missing signature length field.")
        sig_len = raw[offset]
        offset += 1

        # Fix 29: Reject invalid signature sizes
        if sig_len > 80:
            raise ValueError("Signature too large.")
        if sig_len != 0 and sig_len < 8:
            raise ValueError("Signature too small.")

        if len(raw) - offset < sig_len:
            raise ValueError("Incomplete cryptography signature block.")
        signature = raw[offset:offset + sig_len].hex()
        offset += sig_len

        if offset - start > MAX_TX_SIZE:
            raise ValueError("Transaction structure violates MAX_TX_SIZE.")

        txid = CanonicalWireSerializer.compute_tx_id(sender.hex(), inputs, outputs, nonce, timestamp)
        return (txid, sender.hex(), nonce, timestamp, inputs, outputs, signature, offset)

    @staticmethod
    def compute_tx_id(sender_hex: str, inputs: list, outputs: list, nonce: int, timestamp: int) -> str:
        payload = CanonicalWireSerializer.serialize_tx(sender_hex, inputs, outputs, nonce, timestamp, None)
        return CryptoEngine.dsha256(payload).hex()

class MerkleTree:
    @staticmethod
    def compute_root(tx_ids: list[str]) -> str:
        if not tx_ids:
            return CryptoEngine.dsha256(b"").hex()
        layer = [bytes.fromhex(txid) for txid in tx_ids]
        while len(layer) > 1:
            if len(layer) & 1:
                layer.append(layer[-1])
            next_layer = []
            for i in range(0, len(layer), 2):
                next_layer.append(CryptoEngine.dsha256(layer[i] + layer[i + 1]))
            layer = next_layer
        return layer[0].hex()

# --- RELIABLE PERSISTENT DATABASE ENGINE ---
class NakamotoLedgerEngine:
    def __init__(self, port: int):
        self.db_name = f"blockchain_{port}.db"
        self._lock = threading.Lock()
        self.orphan_blocks = {}  # Map prev_hash -> list of raw_block bytes
        self.orphan_hashes = set() # Fix 48: Avoid storing distinct bytes of same block
        self._bootstrap_db()

    def _get_conn(self) -> sqlite3.Connection:
        conn = sqlite3.connect(self.db_name, timeout=15.0, isolation_level=None)
        conn.row_factory = sqlite3.Row
        return conn

    def _bootstrap_db(self):
        with self._get_conn() as conn:
            # Fix 49: Run database integrity diagnostics check on startup
            result = conn.execute("PRAGMA integrity_check;").fetchone()
            if result[0] != "ok":
                raise RuntimeError("Database corruption detected via PRAGMA.")

            conn.execute("PRAGMA foreign_keys = ON;")
            conn.execute("BEGIN IMMEDIATE")
            try:
                conn.execute("""
                    CREATE TABLE IF NOT EXISTS blocks (
                        block_hash TEXT PRIMARY KEY, height INTEGER NOT NULL, prev_hash TEXT,
                        merkle_root TEXT NOT NULL, timestamp REAL NOT NULL, bits INTEGER NOT NULL,
                        nonce INTEGER NOT NULL, chain_work TEXT NOT NULL, raw_bytes BLOB NOT NULL
                    );
                """)
                try:
                    conn.execute("ALTER TABLE blocks ADD COLUMN chain_work TEXT NOT NULL DEFAULT '0';")
                except sqlite3.OperationalError:
                    pass  # Column already exists
                
                conn.execute("CREATE INDEX IF NOT EXISTS idx_height ON blocks(height);")
                conn.execute("""
                    CREATE TABLE IF NOT EXISTS utxos (
                        utxo_key TEXT PRIMARY KEY, owner TEXT NOT NULL, amount INTEGER NOT NULL,
                        is_coinbase INTEGER NOT NULL, height_created INTEGER NOT NULL,
                        height_spent INTEGER
                    );
                """)
                conn.execute("CREATE TABLE IF NOT EXISTS nonces (address TEXT PRIMARY KEY, next_nonce INTEGER NOT NULL);")
                conn.execute("CREATE TABLE IF NOT EXISTS metadata (key TEXT PRIMARY KEY, value TEXT NOT NULL);")
                
                # Fix 54: Eliminate lingering open cursors via inline immediate evaluation
                cursor_count = conn.execute("SELECT COUNT(*) FROM blocks").fetchone()
                if cursor_count[0] == 0:
                    cb = CanonicalWireSerializer.serialize_tx("0" * 66, [], [{"address": "0" * 66, "amount": BLOCK_REWARD}], 0, 1700000000)
                    cb_id, _, _, _, _, _, _, _ = CanonicalWireSerializer.parse_tx(cb)
                    m_root = MerkleTree.compute_root([cb_id])
                    header = struct.pack(BLOCK_HEADER_FMT, 0, b"\x00"*32, bytes.fromhex(m_root), 1700000000.0, 0x1f00ffff, 0, 1)
                    raw_genesis = header + cb
                    g_hash = CryptoEngine.dsha256(header).hex()
                    g_work = f"{CryptoEngine.bits_to_work(0x1f00ffff):064x}"
                    
                    conn.execute("INSERT INTO blocks VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)", (g_hash, 0, None, m_root, 1700000000.0, 0x1f00ffff, 0, g_work, raw_genesis))
                    conn.execute("INSERT INTO utxos VALUES (?, ?, ?, ?, ?, NULL)", (f"{cb_id}:0", "0"*66, BLOCK_REWARD, 1, 0))
                    conn.execute("INSERT INTO metadata VALUES ('main_tip', ?)", (g_hash,))
                conn.commit()
            except Exception:
                conn.rollback()
                raise

    def get_main_tip(self) -> dict | None:
        conn = self._get_conn()
        try:
            tip_row = conn.execute("SELECT value FROM metadata WHERE key = 'main_tip'").fetchone()
            if not tip_row:
                return None
            row = conn.execute("SELECT block_hash, height, bits, chain_work FROM blocks WHERE block_hash = ?", (tip_row["value"],)).fetchone()
            return {"block_hash": row["block_hash"], "index": row["height"], "bits": row["bits"], "chain_work": int(row["chain_work"], 16)} if row else None
        finally:
            conn.close()

    def _get_next_work_required(self, conn, last_block_row) -> int:
        height = last_block_row["height"]
        if height == 0 or (height + 1) % 10 != 0:
            return last_block_row["bits"]
        
        first_height = height - 9
        row = conn.execute("SELECT timestamp FROM blocks WHERE height = ?", (first_height,)).fetchone()
        if not row:
            return last_block_row["bits"]
        
        actual_timespan = last_block_row["timestamp"] - row["timestamp"]
        target_timespan = 10 * 10
        
        if actual_timespan < target_timespan // 4:
            actual_timespan = target_timespan // 4
        if actual_timespan > target_timespan * 4:
            actual_timespan = target_timespan * 4
            
        current_target = CryptoEngine.bits_to_target(last_block_row["bits"])
        new_target = (current_target * actual_timespan) // target_timespan
        if new_target > MAX_TARGET:
            new_target = MAX_TARGET
            
        return CryptoEngine.target_to_bits(new_target)

    def _find_common_ancestor(self, conn, hash_a, hash_b) -> str | None:
        ancestors_a = set()
        curr = hash_a
        while curr:
            ancestors_a.add(curr)
            row = conn.execute("SELECT prev_hash FROM blocks WHERE block_hash = ?", (curr,)).fetchone()
            curr = row["prev_hash"] if row else None
        
        curr = hash_b
        while curr:
            if curr in ancestors_a:
                return curr
            row = conn.execute("SELECT prev_hash FROM blocks WHERE block_hash = ?", (curr,)).fetchone()
            curr = row["prev_hash"] if row else None
        return None

    def _get_chain_branch(self, conn, tip_hash, ancestor_hash) -> list:
        path = []
        curr = tip_hash
        while curr and curr != ancestor_hash:
            row = conn.execute("SELECT prev_hash, raw_bytes FROM blocks WHERE block_hash = ?", (curr,)).fetchone()
            if not row:
                break
            path.append((curr, row["raw_bytes"]))
            curr = row["prev_hash"]
        return path

    def _disconnect_block(self, conn, block_hash, raw_block):
        (height, _, _, _, _, _, tx_count) = struct.unpack(BLOCK_HEADER_FMT, raw_block[:BLOCK_HEADER_SIZE])
        offset = BLOCK_HEADER_SIZE
        for tx_idx in range(tx_count):
            tx_data = CanonicalWireSerializer.parse_tx(raw_block, offset)
            _, sender, _, _, vins, _, _, next_offset = tx_data
            offset = next_offset
            if tx_idx > 0:
                conn.execute("UPDATE nonces SET next_nonce = MAX(0, next_nonce - 1) WHERE address = ?", (sender,))
        conn.execute("DELETE FROM utxos WHERE height_created = ?", (height,))
        conn.execute("UPDATE utxos SET height_spent = NULL WHERE height_spent = ?", (height,))

    def _connect_block(self, conn, block_hash, raw_block, height):
        (_, _, merkle_root_bytes, block_timestamp, _, _, tx_count) = struct.unpack(BLOCK_HEADER_FMT, raw_block[:BLOCK_HEADER_SIZE])
        offset = BLOCK_HEADER_SIZE
        local_block_created = {}
        local_block_spent = set()
        local_nonce_increments = {}
        parsed_tx_ids = []
        
        total_block_fees = 0
        coinbase_output_total = 0
        parsed_count = 0  # Fix 55

        for tx_idx in range(tx_count):
            # Fix 40: Verify transaction parser explicitly made forward progress
            old_offset = offset
            tx_data = CanonicalWireSerializer.parse_tx(raw_block, offset)
            tx_id, sender, tx_nonce, ts, vins, vouts, sig, next_offset = tx_data
            offset = next_offset
            parsed_count += 1

            if next_offset <= old_offset:
                raise RuntimeError("Parser made no progress.")

            # Fix 11: Reject duplicate transaction IDs inside the block
            if tx_id in parsed_tx_ids:
                raise RuntimeError("Duplicate transaction ID inside block.")
            parsed_tx_ids.append(tx_id)

            # Fix 14: Check transaction timestamp boundaries against block header bounds
            if ts > block_timestamp + MAX_FUTURE_BLOCK_TIME:
                raise RuntimeError("Transaction timestamp too far ahead.")

            if tx_idx == 0:
                # Fix 15: Validate coinbase transaction satisfies structured properties
                if len(vins) != 0 or sender != "0" * 66 or not vouts:
                    raise RuntimeError("Malformed coinbase transaction structure.")
                
                # Fix 37: Enforce output overflow protection on coinbase outputs
                coinbase_output_total = 0
                for out in vouts:
                    if out["amount"] < 0:
                        raise RuntimeError("Negative output.")
                    coinbase_output_total += out["amount"]
                    if coinbase_output_total > MAX_MONEY:
                        raise RuntimeError("Money overflow.")
                
                # Fix 51: Validate the coinbase reward is non-negative
                if coinbase_output_total < 0:
                    raise RuntimeError("Negative coinbase reward.")
            else:
                # Fix 15: Confirm secondary coinbase occurrences are rejected
                if sender == "0" * 66:
                    raise RuntimeError("Coinbase transaction not first.")
                if len(vins) == 0:
                    raise RuntimeError("Standard transaction missing inputs.")
                
                unsigned_payload = CanonicalWireSerializer.serialize_tx(sender, vins, vouts, tx_nonce, ts, None)
                if not CryptoEngine.verify_ecdsa(sender, unsigned_payload, sig):
                    raise RuntimeError(f"Cryptographic signature check failed inside block parsing for tx: {tx_id}")

                current_nonce = 0
                row = conn.execute("SELECT next_nonce FROM nonces WHERE address = ?", (sender,)).fetchone()
                if row:
                    current_nonce = row["next_nonce"]
                expected_nonce = current_nonce + local_nonce_increments.get(sender, 0)
                if tx_nonce != expected_nonce:
                    raise RuntimeError("Invalid transaction nonce processing sequence.")
                local_nonce_increments[sender] = local_nonce_increments.get(sender, 0) + 1

                # Fix 37: Enforce explicit monetary sum bounds on transaction outputs
                tx_output_total = 0
                for out in vouts:
                    # Fix 25: Reject negative or zero-value outputs
                    if out["amount"] <= 0:
                        raise RuntimeError("Invalid output amount.")
                    tx_output_total += out["amount"]
                    if tx_output_total > MAX_MONEY:
                        raise RuntimeError("Money overflow.")

                # Fix 27: Reject duplicate inputs inside one transaction
                seen_tx_inputs = set()

                tx_input_total = 0
                for vin in vins:
                    if vin in seen_tx_inputs:
                        raise RuntimeError("Duplicate input.")
                    seen_tx_inputs.add(vin)

                    if vin in local_block_spent:
                        raise RuntimeError("Intra-block double spend detected.")
                    local_block_spent.add(vin)
                    
                    if vin in local_block_created:
                        tx_input_total += local_block_created[vin]["amount"]
                        is_cb = local_block_created[vin]["is_coinbase"]
                        h_created = height
                    else:
                        utxo_row = conn.execute("SELECT amount, is_coinbase, height_created FROM utxos WHERE utxo_key = ? AND height_spent IS NULL", (vin,)).fetchone()
                        if not utxo_row:
                            raise RuntimeError("Input UTXO unavailable or spent context.")
                        
                        # Fix 12: Verify explicit transaction public key ownership explicitly
                        owner_row = conn.execute("SELECT owner FROM utxos WHERE utxo_key=?", (vin,)).fetchone()
                        if owner_row is None:
                            raise RuntimeError("Missing owner.")
                        if owner_row["owner"] != sender:
                            raise RuntimeError("Sender does not own input.")

                        tx_input_total += utxo_row["amount"]
                        is_cb = utxo_row["is_coinbase"]
                        h_created = utxo_row["height_created"]
                        
                    if is_cb == 1 and (height - h_created) < COINBASE_MATURITY:
                        raise RuntimeError(f"Coinbase reward output {vin} spent before required maturity horizon.")

                if tx_input_total < tx_output_total:
                    raise RuntimeError("Transaction outputs value exceeds available input limits.")
                total_block_fees += (tx_input_total - tx_output_total)

            for idx, out in enumerate(vouts):
                utxo_key = f"{tx_id}:{idx}"
                if utxo_key in local_block_created:
                    raise RuntimeError("Duplicate UTXO context generated.")
                
                # Fix 24 & Fix 45: Reject duplicate UTXO insertions or duplicate coinbase outputs
                utxo_exists = conn.execute("SELECT 1 FROM utxos WHERE utxo_key=?", (utxo_key,)).fetchone()
                if utxo_exists:
                    raise RuntimeError("Duplicate UTXO.")

                local_block_created[utxo_key] = {"owner": out["address"], "amount": out["amount"], "is_coinbase": 1 if tx_idx == 0 else 0}

        # Fix 55: Validate total iteration parsed count matches total encoded context
        if parsed_count != tx_count:
            raise RuntimeError("Transaction count mismatch.")

        # Fix 34: Verify block size structure left no bytes hanging trailing the message
        if offset != len(raw_block):
            raise RuntimeError("Extra bytes after block.")

        if coinbase_output_total > BLOCK_REWARD + total_block_fees:
            raise RuntimeError(f"Coinbase total output {coinbase_output_total} exceeds allowed limits: {BLOCK_REWARD + total_block_fees}")

        # Fix 13: Checked prior to database storage
        for spent_key in local_block_spent:
            conn.execute("UPDATE utxos SET height_spent = ? WHERE utxo_key = ?", (height, spent_key))
            
        for key, obj in local_block_created.items():
            conn.execute("INSERT INTO utxos VALUES (?, ?, ?, ?, ?, NULL)", (key, obj["owner"], obj["amount"], obj["is_coinbase"], height))
        for addr, inc in local_nonce_increments.items():
            conn.execute("INSERT INTO nonces VALUES (?, ?) ON CONFLICT(address) DO UPDATE SET next_nonce = next_nonce + ?", (addr, inc, inc))

    def process_incoming_block(self, raw_block: bytes) -> bool:
        # Fix 38: Verify structural block size bounds explicitly before executing un-boxing
        if len(raw_block) < BLOCK_HEADER_SIZE:
            return False
        if len(raw_block) > MAX_BLOCK_SIZE:
            return False
        
        b_hash = CryptoEngine.dsha256(raw_block[:BLOCK_HEADER_SIZE]).hex()
        
        # Fix 39: Move duplicate block check early to avoid expensive processing overheads
        with self._lock:
            conn = self._get_conn()
            try:
                if conn.execute("SELECT 1 FROM blocks WHERE block_hash = ?", (b_hash,)).fetchone():
                    conn.close()
                    return False
            finally:
                conn.close()

        try:
            (height, prev_hash_bytes, merkle_root_bytes, timestamp, bits, nonce, tx_count) = \
                struct.unpack(BLOCK_HEADER_FMT, raw_block[:BLOCK_HEADER_SIZE])
            prev_hash = prev_hash_bytes.hex()
            
            # Fix 17: Verify explicit hexadecimal mapping bounds for previous hash values
            if len(prev_hash) != 64:
                return False

            # Fix 3: Reject blocks presenting dynamic future dates
            if timestamp > time.time() + MAX_FUTURE_BLOCK_TIME:
                # Fix 60: Improve contextual diagnostics logging metrics output
                logger.warning("Rejected block %s with future timestamp: %f", b_hash, timestamp)
                return False

            # Fix 16: Check empty transaction payloads
            if tx_count == 0:
                return False

            # Fix 9 & Fix 33: Boundary throttling limits on block transaction volume mapping
            if tx_count > MAX_BLOCK_TX_SIZE_LIMIT or tx_count > MAX_TX_COUNT_PER_BLOCK:
                return False

            if int.from_bytes(CryptoEngine.dsha256(raw_block[:BLOCK_HEADER_SIZE]), byteorder='big') >= CryptoEngine.bits_to_target(bits):
                return False

            # Fix 46: Validate Merkle root format length representation boundaries
            if len(merkle_root_bytes.hex()) != 64:
                return False

            # Fix 13: Extract, decode and match Merkle tree rules before performing block insert
            try:
                offset_scan = BLOCK_HEADER_SIZE
                scanned_txids = []
                for _ in range(tx_count):
                    tx_data = CanonicalWireSerializer.parse_tx(raw_block, offset_scan)
                    tx_id, _, _, _, _, _, _, next_offset = tx_data
                    scanned_txids.append(tx_id)
                    offset_scan = next_offset
                
                # Fix 26: Reject oversized Merkle Tree structures
                if len(scanned_txids) > MAX_MERKLE_TREE_ELEMENTS:
                    return False

                if MerkleTree.compute_root(scanned_txids) != merkle_root_bytes.hex():
                    return False
            except Exception:
                return False

            with self._lock:
                conn = self._get_conn()
                try:
                    conn.execute("BEGIN IMMEDIATE")
                    if conn.execute("SELECT 1 FROM blocks WHERE block_hash = ?", (b_hash,)).fetchone():
                        conn.rollback()
                        return False
                    
                    if prev_hash == "0"*64:
                        parent_height = -1
                        expected_bits = 0x1f00ffff
                        parent_work = 0
                    else:
                        parent_row = conn.execute("SELECT height, bits, timestamp, chain_work FROM blocks WHERE block_hash = ?", (prev_hash,)).fetchone()
                        
                        if not parent_row:
                            # Fix 18: Restrict orphan list expansion properties under resource limits
                            if sum(len(v) for v in self.orphan_blocks.values()) >= MAX_ORPHANS:
                                logger.warning("Orphan pool full.")
                                conn.rollback()
                                return False
                            
                            if prev_hash not in self.orphan_blocks:
                                self.orphan_blocks[prev_hash] = []
                            
                            # Fix 48: Double check structural block equivalence using calculated hashes
                            if b_hash not in self.orphan_hashes:
                                self.orphan_blocks[prev_hash].append(raw_block)
                                self.orphan_hashes.add(b_hash)
                            
                            conn.rollback()
                            logger.info("Stored block %s as orphan due to missing parent %s", b_hash, prev_hash)
                            return False
                        
                        # Fix 23: Validate block timestamp is strictly progressive against its parent's time mark
                        if timestamp <= parent_row["timestamp"]:
                            conn.rollback()
                            logger.warning("Block timestamp not greater than parent: %f <= %f", timestamp, parent_row["timestamp"])
                            return False

                        parent_height = parent_row["height"]
                        expected_bits = self._get_next_work_required(conn, parent_row)
                        parent_work = int(parent_row["chain_work"], 16)
                    
                    computed_height = parent_height + 1
                    
                    # Fix 10: Enforce logical height verification against sequential branch rules
                    if height != computed_height:
                        conn.rollback()
                        logger.warning("Invalid block height. Expected %d got %d", computed_height, height)
                        return False

                    if bits != expected_bits:
                        conn.rollback()
                        return False

                    current_block_work = CryptoEngine.bits_to_work(bits)
                    total_cumulative_work = parent_work + current_block_work
                    work_hex = f"{total_cumulative_work:064x}"

                    conn.execute("INSERT INTO blocks VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)", 
                                 (b_hash, computed_height, prev_hash if computed_height > 0 else None, 
                                  merkle_root_bytes.hex(), timestamp, bits, nonce, work_hex, raw_block))
                    
                    tip_row = conn.execute("SELECT value FROM metadata WHERE key = 'main_tip'").fetchone()
                    current_tip_hash = tip_row["value"] if tip_row else None
                    current_tip_work = 0
                    if current_tip_hash:
                        ct_row = conn.execute("SELECT chain_work FROM blocks WHERE block_hash = ?", (current_tip_hash,)).fetchone()
                        current_tip_work = int(ct_row["chain_work"], 16)
                    
                    if total_cumulative_work > current_tip_work:
                        common_ancestor = self._find_common_ancestor(conn, current_tip_hash, b_hash)
                        disconnect_path = self._get_chain_branch(conn, current_tip_hash, common_ancestor)
                        connect_path = self._get_chain_branch(conn, b_hash, common_ancestor)
                        connect_path.reverse()
                        
                        for _, rb_bytes in disconnect_path:
                            self._disconnect_block(conn, current_tip_hash, rb_bytes)
                        try:
                            for h, conn_bytes in connect_path:
                                b_row = conn.execute("SELECT height FROM blocks WHERE block_hash = ?", (h,)).fetchone()
                                self._connect_block(conn, h, conn_bytes, b_row["height"])
                            conn.execute("INSERT OR REPLACE INTO metadata VALUES ('main_tip', ?)", (b_hash,))
                            conn.commit()
                            logger.info("Successfully integrated block %s at height %d (Main Tip updated via work evaluation)", b_hash, computed_height)
                            
                            # Evict from tracking context once bound to main repository chain structures
                            if b_hash in self.orphan_hashes:
                                self.orphan_hashes.remove(b_hash)

                            threading.Thread(target=self._unwind_orphans, args=(b_hash,), daemon=True).start()
                            return True
                        except Exception as e:
                            conn.rollback()
                            logger.error("Fork validation failed, discarding branch: %s", e)
                            return False
                    else:
                        conn.commit()
                        logger.info("Stored valid sidechain block %s at height %d (Lower work profile)", b_hash, computed_height)
                        return True
                # Fix 56: Narrow database handling errors distinctly from general script execution issues
                except sqlite3.Error as se:
                    logger.error("Database layer processing error: %s", se)
                    return False
                finally:
                    conn.close()
        except Exception:
            logger.exception("Sandbox verification failure for block %s", b_hash)
            return False

    def _unwind_orphans(self, parent_hash: str):
        with self._lock:
            candidates = self.orphan_blocks.pop(parent_hash, [])
        for orphan_bytes in candidates:
            self.process_incoming_block(orphan_bytes)

    def get_utxo_state(self, utxo_key: str) -> dict | None:
        with self._lock:
            conn = self._get_conn()
            try:
                row = conn.execute("SELECT owner, amount FROM utxos WHERE utxo_key = ? AND height_spent IS NULL", (utxo_key,)).fetchone()
                return {"owner": row["owner"], "amount": row["amount"]} if row else None
            finally:
                conn.close()

    def get_account_nonce(self, address: str) -> int:
        with self._lock:
            conn = self._get_conn()
            try:
                row = conn.execute("SELECT next_nonce FROM nonces WHERE address = ?", (address,)).fetchone()
                return row["next_nonce"] if row else 0
            finally:
                conn.close()

# --- MEMORY POOL MANAGER ---
class MemoryPoolManager:
    def __init__(self, ledger: NakamotoLedgerEngine):
        self.ledger = ledger
        self.pool = {}
        self.spent_outpoints = set()
        self._lock = threading.Lock()
        # Fix 21: Declare explicit ceiling limitations to preserve node memory state
        self.max_pool_size = MAX_MEMPOOL_SIZE

    def add_transaction(self, tx_bytes: bytes) -> bool:
        if len(tx_bytes) > MAX_TX_SIZE:
            # Fix 47: Incorporate explicit contextual rejection trace diagnostics logs
            logger.warning("Rejected tx insertion: Sizes surpass limit boundaries.")
            return False
        try:
            (tx_id, sender, nonce, tx_time, vins, vouts, sig_hex, _) = CanonicalWireSerializer.parse_tx(tx_bytes)
            unsigned = CanonicalWireSerializer.serialize_tx(sender, vins, vouts, nonce, tx_time, None)
            if not CryptoEngine.verify_ecdsa(sender, unsigned, sig_hex):
                logger.warning("Rejected tx %s: Cryptographic verification fault.", tx_id)
                return False

            output_total = sum(output["amount"] for output in vouts)
            tx_len = max(len(tx_bytes), 1)

            with self._lock:
                # Fix 21: Ensure transactional volume ceilings stay constrained
                if len(self.pool) >= self.max_pool_size:
                    logger.warning("Rejected tx %s: Node memory pool constraints filled.", tx_id)
                    return False

                if tx_id in self.pool or not self.spent_outpoints.isdisjoint(vins):
                    logger.warning("Rejected tx %s: Double spend or duplicate mempool event.", tx_id)
                    return False

                input_total = 0
                for vin in vins:
                    utxo = self.ledger.get_utxo_state(vin)
                    if utxo is None or utxo["owner"] != sender:
                        logger.warning("Rejected tx %s: Missing input or identity mismatch.", tx_id)
                        return False
                    input_total += utxo["amount"]

                if input_total < output_total:
                    logger.warning("Rejected tx %s: Input total %d < Output total %d", tx_id, input_total, output_total)
                    return False

                if nonce != self.ledger.get_account_nonce(sender):
                    logger.warning("Rejected tx %s: Nonce mismatch state context.", tx_id)
                    return False

                fee = input_total - output_total
                self.pool[tx_id] = {
                    "bytes": tx_bytes, "fee": fee, "time": tx_time,
                    "inputs": list(vins), "feerate": fee / tx_len
                }
                self.spent_outpoints.update(vins)
                logger.info("Mempool tracked transaction: %s", tx_id)
                return True
        except Exception:
            return False

    def get_batch(self, limit: int = 50) -> list[bytes]:
        with self._lock:
            ordered = sorted(self.pool.values(), key=lambda tx: (-tx["feerate"], tx["time"]))
            return [tx["bytes"] for tx in ordered[:limit]]

    def remove_mined_transactions(self, tx_ids: list[str]) -> None:
        with self._lock:
            for tx_id in tx_ids:
                tx = self.pool.pop(tx_id, None)
                if tx:
                    self.spent_outpoints.difference_update(tx["inputs"])

# --- ASYNCHRONOUS P2P NETWORKING LAYER ---
class P2PPeerNode:
    def __init__(self, listen_port: int, ledger: NakamotoLedgerEngine, mempool: MemoryPoolManager):
        self.host = "127.0.0.1"
        self.port = listen_port
        self.ledger = ledger
        self.mempool = mempool
        self.running = False
        self._lock = threading.Lock()
        self.peers: set[socket.socket] = set()
        self.known_peers = {f"127.0.0.1:{listen_port}"}
        # Fix 22: Mitigate broadcast loop storm sequences across nodes
        self.recent_broadcasts = set()
        self.listener_sock = None

    def start(self):
        self.running = True
        self.listener_sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.listener_sock.setsockopt(socket.SOL_SOCKET, socket.SO_KEEPALIVE, 1)
        self.listener_sock.bind((self.host, self.port))
        self.listener_sock.listen(10)
        self.listener_sock.settimeout(1.0)
        threading.Thread(target=self._listen, daemon=True).start()

    def _frame_message(self, msg_type: str, payload: dict) -> bytes:
        serialized_msg = json.dumps({"type": msg_type, "payload": payload}).encode('utf-8')
        return MAGIC_BYTES + msg_type.encode('utf-8').ljust(12, b'\x00') + struct.pack("!I", len(serialized_msg)) + serialized_msg

    # Fix 4: Enforce rigid stream-length slicing logic to eliminate partial chunk reads
    def recv_exact(self, sock: socket.socket, size: int) -> bytes | None:
        """Reads exactly the requested size bytes from standard socket streams securely."""
        data = bytearray()
        while len(data) < size:
            # Fix 59: Evaluate thread lifecycle status properties during iteration
            if not self.running:
                return None
            try:
                packet = sock.recv(size - len(data))
                if not packet:
                    return None
                data.extend(packet)
            except Exception:
                return None
        return bytes(data)

    def _listen(self):
        while self.running:
            try:
                sock, _ = self.listener_sock.accept()
                # Fix 19: Apply read/write operation duration caps to clean idle hangs
                sock.settimeout(NETWORK_READ_TIMEOUT)
                sock.setsockopt(socket.SOL_SOCKET, socket.SO_KEEPALIVE, 1)
                with self._lock:
                    if len(self.peers) >= MAX_PEERS:
                        sock.close()
                        continue
                    
                    # Fix 6: Drop inbound redundant socket allocations matching verified targets
                    try:
                        peer_name = f"{sock.getpeername()[0]}:{sock.getpeername()[1]}"
                        if peer_name in self.known_peers:
                            sock.close()
                            continue
                        self.known_peers.add(peer_name)
                    except Exception:
                        sock.close()
                        continue

                    # Fix 53: Inspect the pool structures to protect duplicate descriptors
                    if sock in self.peers:
                        sock.close()
                        continue

                    self.peers.add(sock)
                threading.Thread(target=self._peer_handler, args=(sock,), daemon=True).start()
                
                # Fix 43: Set transient operational constraints when applying writes
                sock.settimeout(SOCKET_SEND_TIMEOUT)
                sock.sendall(self._frame_message("getpeers", {}))
                sock.settimeout(NETWORK_READ_TIMEOUT)
            except socket.timeout:
                continue
            except Exception:
                break

    def connect(self, target_port: int) -> bool:
        # Fix 5: Reject loopback connection matching localized target parameters
        if target_port == self.port:
            return False

        peer_str = f"127.0.0.1:{target_port}"
        with self._lock:
            if len(self.peers) >= MAX_PEERS:
                return False
            self.known_peers.add(peer_str)

        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_KEEPALIVE, 1)
        try:
            sock.settimeout(SOCKET_SEND_TIMEOUT)
            sock.connect((self.host, target_port))
            
            with self._lock:
                if len(self.peers) >= MAX_PEERS or sock in self.peers:
                    sock.close()
                    return False
                self.peers.add(sock)
            
            threading.Thread(target=self._peer_handler, args=(sock,), daemon=True).start()
            sock.sendall(self._frame_message("getpeers", {}))
            sock.settimeout(NETWORK_READ_TIMEOUT)
            return True
        except Exception as exc:
            logger.warning("Outward connection to peer %d failed: %s", target_port, exc)
            
            # Fix 42: Clear chronically broken endpoints from tracking indexes
            with self._lock:
                if peer_str in self.known_peers:
                    self.known_peers.discard(peer_str)
            sock.close()
            return False

    def _peer_handler(self, sock: socket.socket):
        try:
            while self.running:
                msg = self.recv_framed_msg(sock)
                if msg is None:
                    break
                
                # Fix 32: Confirm parsed command maps to recognized types
                msg_type = msg.get("type")
                if msg_type not in {"tx", "block", "getpeers", "peers"}:
                    continue

                payload = msg.get("payload", {})
                
                if msg_type == "tx":
                    tx_hex_raw = payload.get("data", "")
                    # Fix 22: Verify object hash properties prior to network broadcast execution
                    tx_hash_id = hashlib.sha256(bytes.fromhex(tx_hex_raw)).hexdigest()
                    
                    with self._lock:
                        if tx_hash_id in self.recent_broadcasts:
                            continue
                        self.recent_broadcasts.add(tx_hash_id)
                        if len(self.recent_broadcasts) > 10000:
                            self.recent_broadcasts.pop()

                    tx_bytes = bytes.fromhex(tx_hex_raw)
                    if self.mempool.add_transaction(tx_bytes):
                        self.broadcast("tx", payload, skip_sock=sock)

                elif msg_type == "block":
                    block_hex_raw = payload.get("data", "")
                    block_hash_id = CryptoEngine.dsha256(bytes.fromhex(block_hex_raw[:BLOCK_HEADER_SIZE * 2])).hex()
                    
                    with self._lock:
                        if block_hash_id in self.recent_broadcasts:
                            continue
                        self.recent_broadcasts.add(block_hash_id)

                    block_bytes = bytes.fromhex(block_hex_raw)
                    if self.ledger.process_incoming_block(block_bytes):
                        try:
                            (_, _, _, _, _, _, tx_count) = struct.unpack(BLOCK_HEADER_FMT, block_bytes[:BLOCK_HEADER_SIZE])
                            offset = BLOCK_HEADER_SIZE
                            mined_ids = []
                            for _ in range(tx_count):
                                tx_data = CanonicalWireSerializer.parse_tx(block_bytes, offset)
                                tx_id, _, _, _, _, _, _, next_offset = tx_data
                                mined_ids.append(tx_id)
                                offset = next_offset
                            self.mempool.remove_mined_transactions(mined_ids)
                        except Exception:
                            pass
                        self.broadcast("block", payload, skip_sock=sock)

                elif msg_type == "getpeers":
                    with self._lock:
                        peers_snapshot = list(self.known_peers)
                    sock.settimeout(SOCKET_SEND_TIMEOUT)
                    sock.sendall(self._frame_message("peers", {"list": peers_snapshot}))
                    sock.settimeout(NETWORK_READ_TIMEOUT)

                elif msg_type == "peers":
                    incoming_peers = payload.get("list", [])
                    # Fix 41: Cap raw input parameter lengths on discovered listings
                    if len(incoming_peers) > PEER_DISCOVERY_LIMIT:
                        incoming_peers = incoming_peers[:PEER_DISCOVERY_LIMIT]

                    with self._lock:
                        for p in incoming_peers:
                            if p not in self.known_peers and len(self.peers) < MAX_PEERS:
                                self.known_peers.add(p)
                                try:
                                    host_str, port_str = p.split(":")
                                    threading.Thread(target=self.connect, args=(int(port_str),), daemon=True).start()
                                except Exception:
                                    continue
        except (socket.error, ValueError):
            pass
        finally:
            with self._lock:
                if sock in self.peers:
                    self.peers.remove(sock)
            try:
                sock.close()
            except Exception:
                pass

    def recv_framed_msg(self, sock: socket.socket) -> dict | None:
        """Reads framed payload from stream using exact message length specifications."""
        try:
            # Fix 4: Transition parsing routine execution using exact length slicing limits
            magic = self.recv_exact(sock, 4)
            if magic != MAGIC_BYTES:
                return None
            
            msg_type_raw = self.recv_exact(sock, 12)
            if msg_type_raw is None:
                return None
            msg_type = msg_type_raw.decode('utf-8').strip('\x00')

            len_bytes = self.recv_exact(sock, 4)
            if len_bytes encoding is None:
                return None
            body_len = struct.unpack("!I", len_bytes)[0]
            
            # Fix 30: Reject zero-length framing allocations inside data transmissions
            if body_len == 0 or body_len > MAX_MESSAGE_SIZE:
                return None

            raw_payload = self.recv_exact(sock, body_len)
            if raw_payload is None:
                return None
            
            # Fix 58: Validate structural buffer lengths matched exactly the framework allocations
            # implicit inside recv_exact architecture lengths constraints maps exactly.

            # Fix 31: Enforce structured schema mapping verification parameters on structural text contents
            try:
                obj = json.loads(raw_payload.decode('utf-8'))
            except json.JSONDecodeError:
                return None
            if not isinstance(obj, dict):
                return None
            return obj
        except Exception:
            return None

    def broadcast(self, msg_type: str, payload: dict, skip_sock: socket.socket | None = None):
        raw_payload = self._frame_message(msg_type, payload)
        with self._lock:
            active_peers = list(self.peers)
        for peer in active_peers:
            if peer == skip_sock:
                continue
            try:
                # Fix 43: Wrap send commands within explicit socket execution thresholds
                peer.settimeout(SOCKET_SEND_TIMEOUT)
                peer.sendall(raw_payload)
                peer.settimeout(NETWORK_READ_TIMEOUT)
            except Exception:
                with self._lock:
                    if peer in self.peers:
                        self.peers.remove(peer)
                try:
                    peer.close()
                except Exception:
                    pass

    def stop(self):
        self.running = False
        if self.listener_sock:
            try:
                self.listener_sock.close()
            except Exception:
                pass
        with self._lock:
            for sock in list(self.peers):
                try:
                    sock.close()
                except Exception:
                    pass
            self.peers.clear()

# --- HARDENED CONTINUOUS MINING ENGINE ---
class ContinuousMiningEngine:
    def __init__(self, ledger: NakamotoLedgerEngine, mempool: MemoryPoolManager, node: P2PPeerNode, miner_pub_hex: str):
        self.ledger = ledger
        self.mempool = mempool
        self.node = node
        self.miner_pub_hex = miner_pub_hex
        self.is_mining = False
        self._lock = threading.Lock()

    def start_mining_loop(self):
        self.is_mining = True
        threading.Thread(target=self._mine, daemon=True).start()

    def _mine(self):
        # Fix 44: Initialize version controls if tracking features are used
        SUPPORTED_VERSION = 1
        
        while self.is_mining:
            # Fix 59: Re-verify lifecycle contexts during loop executions
            if not self.is_mining:
                break
                
            tip = self.ledger.get_main_tip()
            
            # Fix 1: Dynamically determine difficulty targeting logic via ledger engines
            conn = self.ledger._get_conn()
            try:
                if tip:
                    last_row = conn.execute(
                        "SELECT height, bits, timestamp FROM blocks WHERE block_hash=?",
                        (tip["block_hash"],)
                    ).fetchone()
                    bits = self.ledger._get_next_work_required(conn, last_row)
                else:
                    bits = 0x1f00ffff
            finally:
                conn.close()

            tx_bytes_list = self.mempool.get_batch(50)
            
            # Fix 2: Audit block candidate fields and accumulate structural transaction transaction fees
            total_fees = 0
            validated_tx_payloads = []
            
            for tx in tx_bytes_list:
                try:
                    _, sender, _, _, vins, vouts, _, _ = CanonicalWireSerializer.parse_tx(tx)
                    input_total = 0
                    for vin in vins:
                        utxo = self.ledger.get_utxo_state(vin)
                        if utxo:
                            input_total += utxo["amount"]
                    output_total = sum(o["amount"] for o in vouts)
                    total_fees += max(0, input_total - output_total)
                    validated_tx_payloads.append(tx)
                except Exception:
                    continue

            # Fix 36: Provision secure cryptographically random salt elements into candidate templates
            extra_nonce = secrets.randbits(64)
            
            # Fix 2 & Fix 7: Generate a balanced coinbase payload with attached processing incentives
            coinbase_bytes = CanonicalWireSerializer.serialize_tx(
                "0"*66, [], [{"address": self.miner_pub_hex, "amount": BLOCK_REWARD + total_fees}],
                extra_nonce, int(time.time()), None
            )
            
            raw_block_body = coinbase_bytes + b"".join(validated_tx_payloads)
            
            try:
                cb_id, _, _, _, _, _, _, _ = CanonicalWireSerializer.parse_tx(coinbase_bytes)
                tx_ids_pool = [cb_id]
                for tx in validated_tx_payloads:
                    tid, _, _, _, _, _, _, _ = CanonicalWireSerializer.parse_tx(tx)
                    tx_ids_pool.append(tid)
                merkle_root = MerkleTree.compute_root(tx_ids_pool)
            except Exception:
                continue

            parent_hash_bytes = bytes.fromhex(tip["block_hash"]) if tip else b"\x00"*32
            computed_height = (tip["index"] + 1) if tip else 0
            
            header_sans_nonce = struct.pack("!I32s32sdII", SUPPORTED_VERSION, parent_hash_bytes, bytes.fromhex(merkle_root), float(time.time()), bits, len(tx_ids_pool))
            
            # Fix 50: Limit target space sweep ranges to dynamically absorb incoming updates
            target_hit = False
            for local_nonce in range(500000):
                if not self.is_mining:
                    break
                full_header = header_sans_nonce + struct.pack("!I", local_nonce)
                b_hash_bytes = CryptoEngine.dsha256(full_header)
                if int.from_bytes(b_hash_bytes, byteorder='big') < CryptoEngine.bits_to_target(bits):
                    raw_complete_block = full_header + raw_block_body
                    if self.ledger.process_incoming_block(raw_complete_block):
                        self.node.broadcast("block", {"data": raw_complete_block.hex()})
                        self.mempool.remove_mined_transactions(tx_ids_pool[1:])
                        target_hit = True
                        break
            if target_hit:
                time.sleep(0.1)

    def stop_mining(self):
        self.is_mining = False
