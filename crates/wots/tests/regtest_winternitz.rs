//! The Winternitz verify gadget through the interpreter.
use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use bitcoin::{Amount, TxOut};
use lichen_btc::regtest::Regtest;
use lichen_btc::taptree::{Leaf, TapTree};
use lichen_btc::tx::{build_spend, Timelock};
use lichen_btc::witness::WitnessStack;
use lichen_wots::{message_digits, Chain, Wots256Secret, WotsExt, WotsParams, WotsSecret, WotsSecretOf, WotsSig};

#[test]
fn winternitz_leaf_on_regtest() {
    let rt = Regtest::start().unwrap();
    for n_bytes in [32u32, 4] {
        winternitz_leaf(&rt, WotsSecret::from_entropy(WotsParams::for_bytes(n_bytes), [3u8; 32]));
    }
    // SHA-256 chains: a 4-byte word, as lichen's hub signs b
    winternitz_leaf(&rt, Wots256Secret::from_entropy(WotsParams::for_bytes(4), [3u8; 32]));
}

fn winternitz_leaf<H: Chain>(rt: &Regtest, sk: WotsSecretOf<H>) {
    let ps = sk.params;
    let n_bytes = ps.message_digits / 2;
    let pk = sk.public();
    let msg: Vec<u8> = (0..n_bytes as u8).map(|i| i.wrapping_mul(59).wrapping_add(1)).collect();
    // leaf: verify, then require the 64 digits equal the message's nibbles (last nibble on top)
    let mut b = Builder::new().wots_verify(&pk);
    for n in message_digits(&msg).iter().rev() {
        b = if *n == 0 { b.push_opcode(OP_PUSHBYTES_0) } else { b.push_int(i64::from(*n)) };
        b = b.push_opcode(OP_EQUALVERIFY);
    }
    let leaf = b.push_opcode(OP_PUSHNUM_1).into_script();
    eprintln!("SIZE wots verify leaf ({n_bytes} bytes): {} bytes", leaf.len());
    let tree = TapTree::new(vec![Leaf::new("w", leaf.clone(), Timelock::NONE)]).unwrap();
    let sink = TapTree::new(vec![Leaf::new("x", Builder::new().push_int(1).into_script(), Timelock::NONE)]).unwrap().script_pubkey();
    let spend = |items: Vec<Vec<u8>>| {
        let (op, _p) = rt.fund(&tree.script_pubkey(), Amount::from_sat(50_000)).unwrap();
        let mut tx = build_spend(op, &Timelock::NONE, vec![TxOut { value: Amount::from_sat(40_000), script_pubkey: sink.clone() }]);
        let mut w = WitnessStack::new();
        w.extend(items);
        tx.input[0].witness = w.build(&leaf, &tree.control_block("w").unwrap());
        tx
    };
    let sig = sk.sign(&msg).unwrap();
    let tx = spend(sig.consumption_order());
    let vs = rt.test_accept(&tx).unwrap();
    eprintln!("wots accepted: vsize {vs}, witness {} bytes", tx.input[0].witness.size());
    // wrong message
    let mut other = msg.clone();
    other[3] ^= 0x30;
    assert!(rt.test_accept(&spend(sk.sign(&other).unwrap().consumption_order())).is_err());
    // forgery: bump one digit by hashing its signature once more, checksum untouched
    let mut forged = sig.clone();
    forged.digits[5] += 1;
    forged.hashes[5] = H::hash(forged.hashes[5].as_ref());
    assert!(rt.test_accept(&spend(forged.consumption_order())).is_err(), "forged digit must fail the checksum");
    rt.send_and_confirm(&tx).unwrap();
}

/// The gadget reads a digit as a script number clamped to 15, so a 15
/// written as 16 verifies; `from_consumption_order` reads each digit as
/// Bitcoin does (`script_digit`), under mainnet's relay policy and in a
/// block.
#[test]
fn bitcoin_reads_a_digit_as_from_consumption_order_does() {
    let rt = Regtest::start_standard().unwrap();
    let ps = WotsParams::for_bytes(4);
    let sk = WotsSecret::from_entropy(ps, [5; 32]);
    let mut b = Builder::new().wots_verify(&sk.public());
    for _ in 0..ps.message_digits {
        b = b.push_opcode(OP_DROP);
    }
    let leaf = b.push_opcode(OP_PUSHNUM_1).into_script();
    let tree = TapTree::new(vec![Leaf::new("w", leaf.clone(), Timelock::NONE)]).unwrap();
    let sink = TapTree::new(vec![Leaf::new("x", Builder::new().push_int(1).into_script(), Timelock::NONE)]).unwrap().script_pubkey();
    let spend = |items: Vec<Vec<u8>>| {
        let (op, _) = rt.fund(&tree.script_pubkey(), Amount::from_sat(50_000)).unwrap();
        let mut tx = build_spend(op, &Timelock::NONE, vec![TxOut { value: Amount::from_sat(40_000), script_pubkey: sink.clone() }]);
        let mut w = WitnessStack::new();
        w.extend(items);
        tx.input[0].witness = w.build(&leaf, &tree.control_block("w").unwrap());
        tx
    };
    // a message with 15s among its digits
    let sig = sk.sign(&0x0f3f_f0ffu32.to_be_bytes()).unwrap();
    let items = sig.consumption_order();
    let fifteen = items.iter().position(|i| i.as_slice() == [15]).unwrap();
    // each encoding of 15 that relays reads as 15
    for written in [vec![16], vec![0x7f], vec![0xff, 0xff, 0xff, 0x7f]] {
        let mut loose = items.clone();
        loose[fifteen] = written.clone();
        rt.test_accept(&spend(loose.clone())).unwrap_or_else(|e| panic!("{written:?}: {e}"));
        assert_eq!(WotsSig::from_consumption_order(ps, &loose).unwrap(), sig, "{written:?}");
    }
    // a nonminimal one doesn't relay but is valid in a block (minimal
    // numbers are only policy in tapscript): read as 15 too
    let mut nonminimal = items.clone();
    nonminimal[fifteen] = vec![15, 0];
    assert!(rt.test_accept(&spend(nonminimal.clone())).is_err());
    assert_eq!(WotsSig::from_consumption_order(ps, &nonminimal).unwrap(), sig);
    // a negative digit or an element longer than a number: Bitcoin
    // refuses it, and so does from_consumption_order
    for bad in [vec![0x81], vec![15, 0, 0, 0, 0]] {
        let mut b = items.clone();
        b[fifteen] = bad.clone();
        assert!(rt.test_accept(&spend(b.clone())).is_err(), "{bad:?}");
        assert!(WotsSig::from_consumption_order(ps, &b).is_err(), "{bad:?}");
    }
}
