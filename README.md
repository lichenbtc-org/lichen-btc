# lichen-btc

The Bitcoin layer under [lichen](https://github.com/lichenbtc-org/lichen):
general pieces, none of them lichen's protocol (lichen's contract, its
transactions and its dispute live in lichen).

| Crate | What |
|---|---|
| `lichen-btc` | A thin layer over rust-bitcoin: keys, taproot trees, sighash, transactions, witnesses, Schnorr adaptor signatures, a regtest `bitcoind` |
| `lichen-wots` | Winternitz one-time signatures, signed off chain and checked in Bitcoin Script |
| `lichen-risc0` | RISC Zero 3.1's Groth16 statement checked natively: the verifying key, the receipt claim's digest, the proof's public inputs and points |

## Build and test

```sh
cargo test --workspace
```

The regtest tests start their own `bitcoind` (on the `PATH`, or
`LICHEN_BITCOIND`; `LICHEN_KEEP_DATADIR=1` keeps its data directory).
Tested with Rust 1.96 (`rust-toolchain.toml`) and Bitcoin Core 31.0.

## Using it

lichen depends on these crates by git commit:

```toml
lichen-btc = { git = "https://github.com/lichenbtc-org/lichen-btc", rev = "<commit>" }
```

## Origin

Extracted from [ln-gap](https://github.com/AdamISZ/ln-gap) at 8b057ed
(its `btc` crate, the Winternitz module of `lamport`, and the Groth16
module of `zk`), whose history has these files' earlier changes. Two
hashing tags keep ln-gap's names (`lngap-seed/`, `lngap/adaptor/nonce`),
so keys and nonces derived before the move stay the same.

## License

MIT
