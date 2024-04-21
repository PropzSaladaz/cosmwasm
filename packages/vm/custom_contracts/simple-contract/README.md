Compile the contract into WASM - release version:
```
cargo wasm
```

Compile debug version:
```
cargo wasm-debug
```

Check if contract is valid:
```
cosmwasm-check ./target/wasm32-unknown-unknown/release/contract.wasm
```

Compile:
```
cargo build --target wasm32-unknown-unknown
```