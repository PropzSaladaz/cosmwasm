install webassembly target
```
rustup target add wasm32-unknown-unknown
```

Compile:
```
cargo build --target wasm32-unknown-unknown --release
```