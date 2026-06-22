# Ligare test fixtures

## nat.lig
Non-recursive union demo (full pipeline: parse → check → C codegen):
- Enum-style union (Color)
- Pattern matching function (`to_int`)
- `#show` expressions compiled to native executable

## nat_peano.lig
Recursive Peano naturals (interpreter only):
- `Nat = Zero | Succ Nat`
- Nested variant construction
- Match with binding

## union_basic.lig
Union type feature tour:
- Enum + payload variants
- `#check` + `#show` with match

## union_single.lig
Minimal smoke test: single union definition.

## Running

```sh
# Interpreter
cargo run -- tests/fixtures/nat.lig

# Compile to native
cargo run -- tests/fixtures/nat.lig -o test && ./test
```
