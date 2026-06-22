# Ligare test fixtures

## union_single.lig
Basic smoke test: single union definition with three zero-payload variants.

## union_basic.lig
Full union feature demo:
- Enum-style union (Color)
- Union with payload (Option)
- `#check` variant constructors
- `#show` match expressions with and without bindings

## Running

```sh
cargo run -- tests/fixtures/union_basic.lig
```
