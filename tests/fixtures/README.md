# Ligare test fixtures

## struct_basic.lig
Struct type feature tour:
- Point, Person, Flag, Wrapper struct definitions
- Construction via `Name.mk`
- Field projection via `Name.field`
- `#check` + `#eval` with structs and fields

## struct_point.lig
Struct arithmetic:
- Vector-like operations on Point
- `add`, `scale`, `sum` functions
- Field comparison operators

## struct_nested.lig
Nested types:
- Struct inside union variant payload (Shape)
- Union inside struct field (Config)
- Mixed construction and `#eval`

## color.lig
Non-recursive union demo (full pipeline: parse → check → C codegen):
- Enum-style union (Color)
- Pattern matching function (`to_int`)
- `#eval` expressions compiled to native executable

## nat_peano.lig
Recursive Peano naturals (interpreter only):
- `Nat = Zero | Succ Nat`
- Nested variant construction
- Match with binding

## union_basic.lig
Union type feature tour:
- Enum + payload variants
- `#check` + `#eval` with match

## union_single.lig
Minimal smoke test: single union definition.

## union_color.lig
Color enum union type.

## union_option.lig
Option type with payload and matching.

## ffi.lig
FFI fixture:
- External pure C function (`ffi_abs`)
- External IO C function (`ffi_read`)
- Required `unsafe { ... }` call sites
- IO value unwrapped in a `do` block
- Full compile-and-run test expects output `7` then `8`

## Running

```sh
# Interpreter
cargo run -- tests/fixtures/struct_basic.lig

# Compile to native
cargo run -- tests/fixtures/struct_basic.lig -o test && ./test
```
