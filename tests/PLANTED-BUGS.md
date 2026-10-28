# Planted bugs

Written by `python3 tests/planted_bugs.py`. Each row is one small change to the
code, made in a copy. The tests ran on 20,000 inputs from their recorded seed
against the changed tool. A bug is caught when they report failures.

| Bug | File | Failures |
|-----|------|----------|
| Field number 0 read | `Protobuf/Wire.lean` | 170 |
| Tags of 2^32 or more read | `Protobuf/Wire.lean` | 174 |
| A tag of exactly 2^32 read | `Protobuf/Wire.lean` | 88 |
| Six-byte tags read | `Protobuf/Wire.lean` | 133 |
| Eleven-byte varints read | `Protobuf/Varint.lean` | 70 |
| Bits past the 64th kept | `Protobuf/Varint.lean` | 23 |
| No LEN length limit | `Protobuf/Wire.lean` | 0, not caught by the tests: it shows only when a length of 2^31 - 16 or more is followed by that many bytes, an input of about 2 GiB; a shorter input with such a length is refused for running out of input either way. `Protobuf.Spec.decode_iff` covers the limit. |
| A group start tag read as an empty LEN field | `Protobuf/Wire.lean` | 150 |
| isValid takes field number 2^29 | `Protobuf/Wire.lean` | 90 |
| CR kept at the end of a CR LF request | `Main.lean` | 2856 |

## The changes

**Field number 0 read** in `Protobuf/Wire.lean`:

```
- if 2 ^ 32 ≤ t ∨ t / 8 = 0 then none
+ if 2 ^ 32 ≤ t then none
```

**Tags of 2^32 or more read** in `Protobuf/Wire.lean`:

```
- if 2 ^ 32 ≤ t ∨ t / 8 = 0 then none
+ if t / 8 = 0 then none
```

**A tag of exactly 2^32 read** in `Protobuf/Wire.lean`:

```
- if 2 ^ 32 ≤ t ∨ t / 8 = 0 then none
+ if 2 ^ 32 < t ∨ t / 8 = 0 then none
```

**Six-byte tags read** in `Protobuf/Wire.lean`:

```
-   match Varint.decodeAux 5 bs with
+   match Varint.decodeAux 6 bs with
```

**Eleven-byte varints read** in `Protobuf/Varint.lean`:

```
-   match decodeAux 10 bs with
+   match decodeAux 11 bs with
```

**Bits past the 64th kept** in `Protobuf/Varint.lean`:

```
- | some (v, rest) => some (v % 2 ^ 64, rest)
+ | some (v, rest) => some (v, rest)
```

**No LEN length limit** in `Protobuf/Wire.lean`:

```
- if 2 ^ 31 - 16 ≤ len ∨ (rest.take len).length < len then none
+ if (rest.take len).length < len then none
```

**A group start tag read as an empty LEN field** in `Protobuf/Wire.lean`:

```
-       | _ => none
+       | 3 => some (⟨n, .len []⟩, rest)
+       | _ => none
```

**isValid takes field number 2^29** in `Protobuf/Wire.lean`:

```
- 1 ≤ f.number && f.number < 2 ^ 29 &&
+ 1 ≤ f.number && f.number ≤ 2 ^ 29 &&
```

**CR kept at the end of a CR LF request** in `Main.lean`:

```
-     String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
+     String.ofList cs
```
