/-
  Command line front end, used by the differential tests.

    protowire serve

  answers requests on standard input, one per line:

    decode HEX       prints  OK, then one tab-separated item per field,
                     NUMBER:KIND:VALUE; or REJECT
    encode FIELDS    prints  the hex of the encoded message, or INVALID
                     when a field cannot be written

  KIND is `varint`, `i64`, `len` or `i32`. VALUE is a decimal number,
  or for `len` the bytes in lower case hex (empty for no bytes). FIELDS
  is NUMBER:KIND:VALUE items separated by commas, or `-` for none.

  A malformed request prints `error`: an unknown operation, hex digits
  that are not in pairs, or a field item that does not parse. A request
  line may end in LF or CR LF.

  Every answer comes from the proved functions in `Protobuf/`: `decode`,
  `encode` and `Field.isValid`. The parsing and printing here are covered
  by the tests, not by a proof.
-/

import Protobuf

open Protobuf

def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def hexBytes : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    let hi ← hexValue a
    let lo ← hexValue b
    let bs ← hexBytes rest
    pure ((hi * 16 + lo).toUInt8 :: bs)
  | [_] => none

def hexDigit (n : Nat) : Char := "0123456789abcdef".toList.getD n '?'

def showHex (bs : List UInt8) : String :=
  String.ofList (bs.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])

/-- A number in plain decimal digits, refused past 30 digits so that a
    huge request cannot make the conversion slow. -/
def number (t : String) : Option Nat :=
  let ds := t.toList
  if ds.isEmpty || !ds.all Char.isDigit || ds.length > 30 then none else t.toNat?

def showField (f : Field) : String :=
  let (kind, value) := match f.value with
    | .varint v => ("varint", toString v)
    | .i64 v => ("i64", toString v)
    | .len d => ("len", showHex d)
    | .i32 v => ("i32", toString v)
  s!"{f.number}:{kind}:{value}"

def readField (item : String) : Option Field :=
  match item.splitOn ":" with
  | [n, kind, v] => do
    let n ← number n
    match kind with
    | "varint" => pure ⟨n, .varint (← number v)⟩
    | "i64" => pure ⟨n, .i64 (← number v)⟩
    | "len" => pure ⟨n, .len (← hexBytes v.toList)⟩
    | "i32" => pure ⟨n, .i32 (← number v)⟩
    | _ => none
  | _ => none

/-- The answer to one request line, or `none` when it is malformed. -/
def request (line : String) : Option String :=
  match line.splitOn " " with
  | ["decode", h] => do
    let bs ← hexBytes h.toList
    pure <| match decode bs with
      | some fs => "\t".intercalate ("OK" :: fs.map showField)
      | none => "REJECT"
  | ["encode", "-"] => pure (showHex (encode []))
  | ["encode", items] => do
    let fs ← (items.splitOn ",").mapM readField
    pure <| if fs.all Field.isValid then showHex (encode fs) else "INVALID"
  | _ => none

/-- The line without its line ending: LF, or CR LF. -/
def chomp (line : String) : String :=
  let cs := line.toList
  if cs.getLast? = some '\n' then
    let cs := cs.dropLast
    String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
  else line

def main (args : List String) : IO UInt32 := do
  match args with
  | ["serve"] =>
    let stdin ← IO.getStdin
    let stdout ← IO.getStdout
    repeat
      let line ← stdin.getLine
      if line.isEmpty then break
      stdout.putStrLn ((request (chomp line)).getD "error")
    return 0
  | _ =>
    IO.eprintln "usage: protowire serve"
    return 2
