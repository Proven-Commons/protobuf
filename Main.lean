/-
  Command line front end for the Protobuf wire format codec.

  One request per line, in the shape `op numbers`, where the op
  and the numbers are parted by one space, and the numbers are
  decimal numbers parted by commas, with no spaces inside the
  number list. A line holds a number in plain decimal: no sign,
  no leading zeros (the number 0 itself is written `0`), and at
  most twenty digits. An empty line is passed over with no
  answer. A request that breaks the line shape prints `error`.

  The operations:

  - `venc` takes one number, the value to encode, below 2^64,
    and prints its varint bytes as comma parted decimal numbers.
  - `vdec` takes comma parted byte numbers and prints `ok:` and
    the value when the bytes are exactly one varint that this
    slice reads, and `none` when they are not.
  - `enc` takes a field list in the field list format below and
    prints the message bytes as comma parted decimal numbers.
  - `dec` takes comma parted byte numbers and prints `ok:` and
    the field list in the same format when the bytes are a
    message this slice reads, and `none` when they are not.

  The field list format reads the numbers as groups, one group
  per field, in field order. A group is: the field number, the
  wire type, then the payload. The payload is one number, the
  varint value, for wire type 0. It is eight byte numbers for
  wire type 1. It is a length number and then that many byte
  numbers for wire type 2. It is four byte numbers for wire type
  5. The empty field list is the empty number list. A group that
  breaks these rules (a field number of 0 or above 536870911, a
  wire type outside 0, 1, 2, 5, a byte number above 255, a varint
  value or a length at or above 2^64, or numbers that run out in
  the middle of a group) makes the whole request malformed, and
  `enc` prints `error`. The full rules are in SPEC.md.
-/

import Protobuf

open Protobuf

/-- Read one number token: plain decimal digits, no sign, no
    leading zeros but for the number 0 itself, at most twenty
    digits. -/
def parseNat (s : String) : Option Nat :=
  let cs := s.toList
  if cs.isEmpty ∨ 20 < cs.length then none
  else if 1 < cs.length ∧ cs.head! = '0' then none
  else if cs.all Char.isDigit then
    some (cs.foldl (fun n c => n * 10 + (c.toNat - 48)) 0)
  else none

/-- Read the number list of a payload. The empty payload is the
    empty list. -/
def numsOf (payload : String) : Option (List Nat) :=
  if payload.isEmpty then some []
  else (payload.splitOn ",").mapM parseNat

/-- Read the byte list of a payload: every number at most 255. -/
def bytesOf (payload : String) : Option (List UInt8) :=
  (numsOf payload).bind fun ns =>
    if ns.all (· ≤ 255) then some (ns.map Nat.toUInt8) else none

/-- Take `n` byte values off the front of a number list. -/
def takeBytes : Nat → List Nat → Option (List UInt8 × List Nat)
  | 0, ts => some ([], ts)
  | _ + 1, [] => none
  | n + 1, t :: ts =>
    if t ≤ 255 then
      (takeBytes n ts).map fun (bs, rest) => (t.toUInt8 :: bs, rest)
    else none

/-- Read a field list off a number list, group by group, in the
    field list format of the header comment. The fuel count is
    the number count: each group eats at least two numbers. -/
def parseFieldTokens : Nat → List Nat → Option (List Field)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, num :: wt :: rest =>
    if num = 0 ∨ 536870912 ≤ num then none
    else if wt = 0 then
      match rest with
      | v :: rest' =>
        if v < 18446744073709551616 then
          (parseFieldTokens fuel rest').map (⟨num, .varint v⟩ :: ·)
        else none
      | [] => none
    else if wt = 1 then
      (takeBytes 8 rest).bind fun (bs, rest') =>
        (parseFieldTokens fuel rest').map (⟨num, .fixed64 bs⟩ :: ·)
    else if wt = 2 then
      match rest with
      | len :: rest' =>
        if len < 18446744073709551616 then
          (takeBytes len rest').bind fun (bs, rest'') =>
            (parseFieldTokens fuel rest'').map (⟨num, .bytes bs⟩ :: ·)
        else none
      | [] => none
    else if wt = 5 then
      (takeBytes 4 rest).bind fun (bs, rest') =>
        (parseFieldTokens fuel rest').map (⟨num, .fixed32 bs⟩ :: ·)
    else none
  | _, _ => none

/-- The numbers of one field, in the field list format. -/
def fieldTokens (f : Field) : List Nat :=
  f.num :: wireType f.value :: match f.value with
    | .varint v => [v]
    | .fixed64 bs => bs.map UInt8.toNat
    | .bytes bs => bs.length :: bs.map UInt8.toNat
    | .fixed32 bs => bs.map UInt8.toNat

/-- Print a number list as comma parted decimal numbers. -/
def joinNums (ns : List Nat) : String :=
  ns.foldl (fun acc n => if acc.isEmpty then toString n else acc ++ "," ++ toString n) ""

/-- Run one operation on one payload. The answer is `error` for a
    malformed request, and `none` (as an answer, for the decoders)
    for well formed bytes that this slice rejects. -/
def run (op payload : String) : String :=
  match op with
  | "venc" =>
    match numsOf payload with
    | some [v] =>
      if v < 18446744073709551616 then
        joinNums (List.map UInt8.toNat (encodeVarint v))
      else "error"
    | _ => "error"
  | "vdec" =>
    match bytesOf payload with
    | none => "error"
    | some bs =>
      match decodeVarint bs with
      | some (v, []) => s!"ok:{v}"
      | _ => "none"
  | "enc" =>
    match (numsOf payload).bind fun ns => parseFieldTokens ns.length ns with
    | some fs => joinNums (List.map UInt8.toNat (encodeMessage fs))
    | none => "error"
  | "dec" =>
    match bytesOf payload with
    | none => "error"
    | some bs =>
      match decodeMessage bs with
      | some fs =>
        let ts := fs.flatMap fieldTokens
        if ts.isEmpty then "ok:" else "ok:" ++ joinNums ts
      | none => "none"
  | _ => "error"

/-- Answer one request line. An empty line gets no answer. -/
def processLine (line : String) : Option String :=
  if line.isEmpty then none
  else
    match line.splitOn " " with
    | [op] => some (run op "")
    | [op, payload] => some (run op payload)
    | _ => some "error"

/-- The line without its line ending: LF, or CR LF. -/
def chomp (line : String) : String :=
  let cs := line.toList
  if cs.getLast? = some '\n' then
    let cs := cs.dropLast
    String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
  else line

def main : IO Unit := do
  let stdin ← IO.getStdin
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    match processLine (chomp line) with
    | some out => IO.println out
    | none => pure ()
