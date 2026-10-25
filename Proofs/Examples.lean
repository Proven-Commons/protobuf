/-
  The worked examples from the Protobuf encoding documentation,
  proved. The same examples run through the command line tool in
  the test harness, where they are checked byte by byte a second
  time.

  From the docs: the number 1 encodes as the single byte 1, and
  300 as the two bytes 172 and 2, since 300 is 44 plus two times
  128. The message with field 1 holding the varint 150 encodes as
  the bytes 8, 150, 1. The message with field 2 holding the text
  "testing" encodes as the tag byte 18, the length 7, and the
  seven text bytes.
-/

import Protobuf

namespace Protobuf.Examples

open Protobuf

/-- The byte list of the text "testing". -/
def testingBytes : List UInt8 := [116, 101, 115, 116, 105, 110, 103]

theorem encodeVarint_one : encodeVarint 1 = [1] := by
  rw [encodeVarint_def]
  decide

theorem encodeVarint_300 : encodeVarint 300 = [172, 2] := by
  rw [encodeVarint_def, encodeVarint_def]
  decide

theorem decodeVarint_300 : decodeVarint [172, 2] = some (300, []) := by decide

theorem encodeVarint_150 : encodeVarint 150 = [150, 1] := by
  rw [encodeVarint_def, encodeVarint_def]
  decide

/-- A varint of ten bytes with every value bit set is the largest
    64 bit number, and is accepted. -/
theorem decodeVarint_max :
    decodeVarint [255, 255, 255, 255, 255, 255, 255, 255, 255, 1] =
      some (18446744073709551615, []) := by decide

/-- The same ten bytes with 2 in the last byte carry a bit past
    64, and are rejected. -/
theorem decodeVarint_past64 :
    decodeVarint [255, 255, 255, 255, 255, 255, 255, 255, 255, 2] = none := by
  decide

/-- An eleven byte varint is rejected, however it ends. -/
theorem decodeVarint_eleven :
    decodeVarint [128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 1] =
      none := by decide

/-- A varint cut short by the end of the input is rejected. -/
theorem decodeVarint_cut : decodeVarint [172] = none := by decide

/-- The docs message example, on the encode side: field 1 with
    the varint 150. -/
theorem encode_test1 :
    encodeMessage [⟨1, .varint 150⟩] = [8, 150, 1] := by
  have h8 : encodeVarint 8 = [8] := by
    rw [encodeVarint_def]
    decide
  simp [encodeMessage, encodeField, encodeValue, wireType, h8, encodeVarint_150]

/-- The docs message example, on the decode side. -/
theorem decode_test1 :
    decodeMessage [8, 150, 1] = some [⟨1, .varint 150⟩] := by decide

/-- The docs string example, on the encode side: field 2 with
    the text "testing". -/
theorem encode_test2 :
    encodeMessage [⟨2, .bytes testingBytes⟩] =
      [18, 7, 116, 101, 115, 116, 105, 110, 103] := by
  have h18 : encodeVarint 18 = [18] := by
    rw [encodeVarint_def]
    decide
  have h7 : encodeVarint 7 = [7] := by
    rw [encodeVarint_def]
    decide
  simp [encodeMessage, encodeField, encodeValue, wireType, testingBytes, h18, h7]

/-- The docs string example, on the decode side. -/
theorem decode_test2 :
    decodeMessage [18, 7, 116, 101, 115, 116, 105, 110, 103] =
      some [⟨2, .bytes testingBytes⟩] := by decide

/-- A tag with field number zero is rejected. -/
theorem decode_field_zero : decodeMessage [0, 1] = none := by decide

/-- A group start tag, wire type 3, is rejected. -/
theorem decode_group_tag : decodeMessage [27, 1] = none := by decide

/-- A length that runs past the bytes left is rejected. -/
theorem decode_length_past : decodeMessage [18, 7, 116, 101] = none := by decide

end Protobuf.Examples
