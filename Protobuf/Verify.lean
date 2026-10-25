/-
  Axiom check for the claims this package makes. Run with:

    lake env lean Protobuf/Verify.lean

  Every claim should list only the standard axioms (propext,
  Classical.choice, Quot.sound). A line naming sorryAx would mean
  a proof rests on an admitted gap, and the claim is not proved.
-/

import Proofs
import Proofs.Examples

open Protobuf.Proofs Protobuf.Examples

#print axioms decodeVarint_encode
#print axioms decodeVarint_encode_append
#print axioms parseField_encode
#print axioms decodeMessage_encode
#print axioms encodeVarint_300
#print axioms decode_test1
#print axioms decode_test2
