/-
The results of the encoding/json model's translated part (`models/encoding/json`, the main tree's
`Code/encoding/json`; mit-pdos/etcd-grove#24, J2/J3): each proved spec with its callees' proofs
plugged in (Perennial's `sync.Mutex`), restated, with `#print axioms` of each.

* the codec registry: `SetCodec`, `getCodec` (`Registry.lean`: `codecInv`, `codecUnset`,
  `codecSetWith`);
* validity: `isSpace`, `skipSpace`, `valid` (over the registered codec's `Scan`, `scanOk F`);
* the per-type dispatch and the entry points: `marshalAny`, `Marshal` (`marshalVia J F v`), and
  `Unmarshal` (`unmarshalVia J F ptr`).

Proved elsewhere: `NewEncoder` and `Encoder.Encode` on a connection, at the model's encoder
`encRepModel` (`Codec/NewEncoder.lean`, `Codec/Encoder__Encode_conn.lean`: linked by their user,
vr's `Link.lean`, since `Encode`'s spec is over `net`). Not translated, not proved: the `Decoder`.
-/
module

public import Proof.encoding.json.Codec.getCodec
public import Proof.encoding.json.Codec.SetCodec
public import Proof.encoding.json.Codec.isSpace
public import Proof.encoding.json.Codec.skipSpace
public import Proof.encoding.json.Codec.valid
public import Proof.encoding.json.Codec.marshalAny
public import Proof.encoding.json.Codec.Marshal
public import Proof.encoding.json.Codec.Unmarshal
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace encoding.json

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [encoding.json.Assumptions] [sync.Assumptions]

theorem getCodec.wp : getCodec.spec (GF := GF) (hG := hG) :=
  getCodec.wp_proof sync.Mutex.wp_Lock sync.Mutex.wp_Unlock

theorem SetCodec.wp : SetCodec.spec (GF := GF) (hG := hG) :=
  SetCodec.wp_proof sync.Mutex.wp_Lock sync.Mutex.wp_Unlock

theorem isSpace.wp : isSpace.spec (GF := GF) (hG := hG) := isSpace.wp_proof

theorem skipSpace.wp : skipSpace.spec (GF := GF) (hG := hG) := skipSpace.wp_proof isSpace.wp

theorem valid.wp : valid.spec (GF := GF) (hG := hG) := valid.wp_proof skipSpace.wp

theorem marshalAny.wp : marshalAny.spec (GF := GF) (hG := hG) := marshalAny.wp_proof getCodec.wp

theorem Marshal.wp : Marshal.spec (GF := GF) (hG := hG) := Marshal.wp_proof marshalAny.wp

theorem Unmarshal.wp : Unmarshal.spec (GF := GF) (hG := hG) :=
  Unmarshal.wp_proof getCodec.wp valid.wp

end results

end encoding.json
end Perennial

#print axioms Perennial.encoding.json.getCodec.wp
#print axioms Perennial.encoding.json.SetCodec.wp
#print axioms Perennial.encoding.json.isSpace.wp
#print axioms Perennial.encoding.json.skipSpace.wp
#print axioms Perennial.encoding.json.valid.wp
#print axioms Perennial.encoding.json.marshalAny.wp
#print axioms Perennial.encoding.json.Marshal.wp
#print axioms Perennial.encoding.json.Unmarshal.wp
