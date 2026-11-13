/-
The trust boundary: `proto.MarshalAppendCachedRecord.spec` (names-only; `walpb.Record`'s registered
pair; **pending the user's review**).
-/
module

public import LinuxFs.Spec.google_golang_org.protobuf.proto.MarshalAppendCachedRecord

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom proto.MarshalAppendCachedRecord.wp_proof :
  proto.MarshalAppendCachedRecord.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
