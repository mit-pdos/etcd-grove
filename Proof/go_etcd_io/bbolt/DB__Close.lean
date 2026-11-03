/-
The proof of `Spec/go_etcd_io/bbolt/DB__Close.lean`: not yet (the invariants stage, after bbolt's
invariants are designed). Until then the backend rests on the old `_kv` axioms, not on this.
-/
module

public import Spec.go_etcd_io.bbolt.DB__Close

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem DB.Close.wp_proof : DB.Close.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end bbolt
end EtcdGrove
end Perennial
