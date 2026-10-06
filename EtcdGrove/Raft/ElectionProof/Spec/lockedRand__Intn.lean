/-
Port of `election_proof/spec_lockedRand__Intn.v`.
-/
import EtcdGrove.Raft.ElectionProof.InvBig

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `lr.Intn(n)` returns a value in `[0, n)` for a positive `n`. -/
abbrev lockedRand.Intn.spec : Prop :=
  ∀ (lr : Loc) (n : w64),
  0 < sint.Z n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isLockedRand lr }}
    (App (Val (lr @!! go.GoType.PointerType lockedRand.ty @!! go!"Intn")) (Val #n))
  {{ (v : w64), RET #v; ⌜0 ≤ sint.Z v ∧ sint.Z v < sint.Z n⌝ }}

end spec

end EtcdGrove
end Perennial
