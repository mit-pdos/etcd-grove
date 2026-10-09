/-
`(*consistentIndex).SetConsistentIndex(v, term)`. Lean-first (no Rocq counterpart); see
`InvCindex.lean`.
-/
import EtcdGrove.Server.InvCindex

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.cindex

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.cindex.Assumptions]

/-- `ci.SetConsistentIndex(v, term)` stores the index `v` (the linearization point: the
caller's update gets `ciIdx γ k` and gives back `ciIdx γ v`), then the term. -/
abbrev consistentIndex.SetConsistentIndex.spec : Prop :=
  ∀ (ci : Loc) (γ : CINames) (v term : w64),
  ⊢ ∀ Φ : val → IProp GF,
    (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗
      isCI ci γ) -∗
    (|={⊤ \ ↑ciN, ∅}=> ∃ k : w64, ciIdx γ k ∗ (ciIdx γ v ={∅, ⊤ \ ↑ciN}=∗ Φ #())) -∗
    WP (App (App (Val (ci @!! go.GoType.PointerType consistentIndex.ty @!! go!"SetConsistentIndex"))
      (Val #v)) (Val #term)) {{ Φ }}

end spec

end EtcdGrove
end Perennial
