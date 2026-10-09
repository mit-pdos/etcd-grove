/-
`(*consistentIndex).SetBackend(be)`. Lean-first (no Rocq counterpart); see `InvCindex.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvCindex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.cindex go_etcd_io.etcd.server.v3.storage

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.cindex.Assumptions]

/-- `ci.SetBackend(be)` (by the owner, under `mutex`) makes `be` the backend and resets the
index to 0 (the linearization point), so that the next read loads it from `be`. -/
abbrev consistentIndex.SetBackend.spec : Prop :=
  ∀ (ci : Loc) (γ : CINames) (b0 be : GoInterface),
  ⊢ ∀ Φ : val → IProp GF,
    (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗ isCI ci γ ∗ ciOwner ci b0) -∗
    (|={⊤ \ ↑ciN, ∅}=> ∃ k : w64, ciIdx γ k ∗ (ciIdx γ (W64 0) ={∅, ⊤ \ ↑ciN}=∗
      (ciOwner ci be -∗ Φ #()))) -∗
    WP (App (Val (ci @!! go.GoType.PointerType consistentIndex.ty @!! go!"SetBackend")) (Val #be)) {{ Φ }}

end spec

end EtcdGrove
end Perennial
