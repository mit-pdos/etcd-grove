/-
`(*consistentIndex).UnsafeConsistentIndex()`. Lean-first (no Rocq counterpart); see
`InvCindex.lean`.
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

/-- `ci.UnsafeConsistentIndex()` (by the owner, who knows the backend is `b`) reads the index (a linearization point); if it is not 0, returns it; else it loads the
index and term from the backend `b` (`isMetaBackend b E View`: the reads `readCIAU`) and
stores them (a second linearization point), returning the index.
Unlike `ConsistentIndex`, the load reads `be` without `mutex` (hence the owner's half) and
uses `schema.UnsafeReadConsistentIndex`, without `RLock`. -/
abbrev consistentIndex.UnsafeConsistentIndex.spec : Prop :=
  ∀ (ci : Loc) (γ : CINames) (b : GoInterface) (E : CoPset) (View : MetaCI → IProp GF),
  ⊢ ∀ Φ : val → IProp GF,
    (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗ isCI ci γ ∗ ciOwner ci b ∗ isMetaBackend b E View) -∗
    (|={⊤ \ ↑ciN, ∅}=> ∃ k : w64, ciIdx γ k ∗ (ciIdx γ k ={∅, ⊤ \ ↑ciN}=∗
      if k = W64 0 then
        readCIAU E View (fun m => iprop(|={⊤ \ ↑ciN, ∅}=> ∃ k' : w64, ciIdx γ k' ∗
          (ciIdx γ m.1 ={∅, ⊤ \ ↑ciN}=∗ (ciOwner ci b -∗ Φ #m.1))))
      else (ciOwner ci b -∗ Φ #k))) -∗
    WP (App (Val (ci @!! go.GoType.PointerType consistentIndex.ty @!! go!"UnsafeConsistentIndex")) (Val #())) {{ Φ }}

end spec

end EtcdGrove
end Perennial
