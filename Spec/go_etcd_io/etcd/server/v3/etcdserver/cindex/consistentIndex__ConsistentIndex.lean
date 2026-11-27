/-
`(*consistentIndex).ConsistentIndex()`. Lean-first (no Rocq counterpart); see `InvCindex.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvCindex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.cindex go_etcd_io.etcd.server.v3.storage

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.cindex.Assumptions]

/-- `ci.ConsistentIndex()` (by the owner, who knows the backend is `b`) reads the index (a linearization point); if it is not 0, returns it; else it loads the
index and term from the backend `b` (`isMetaBackend b E View`: the reads `readCIAU`) and
stores them (a second linearization point), returning the index. (keepfix-d, 2026-11-27) The
store keeps the pair predicate: the read's continuation gives it for the pair read (keepfix (c): at the raft
term `rt` of the caller's mirror `ciRaftTerm`, given back).
The load is under `mutex` and uses `schema.ReadConsistentIndex` (under the read transaction's
`RLock`). -/
abbrev consistentIndex.ConsistentIndex.spec : Prop :=
  ∀ (ci : Loc) (γ : CINames) (P : w64 → w64 → w64 → IProp GF) (b : GoInterface) (rt : w64) (E : CoPset) (View : MetaCI → IProp GF),
  ⊢ ∀ Φ : val → IProp GF,
    (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗ isCI ci γ P ∗ ciOwner ci b ∗ ciRaftTerm γ rt ∗ isMetaBackend b E View) -∗
    (|={⊤ \ ↑ciN, ∅}=> ∃ k : w64, ciIdx γ k ∗ (ciIdx γ k ={∅, ⊤ \ ↑ciN}=∗
      if k = W64 0 then
        readCIAU E View (fun m => iprop((⌜m.1 = W64 0⌝ ∨ □ P m.1 m.2 rt) ∗
          |={⊤ \ ↑ciN, ∅}=> ∃ k' : w64, ciIdx γ k' ∗
          (ciIdx γ m.1 ={∅, ⊤ \ ↑ciN}=∗ (ciOwner ci b -∗ ciRaftTerm γ rt -∗ Φ #m.1))))
      else (ciOwner ci b -∗ ciRaftTerm γ rt -∗ Φ #k))) -∗
    WP (App (Val (ci @!! go.GoType.PointerType consistentIndex.ty @!! go!"ConsistentIndex")) (Val #())) {{ Φ }}

end spec

end EtcdGrove
end Perennial
