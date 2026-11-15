/-
`(*treeIndex).CountRevisions(key, end, atRev)` (`index.go:141`): under the read lock, the number of
the range's keys present at `atRev`, by the caller's update, unchanged. Internal (`rangeKeys`).
**Changes**: an atomic update over `idxAt`.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalIdx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc

/-- `ti.CountRevisions(key, end, atRev)`. -/
def treeIndex.CountRevisions.spec : Prop :=
  ∀ (ti : Loc) (γi : IdxName) (key endk : GoSlice) (k e : GoString) (dk de : DFrac) (atRev : w64)
    (Q : IndexM → IProp GF),
  {{ pkgInit ∗ isTreeIndex (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti) γi ∗
      key ↦*{dk} k ∗ endk ↦*{de} e ∗
      AU <{ ∃∃ (M : IndexM) (c : Int), idxAt γi M c ∗ ⌜c ≤ sint.Z atRev⌝ }> @ ⊤ \ ↑idxN, ∅
        <{ idxAt γi M c, COMM Q M }> }}
    (App (App (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"CountRevisions")) (Val #key)) (Val #endk)) (Val #atRev))
  {{ (total : w64), RET #total; key ↦*{dk} k ∗ endk ↦*{de} e ∗
      ∃ (M : IndexM) (out : List (GoString × Rev × Rev × w64)) (n : Nat), Q M ∗
        ⌜idxRange M (mrange k endk e) atRev 0 true out n ∧ total = W64 n⌝ }}

end spec
end Mvcc
end EtcdGrove
end Perennial
