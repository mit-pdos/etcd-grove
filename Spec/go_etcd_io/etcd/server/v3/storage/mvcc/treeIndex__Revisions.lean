/-
`(*treeIndex).Revisions(key, end, atRev, limit, withTotalCount)` (`index.go:112`): under the read
lock, the revisions of the range's keys at `atRev` (`idxRange`: cut at the limit, the total), by
the caller's update, unchanged. Internal (`rangeKeys`). **Changes**: an atomic update over `idxAt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalIdx

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

/-- `ti.Revisions(key, end, atRev, limit, withTotalCount)`. -/
def treeIndex.Revisions.spec : Prop :=
  ∀ (ti : Loc) (γi : IdxName) (key endk : GoSlice) (k e : GoString) (dk de : DFrac) (atRev : w64)
    (limit : w64) (wt : Bool) (Q : IndexM → IProp GF),
  {{ pkgInit ∗ isTreeIndex (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti) γi ∗
      key ↦*{dk} k ∗ endk ↦*{de} e ∗
      AU <{ ∃∃ (M : IndexM) (c : Int), idxAt γi M c ∗ ⌜c ≤ sint.Z atRev⌝ }> @ ⊤ \ ↑idxN, ∅
        <{ idxAt γi M c, COMM Q M }> }}
    (App (App (App (App (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"Revisions")) (Val #key)) (Val #endk)) (Val #atRev)) (Val #limit)) (Val #wt))
  {{ (revs : GoSlice) (total : w64), RET (PairV #revs #total); key ↦*{dk} k ∗ endk ↦*{de} e ∗
      ∃ (M : IndexM) (out : List (GoString × Rev × Rev × w64)) (n : Nat), Q M ∗
        ⌜idxRange M (mrange k endk e) atRev (sint.Z limit) wt out n ∧ total = W64 n⌝ ∗
        revs ↦* out.map (fun x => revVal x.2.1) }}

end spec
end Mvcc
end EtcdGrove
end Perennial
