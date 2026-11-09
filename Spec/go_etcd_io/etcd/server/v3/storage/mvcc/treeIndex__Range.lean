/-
`(*treeIndex).Range(key, end, atRev, limit, withTotalCount)` (`index.go:162`): as `Revisions`, the
keys (the index's own key slices, shared read-only: the keys-only read hands them out), their
revisions, creation revisions and versions. Internal (`rangeKeys`'s keys-only path,
`deleteRange`). **Changes**: an atomic update over `idxAt`.
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

/-- `ti.Range(key, end, atRev, limit, withTotalCount)`. -/
def treeIndex.Range.spec : Prop :=
  ∀ (ti : Loc) (γi : IdxName) (key endk : GoSlice) (k e : GoString) (dk de : DFrac) (atRev : w64)
    (limit : w64) (wt : Bool) (Q : IndexM → IProp GF),
  {{ pkgInit ∗ isTreeIndex (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti) γi ∗
      key ↦*{dk} k ∗ endk ↦*{de} e ∗
      AU <{ ∃∃ (M : IndexM) (c : Int), idxAt γi M c ∗ ⌜c ≤ sint.Z atRev⌝ }> @ ⊤ \ ↑idxN, ∅
        <{ idxAt γi M c, COMM Q M }> }}
    (App (App (App (App (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"Range")) (Val #key)) (Val #endk)) (Val #atRev)) (Val #limit)) (Val #wt))
  {{ (keys mods creates vers : GoSlice) (total : w64),
      RET (PairV (PairV (PairV (PairV #keys #mods) #creates) #vers) #total);
      key ↦*{dk} k ∗ endk ↦*{de} e ∗
      ∃ (M : IndexM) (out : List (GoString × Rev × Rev × w64)) (n : Nat), Q M ∗
        ⌜idxRange M (mrange k endk e) atRev (sint.Z limit) wt out n ∧ total = W64 n⌝ ∗
        bytesListAt keys (out.map Prod.fst) ∗ mods ↦* out.map (fun x => revVal x.2.1) ∗
        creates ↦* out.map (fun x => revVal x.2.2.1) ∗ vers ↦* out.map (fun x => x.2.2.2) }}

end spec
end Mvcc
end EtcdGrove
end Perennial
