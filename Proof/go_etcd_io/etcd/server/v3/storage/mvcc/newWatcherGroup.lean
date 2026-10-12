/-
Proof of `Spec/.../mvcc/newWatcherGroup.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newWatcherGroup
public import Spec.go_etcd_io.etcd.pkg.v3.adt.NewIntervalTree
@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.newWatcherGroup.wp_proof
    (hNew : adt.NewIntervalTree.spec (GF := GF) (hG := hG)) :
    mvcc.newWatcherGroup.spec (GF := GF) (hG := hG) := by
  wp_start
  rw [go.make1_underlying, go.is_underlying (t := watcherSetByKey.ty)]
  wp_apply (wp_map_make1 (K := GoString) (V := GoMap)) as %km Hkm
  wp_apply hNew as %t Ht
  rw [go.make1_underlying, go.is_underlying (t := watcherSet.ty)]
  wp_apply (wp_map_make1 (K := Loc) (V := Unit)) as %ws Hws
  iapply HΦ
  iintro %wg Hwg
  iunfold mvcc.ownWatcherGroup
  iexists km, ws, t, ∅, []
  simp only [named]
  iframe Hwg Ht
  isplitl [Hws]
  · iunfold mvcc.ownWatcherSet
    rw [show GMap.domSet (∅ : GMap Loc mvcc.WatchRange) = ∅ from GMap.fmap_empty _]
    iexact Hws
  isplitr
  · iapply BigSepM.bigSepM_empty.2; iempintro
  isplitl [Hkm]
  · iunfold mvcc.ownKeyMap
    iframe Hkm
    isplitl []
    · ipureintro; intro k; simp
    iapply BigSepM.bigSepM_empty.2; iempintro
  isplitl []
  · ipureintro; exact ⟨List.Pairwise.nil, fun ivl => by simp⟩
  iapply BigSepL.bigSepL_nil.2; iempintro

end proof

end EtcdGrove
end Perennial
