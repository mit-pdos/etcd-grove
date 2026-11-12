/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/cacher/store/indexer__delete.lean`. Lean-first (no Rocq
counterpart).
The value's set, if any, is owned: the key deleted from it, and the
set deleted from the index once empty (its ownership dropped).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.cacher.store.indexer__delete

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cacher

open Iris Iris.BI Iris.ProofMode k8s_io.apiserver.pkg.storage.cacher.store

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.cacher.store.Assumptions]
variable [btree_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

theorem indexer.delete.wp_proof :
    indexer.delete.spec (GF := GF) (hG := hG) := by
  intro l key value ix
  wp_start as Hix
  iunfold ownIdx at Hix
  icases Hix with ⟨%m2, Hm, Hs⟩
  (try wp_auto)
  wp_apply (wp_map_lookup1 go.string (go.GoType.MapType go.string (go.GoType.PointerType Element.ty)) ix m2 value (DFrac.own 1)) $$ [$Hm] as Hm
  cases h : m2 !! value with
  | none =>
    simp only [Option.getD_none]
    (try wp_auto)
    iapply HΦ
    iunfold ownIdx
    iexists m2
    iframe
  | some l3 =>
    simp only [Option.getD_some]
    icases (BigSepM.bigSepM_delete (Φ := fun (_ : GoString) (l3 : Loc) => iprop(∃ m3 : GMap GoString Loc, ownMap (GF := GF) l3 (DFrac.own 1) m3)) h).1 $$ Hs with ⟨⟨%m3, Hset⟩, Hs⟩
    ihave %Hnn := ownMap_not_nil l3 m3 (DFrac.own 1) $$ Hset
    (try wp_auto)
    wp_if_destruct
    · exact absurd rfl Hnn
    (try wp_auto)
    wp_apply (wp_mapDelete l3 m3 key go.string (go.GoType.PointerType Element.ty)) $$ [$Hset] as Hset
    (try wp_auto)
    wp_apply (wp_map_len (t := go.GoType.MapType go.string (go.GoType.PointerType Element.ty)) l3 _ (DFrac.own 1)) $$ [$Hset] as Hset
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      wp_apply (wp_mapDelete ix m2 value go.string (go.GoType.MapType go.string (go.GoType.PointerType Element.ty))) $$ [$Hm] as Hm
      (try wp_auto)
      iapply HΦ
      iunfold ownIdx
      iexists _
      iframe
    · (try wp_auto)
      iapply HΦ
      iunfold ownIdx
      iexists m2
      iframe Hm
      iapply (BigSepM.bigSepM_delete (Φ := fun (_ : GoString) (l3 : Loc) => iprop(∃ m3 : GMap GoString Loc, ownMap (GF := GF) l3 (DFrac.own 1) m3)) h).2
      iframe Hs
      iexists _
      iexact Hset

end proof

end cacher
end EtcdGrove
end Perennial
