/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/cacher/store/WatchCacheStorage__UpdateStore.lean`.
Lean-first (no Rocq counterpart).

Under the lock (its resource `wcsLockP w γ 1`, of the writer's state by agreement): the store's
update (`addOrUpdateElem` or `deleteElem`), the indexer's (no error: `isIndexFn`), the clone, its
publication by the atomic store of `latestSnapshot` in the invariant (where the ghost state moves,
`wcs_update`: the lock's half, the writer's quarter and the invariant's quarter), and the
snapshotter's `Add` (past its version: the state's was before `rv`).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.cacher.store.WatchCacheStorage__UpdateStore
public import Spec.k8s_io.apiserver.pkg.storage.cacher.store.btreeStore__addOrUpdateElem
public import Spec.k8s_io.apiserver.pkg.storage.cacher.store.btreeStore__deleteElem
public import Spec.k8s_io.apiserver.pkg.storage.cacher.store.btreeStore__Clone
public import Spec.k8s_io.apiserver.pkg.storage.cacher.store.indexer__updateElem
public import Spec.k8s_io.apiserver.pkg.storage.cacher.store.snapshotter__Add
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.sync.Results

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

theorem WatchCacheStorage.UpdateStore.wp_proof
    (wp_addOrUpdateElem : btreeStore.addOrUpdateElem.spec (GF := GF) (hG := hG))
    (wp_deleteElem : btreeStore.deleteElem.spec (GF := GF) (hG := hG))
    (wp_Clone : btreeStore.Clone.spec (GF := GF) (hG := hG))
    (wp_updateElem : indexer.updateElem.spec (GF := GF) (hG := hG))
    (wp_Add : snapshotter.Add.spec (GF := GF) (hG := hG)) :
    WatchCacheStorage.UpdateStore.spec (GF := GF) (hG := hG) := by
  intro w γ Ψ et e k st rv hrv het
  wp_start as ⟨#Hw, Hown, #He, #HΨ⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #He' := He
  iunfold isElem at He'
  icases He' with ⟨%el, #Hel, %Hkey⟩
  ihave %Hnn := typedPointsto_not_null $$ Hel
  unfold isWCS
  icases Hw with ⟨#Hinv, #Hguard⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_if_destruct
  · exfalso; simp_all
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [] as ⟨Hlk, HP⟩
  · iframe #
  unfold wcsLockP
  icases HP with ⟨%st', Hg, Hstore, Hidx, Hsnaps⟩
  unfold wcsOwn
  ihave ⟨%Heq, Hown, Hg⟩ := ghostVar_agree_keep γ.st st st' _ _ $$ [Hown Hg]
  · iframe
  subst Heq
  (try wp_auto)
  -- the element's key
  icases typedPointsto_split _ _ _ $$ Hel with Hel'
  try simp only [TypedPointsto.typedPointstoDef]
  icases Hel' with ⟨Hk, -⟩
  -- the previous element's facts
  ihave ⟨Hstore, #Hprev⟩ := ownStore_lookup _ _ _ _ k $$ Hstore
  rcases het with rfl | rfl | rfl
  · -- added
    have hU : updSt go!"ADDED" e k st rv = (btree.insert go.GoStringLt st.1 (e, k), rv) := by
      simp [updSt]
    rw [hU]
    rw [show decide ((go!"ADDED" : GoString) = go!"MODIFIED") = false by decide]
    simp only [k8s_io.apimachinery.pkg.watch.Added]
    (try wp_auto)
    wp_apply (wp_addOrUpdateElem _ st.1 st.2 e k rv) $$ [$Hstore] as Hstore
    · simp only [elemOrder]; iframe #
    (try wp_auto)
    rw [Hkey]
    wp_apply (wp_updateElem _ k _ e rv) $$ [$Hidx] as Hidx
    · iframe #
      iapply lookupFact_prev $$ Hprev
    (try wp_auto)
    wp_apply (wp_Clone _ _ rv) $$ [$Hstore] as %p2 ⟨Hstore, Hcl⟩
    imod isSnap_of_ownStore _ _ _ _ $$ Hcl with #Hsn
    (try wp_auto)
    wp_bind (App (Val #(methods _ _ _)) (Val #p2))
    iapply (sync.atomic.Pointer.wp_Store (T' := k8s_io.apiserver.pkg.storage.cacher.store.btreeStore)
      btreeStore.ty (structFieldRef WatchCacheStorage go!"latestSnapshot" w) p2)
    · iPkgInit
    iinv Hinv with ⟨%p0, %st0, >Hp, #Hs0, #HΨ0, >Hpub⟩ Hclose
    all_goals try exact fun _ _ => CoPset.mem_full
    iunfold wcsPub at Hpub
    ihave ⟨%Heq2, Hown, Hpub⟩ := ghostVar_agree_keep γ.st st st0 _ _ $$ [Hown Hpub]
    · iframe
    subst Heq2
    imod wcs_update _ γ st (btree.insert go.GoStringLt st.1 (e, k), rv) $$ [Hg Hown Hpub]
      with ⟨Hg, Hown, Hpub⟩
    · isplitl [Hg]; · iexact Hg
      isplitl [Hown]; · iunfold wcsOwn; iexact Hown
      iunfold wcsPub; iexact Hpub
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists p0
    iframe Hp
    iintro Hp
    imod Hmask with -
    imod Hclose $$ [Hp Hpub] with -
    · inext
      iexists p2
      iexists (btree.insert go.GoStringLt st.1 (e, k), rv)
      simp only
      iframe Hpub Hp
      iframe #
    imodintro
    (try wp_auto)
    wp_apply (wp_Add _ st.2 p2 (btree.insert go.GoStringLt st.1 (e, k)) rv hrv) $$ [$Hsnaps] as Hsnaps
    · iframe #
    (try wp_auto)
    wp_apply (sync.RWMutex.wp_Unlock_guard _ _) $$ [$Hlk Hg Hstore Hidx Hsnaps]
    · iframe #
      inext
      iexists (btree.insert go.GoStringLt st.1 (e, k), rv)
      iframe
    (try wp_auto)
    iapply HΦ
    iframe Hprev
    iunfold wcsOwn at Hown
    iexact Hown
  · -- modified
    have hU : updSt go!"MODIFIED" e k st rv = (btree.insert go.GoStringLt st.1 (e, k), rv) := by
      simp [updSt]
    rw [hU]
    rw [show decide ((go!"MODIFIED" : GoString) = go!"MODIFIED") = true by decide]
    (try wp_auto)
    wp_apply (wp_addOrUpdateElem _ st.1 st.2 e k rv) $$ [$Hstore] as Hstore
    · simp only [elemOrder]; iframe #
    (try wp_auto)
    rw [Hkey]
    wp_apply (wp_updateElem _ k _ e rv) $$ [$Hidx] as Hidx
    · iframe #
      iapply lookupFact_prev $$ Hprev
    (try wp_auto)
    wp_apply (wp_Clone _ _ rv) $$ [$Hstore] as %p2 ⟨Hstore, Hcl⟩
    imod isSnap_of_ownStore _ _ _ _ $$ Hcl with #Hsn
    (try wp_auto)
    wp_bind (App (Val #(methods _ _ _)) (Val #p2))
    iapply (sync.atomic.Pointer.wp_Store (T' := k8s_io.apiserver.pkg.storage.cacher.store.btreeStore)
      btreeStore.ty (structFieldRef WatchCacheStorage go!"latestSnapshot" w) p2)
    · iPkgInit
    iinv Hinv with ⟨%p0, %st0, >Hp, #Hs0, #HΨ0, >Hpub⟩ Hclose
    all_goals try exact fun _ _ => CoPset.mem_full
    iunfold wcsPub at Hpub
    ihave ⟨%Heq2, Hown, Hpub⟩ := ghostVar_agree_keep γ.st st st0 _ _ $$ [Hown Hpub]
    · iframe
    subst Heq2
    imod wcs_update _ γ st (btree.insert go.GoStringLt st.1 (e, k), rv) $$ [Hg Hown Hpub]
      with ⟨Hg, Hown, Hpub⟩
    · isplitl [Hg]; · iexact Hg
      isplitl [Hown]; · iunfold wcsOwn; iexact Hown
      iunfold wcsPub; iexact Hpub
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists p0
    iframe Hp
    iintro Hp
    imod Hmask with -
    imod Hclose $$ [Hp Hpub] with -
    · inext
      iexists p2
      iexists (btree.insert go.GoStringLt st.1 (e, k), rv)
      simp only
      iframe Hpub Hp
      iframe #
    imodintro
    (try wp_auto)
    wp_apply (wp_Add _ st.2 p2 (btree.insert go.GoStringLt st.1 (e, k)) rv hrv) $$ [$Hsnaps] as Hsnaps
    · iframe #
    (try wp_auto)
    wp_apply (sync.RWMutex.wp_Unlock_guard _ _) $$ [$Hlk Hg Hstore Hidx Hsnaps]
    · iframe #
      inext
      iexists (btree.insert go.GoStringLt st.1 (e, k), rv)
      iframe
    (try wp_auto)
    iapply HΦ
    iframe Hprev
    iunfold wcsOwn at Hown
    iexact Hown
  · -- deleted
    have hU : updSt go!"DELETED" e k st rv = (btree.delete st.1 k, rv) := by
      simp [updSt]
    rw [hU]
    rw [show decide ((go!"DELETED" : GoString) = go!"MODIFIED") = false by decide]
    simp only [k8s_io.apimachinery.pkg.watch.Added, k8s_io.apimachinery.pkg.watch.Deleted]
    (try wp_auto)
    wp_apply (wp_deleteElem _ st.1 st.2 e k rv) $$ [$Hstore] as Hstore
    · simp only [elemOrder]; iframe #
    (try wp_auto)
    rw [Hkey]
    wp_apply (wp_updateElem _ k _ null rv) $$ [$Hidx] as Hidx
    · iframe #
      isplitl
      · iapply lookupFact_prev $$ Hprev
      ileft; ipureintro; rfl
    (try wp_auto)
    wp_apply (wp_Clone _ _ rv) $$ [$Hstore] as %p2 ⟨Hstore, Hcl⟩
    imod isSnap_of_ownStore _ _ _ _ $$ Hcl with #Hsn
    (try wp_auto)
    wp_bind (App (Val #(methods _ _ _)) (Val #p2))
    iapply (sync.atomic.Pointer.wp_Store (T' := k8s_io.apiserver.pkg.storage.cacher.store.btreeStore)
      btreeStore.ty (structFieldRef WatchCacheStorage go!"latestSnapshot" w) p2)
    · iPkgInit
    iinv Hinv with ⟨%p0, %st0, >Hp, #Hs0, #HΨ0, >Hpub⟩ Hclose
    all_goals try exact fun _ _ => CoPset.mem_full
    iunfold wcsPub at Hpub
    ihave ⟨%Heq2, Hown, Hpub⟩ := ghostVar_agree_keep γ.st st st0 _ _ $$ [Hown Hpub]
    · iframe
    subst Heq2
    imod wcs_update _ γ st (btree.delete st.1 k, rv) $$ [Hg Hown Hpub]
      with ⟨Hg, Hown, Hpub⟩
    · isplitl [Hg]; · iexact Hg
      isplitl [Hown]; · iunfold wcsOwn; iexact Hown
      iunfold wcsPub; iexact Hpub
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists p0
    iframe Hp
    iintro Hp
    imod Hmask with -
    imod Hclose $$ [Hp Hpub] with -
    · inext
      iexists p2
      iexists (btree.delete st.1 k, rv)
      simp only
      iframe Hpub Hp
      iframe #
    imodintro
    (try wp_auto)
    wp_apply (wp_Add _ st.2 p2 (btree.delete st.1 k) rv hrv) $$ [$Hsnaps] as Hsnaps
    · iframe #
    (try wp_auto)
    wp_apply (sync.RWMutex.wp_Unlock_guard _ _) $$ [$Hlk Hg Hstore Hidx Hsnaps]
    · iframe #
      inext
      iexists (btree.delete st.1 k, rv)
      iframe
    (try wp_auto)
    iapply HΦ
    iframe Hprev
    iunfold wcsOwn at Hown
    iexact Hown

end proof

end cacher
end EtcdGrove
end Perennial
