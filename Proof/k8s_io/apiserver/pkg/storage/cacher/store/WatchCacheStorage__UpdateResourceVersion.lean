/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/cacher/store/WatchCacheStorage__UpdateResourceVersion.lean`.
Lean-first (no Rocq counterpart).

Under the lock (its resource `wcsLockP w γ 1`, of the writer's state by agreement): the store's and
the indexer's versions, the snapshotter's (`UpdateResourceVersion`, not before its own: the state's
was not after `rv`), and the publication of the store's clone by the atomic store of
`latestSnapshot` in the invariant (`wcs_update`), as `UpdateStore`'s.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.cacher.store.WatchCacheStorage__UpdateResourceVersion
public import Spec.k8s_io.apiserver.pkg.storage.cacher.store.btreeStore__Clone
public import Spec.k8s_io.apiserver.pkg.storage.cacher.store.snapshotter__UpdateResourceVersion
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

theorem WatchCacheStorage.UpdateResourceVersion.wp_proof
    (wp_Clone : btreeStore.Clone.spec (GF := GF) (hG := hG))
    (wp_UpdateRV : snapshotter.UpdateResourceVersion.spec (GF := GF) (hG := hG)) :
    WatchCacheStorage.UpdateResourceVersion.spec (GF := GF) (hG := hG) := by
  intro w γ Ψ st rv hrv
  wp_start as ⟨#Hw, Hown, #HΨ⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold isWCS
  icases Hw with ⟨#Hinv, #Hguard⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [] as ⟨Hlk, HP⟩
  · iframe #
  unfold wcsLockP
  icases HP with ⟨%st', Hg, Hstore, Hidx, Hsnaps⟩
  unfold wcsOwn
  ihave ⟨%Heq, Hown, Hg⟩ := ghostVar_agree_keep γ.st st st' _ _ $$ [Hown Hg]
  · iframe
  subst Heq
  iunfold ownStore at Hstore
  icases Hstore with ⟨%t, Htr, Hrv, Ht⟩
  iunfold ownIndexer at Hidx
  icases Hidx with ⟨%ixs, %fns, %irv, %fs, Hixs, Hixo, Hfns, Hfno, #Hfs, Hirv⟩
  (try wp_auto)
  wp_apply (wp_UpdateRV _ st.2 rv hrv) $$ [$Hsnaps] as Hsnaps
  (try wp_auto)
  wp_apply (wp_Clone _ st.1 rv) $$ [Htr Hrv Ht] as %p2 ⟨Hstore, Hcl⟩
  · iunfold ownStore; iexists t; iframe
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
  imod wcs_update _ γ st (st.1, rv) $$ [Hg Hown Hpub] with ⟨Hg, Hown, Hpub⟩
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
    iexists (st.1, rv)
    simp only
    iframe Hpub Hp
    iframe #
  imodintro
  (try wp_auto)
  wp_apply (sync.RWMutex.wp_Unlock_guard _ _) $$ [$Hlk Hg Hstore Hixs Hixo Hfns Hfno Hirv Hsnaps]
  · iframe #
    inext
    iexists (st.1, rv)
    iframe
    iunfold ownIndexer
    iexists ixs, fns, rv, fs
    iframe
    iframe #
  (try wp_auto)
  iapply HΦ
  iunfold wcsOwn at Hown
  iexact Hown

end proof

end cacher
end EtcdGrove
end Perennial
