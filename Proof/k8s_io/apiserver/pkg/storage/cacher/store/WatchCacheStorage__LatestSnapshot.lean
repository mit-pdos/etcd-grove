/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/cacher/store/WatchCacheStorage__LatestSnapshot.lean`.
Lean-first (no Rocq counterpart).

The atomic load of `latestSnapshot`, in the invariant (`isWCS`): the published snapshot, and the
caller's view shift against the published state, at the load.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.cacher.store.WatchCacheStorage__LatestSnapshot
public import Perennial.Proof.sync.atomic.Link

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

theorem WatchCacheStorage.LatestSnapshot.wp_proof :
    WatchCacheStorage.LatestSnapshot.spec (GF := GF) (hG := hG) := by
  intro w γ Ψ P Q
  wp_start as ⟨#Hw, HP, Hvs⟩
  unfold isWCS
  icases Hw with ⟨#Hinv, -⟩
  wp_auto
  wp_bind (App (Val #(methods _ _ _)) (Val #()))
  iapply (sync.atomic.Pointer.wp_Load (T' := k8s_io.apiserver.pkg.storage.cacher.store.btreeStore)
    btreeStore.ty (structFieldRef WatchCacheStorage go!"latestSnapshot" w) (DFrac.own 1))
  · iPkgInit
  iinv Hinv with ⟨%p, %st, >Hp, #Hsnap, #HΨ, >Hpub⟩ Hclose
  imod Hvs $$ %st Hpub HP with ⟨Hpub, HQ⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists p
  iframe Hp
  iintro Hp
  imod Hmask with -
  imod Hclose $$ [Hp Hpub] with -
  · inext; iexists p, st; iframe; iframe #
  imodintro
  wp_auto
  iapply HΦ
  iframe HQ Hsnap HΨ

end proof

end cacher
end EtcdGrove
end Perennial
