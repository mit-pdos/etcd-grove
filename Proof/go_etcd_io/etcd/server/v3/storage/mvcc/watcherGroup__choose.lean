/-
Proof of `Spec/.../mvcc/watcherGroup__choose.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__choose
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__chooseAll
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__add
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newWatcherGroup

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

theorem mvcc.watcherGroup.choose.wp_proof
    (hNew : mvcc.newWatcherGroup.spec (GF := GF) (hG := hG))
    (hAdd : mvcc.watcherGroup.add.spec (GF := GF) (hG := hG))
    (hAll : mvcc.watcherGroup.chooseAll.spec (GF := GF) (hG := hG)) :
    mvcc.watcherGroup.choose.spec (GF := GF) (hG := hG) := by
  have hAdd := mvcc.watcherGroup.add.spec_group hAdd
  intro wg W ST maxWatchers curRev compactRev
  wp_start as ⟨Hg, HST, %Hdom, %Hst⟩
  icases mvcc.ownWatcherGroup_fixed wg W $$ Hg with ⟨Hg, #Hfixed⟩
  icases mvcc.ownWatcherGroup_watchers wg W $$ Hg with ⟨%v, Hwg, Hws, Hback⟩
  iunfold mvcc.ownWatcherSet at Hws
  wp_auto
  wp_apply wp_map_len_lt $$ Hws as ⟨Hws, %Hlt⟩
  have hs : GMap.size (domSet W) = GMap.size W := GMap.map_size_fmap _ _
  rw [hs] at Hlt ⊢
  have hsz : sint.Z (W64 (GMap.size W : Int)) = (GMap.size W : Int) := by
    have := Hlt; word
  (try wp_auto)
  wp_if_destruct
  · ihave Hg := Hback $$ Hwg [Hws]
    · iunfold mvcc.ownWatcherSet; iexact Hws
    wp_apply (hAll wg W ST curRev compactRev) $$ [$Hg $HST] as %m ⟨Hg, HST, %Hm⟩
    · ipureintro; exact ⟨Hdom, Hst⟩
    (try wp_auto)
    iapply HΦ
    iframe HST
    ileft
    iframe Hg
    ipureintro
    exact ⟨⟨rfl, by rw [← hsz]; exact Hif⟩, Hm⟩
  wp_apply hNew as %gv Hgv
  (try wp_auto)
  ihave Hret := Hgv $$ %ret_ptr ret
  have hWdom : ∀ k u, domSet W !! k = some u → ∃ r, W !! k = some r := by
    intro k u h
    have h' : (W !! k).map (fun _ => ()) = some u := h
    cases hW : W !! k with
    | none => rw [hW] at h'; cases h'
    | some r => exact ⟨r, rfl⟩
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_wand_r (Φ := fun bv => iprop(⌜bv = executeVal⌝ ∗ v.watchers' ↦$ domSet W ∗
      ∃ (W' : GMap Loc mvcc.WatchRange) (mw : w64) (wv : Loc),
        maxWatchers_ptr ↦ mw ∗ w_ptr ↦ wv ∗ mvcc.ownWatcherGroup ret_ptr W' ∗
        ⌜W' ⊆ W ∧ (GMap.size W' : Int) = max 0 (sint.Z maxWatchers)⌝)))
  isplitl [Hws maxWatchers w Hret]
  · iapply wp_map_for_range (fun (keys : List Loc) (i : Int) => iprop(∃ (mw : w64) (wv : Loc),
        "maxWatchers" ∷ maxWatchers_ptr ↦ mw ∗ "w" ∷ w_ptr ↦ wv ∗
        "Hret" ∷ mvcc.ownWatcherGroup ret_ptr (mvcc.takeMembers W keys i.toNat) ∗
        "%Hi" ∷ ⌜0 ≤ i ∧ i ≤ max 0 (sint.Z maxWatchers) ∧ sint.Z mw = sint.Z maxWatchers - i ∧
          (GMap.size (mvcc.takeMembers W keys i.toNat) : Int) = i⌝)) $$ Hws
    iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
    isplitl [maxWatchers w Hret]
    · iexists _, _
      simp only [named]
      rw [show (0 : Int).toNat = 0 from rfl, mvcc.takeMembers_zero]
      iframe
      ipureintro
      refine ⟨Int.le_refl _, by omega, by omega, ?_⟩
      rw [GMap.map_size_empty]; rfl
    isplitr
    · imodintro
      iintro %i %key %u ⟨%Hkey, %Hu⟩ HP
      iNamed HP
      obtain ⟨r, hr⟩ := hWdom key u Hu
      wp_auto
      wp_if_destruct
      · -- `maxWatchers <= 0`: break
        unfold forMapPostcondition
        iright; iright; ileft
        isplitr
        · ipureintro; rfl
        iintro Hws
        isplitr
        · ipureintro; rfl
        iframe Hws
        iexists mvcc.takeMembers W keys i.toNat, mw, key
        iframe maxWatchers w Hret
        ipureintro
        refine ⟨mvcc.takeMembers_subseteq _ _ _, ?_⟩
        have h0 : sint.Z (W64 0) = 0 := by decide
        omega
      -- add the watcher
      icases (BigSepM.bigSepM_lookup_acc hr).1 $$ Hfixed with ⟨⟨%fcs, #Hfx⟩, -⟩
      obtain ⟨hT, hN⟩ := mvcc.takeMembers_succ W keys i.toNat key r Hkey Hknodup hr
      wp_apply (hAdd ret_ptr _ key r fcs) $$ [$Hret $Hfx] as Hret
      · ipureintro; exact hN
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _, _
      simp only [named]
      rw [show (i + 1).toNat = i.toNat + 1 by omega, hT]
      iframe
      ipureintro
      have h0 : sint.Z (W64 0) = 0 := by decide
      have hmw : sint.Z (mw - W64 1) = sint.Z mw - 1 := by
        have : 0 < sint.Z mw := by omega
        word
      refine ⟨by omega, by omega, by omega, ?_⟩
      rw [GMap.map_size_insert_None _ _ _ hN]; push_cast; omega
    iintro HP Hws
    iNamed HP
    isplitr
    · ipureintro; rfl
    iframe Hws
    iexists _, _, _
    iframe Hret maxWatchers w
    ipureintro
    refine ⟨mvcc.takeMembers_subseteq _ _ _, ?_⟩
    rw [Hi.2.2.2]
    have hsW : (GMap.size (domSet W) : Int) = GMap.size W := by rw [hs]
    rw [hsz] at Hif
    omega
  iintro %bv ⟨%Hbv, Hws, %W', %mw, %wv, Hmw, Hw, Hret, %HW'⟩
  subst Hbv
  wp_auto
  wp_apply (hAll ret_ptr W' ST curRev compactRev) $$ [$Hret $HST] as %m ⟨Hret, HST, %Hm⟩
  · ipureintro
    refine ⟨fun w hw => ?_, Hst⟩
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hw
    exact Hdom w (by rw [GMap.lookup_weaken hr HW'.1]; rfl)
  (try wp_auto)
  iapply HΦ
  iframe HST
  iright
  iexists W'
  iframe Hret
  isplitl []
  · ipureintro
    refine ⟨HW'.1, by rw [hsz] at Hif; omega, HW'.2⟩
  isplitl [Hwg Hws Hback]
  · iapply Hback $$ Hwg
    iunfold mvcc.ownWatcherSet; iexact Hws
  ipureintro; exact Hm

end proof

end EtcdGrove
end Perennial
