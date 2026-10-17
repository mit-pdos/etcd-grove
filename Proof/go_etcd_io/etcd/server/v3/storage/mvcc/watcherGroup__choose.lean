/-
Proof of `Spec/.../mvcc/watcherGroup__choose.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__choose
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__chooseAll
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__add
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newWatcherGroup
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__delete

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

theorem mvcc.watcherGroup.choose.wp_proofC
    (hNew : mvcc.newWatcherGroup.spec (GF := GF) (hG := hG))
    (hAdd : mvcc.watcherGroup.add.spec (GF := GF) (hG := hG))
    (hDel : mvcc.watcherGroup.delete.spec (GF := GF) (hG := hG)) :
    mvcc.watcherGroup.choose.specC (GF := GF) (hG := hG) := by
  have hAdd := mvcc.watcherGroup.add.spec_group hAdd
  have hDel := mvcc.watcherGroup.delete.spec_group hDel
  intro wg W maxWatchers curRev compactRev Ok P Q hAll hOk
  wp_start as ⟨Hg, HP, %Hpre⟩
  obtain ⟨HokW, HWsz, Hmw0⟩ := Hpre
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
    wp_apply (hAll wg W) $$ [$Hg $HP] as %m ⟨%K, %HK, Hg, HQ⟩
    · ipureintro; exact HokW
    (try wp_auto)
    iapply HΦ
    ileft
    isplitr
    · ipureintro; exact ⟨rfl, by rw [← hsz]; exact Hif⟩
    iexists K
    iframe Hg HQ
    ipureintro; exact HK
  have Hcap0 : sint.Z maxWatchers ≤ (GMap.size W : Int) := by rw [hsz] at Hif; omega
  wp_apply hNew as %gv Hgv
  (try wp_auto)
  ihave Hret := Hgv $$ %ret_ptr ret
  have hWdom : ∀ k u, domSet W !! k = some u → ∃ r, W !! k = some r := by
    intro k u h
    have h' : (W !! k).map (fun _ => ()) = some u := h
    cases hW : W !! k with
    | none => rw [hW] at h'; cases h'
    | some r => exact ⟨r, rfl⟩
  wp_apply (wp_slice_make3 (V := Loc) (W64 0) maxWatchers ⟨by decide, Hmw0⟩) as %sl ⟨Hsl, Hcap, -⟩
  (try wp_auto)
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_wand_r (Φ := fun bv => iprop(⌜bv = executeVal⌝ ∗ v.watchers' ↦$ domSet W ∗
      ∃ (W' : GMap Loc mvcc.WatchRange) (mw : w64) (wv : Loc) (s : GoSlice) (sel : List Loc),
        maxWatchers_ptr ↦ mw ∗ w_ptr ↦ wv ∗ mvcc.ownWatcherGroup ret_ptr W' ∗
        selected_ptr ↦ s ∗ s ↦* sel ∗ ownSliceCap Loc s (DFrac.own 1) ∗
        ⌜W' ⊆ W ∧ (GMap.size W' : Int) = sint.Z maxWatchers ∧
          (∀ k, (W' !! k).isSome ↔ k ∈ sel)⌝)))
  isplitl [Hws maxWatchers w Hret selected Hsl Hcap]
  · iapply wp_map_for_range (fun (keys : List Loc) (i : Int) => iprop(∃ (mw : w64) (wv : Loc)
        (s : GoSlice),
        "maxWatchers" ∷ maxWatchers_ptr ↦ mw ∗ "w" ∷ w_ptr ↦ wv ∗
        "Hret" ∷ mvcc.ownWatcherGroup ret_ptr (mvcc.takeMembers W keys i.toNat) ∗
        "selected" ∷ selected_ptr ↦ s ∗ "Hsl" ∷ s ↦* keys.take i.toNat ∗
        "Hcap" ∷ ownSliceCap Loc s (DFrac.own 1) ∗
        "%Hi" ∷ ⌜0 ≤ i ∧ i ≤ sint.Z maxWatchers ∧ sint.Z mw = sint.Z maxWatchers - i ∧
          (GMap.size (mvcc.takeMembers W keys i.toNat) : Int) = i⌝)) $$ Hws
    iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
    have hkW : ∀ k, k ∈ keys → (W !! k).isSome := by
      intro k hk
      have h := (Hkset k).1 hk
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 h
      obtain ⟨r, hr⟩ := hWdom k u hu
      rw [hr]; rfl
    isplitl [maxWatchers w Hret selected Hsl Hcap]
    · iexists _, _, _
      simp only [named]
      rw [show (0 : Int).toNat = 0 from rfl, mvcc.takeMembers_zero, List.take_zero,
        show ([] : List Loc) = List.replicate 0 (zero_val Loc) from rfl]
      iframe
      ipureintro
      refine ⟨Int.le_refl _, Hmw0, by omega, ?_⟩
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
        iexists mvcc.takeMembers W keys i.toNat, mw, key, s, keys.take i.toNat
        iframe maxWatchers w Hret selected Hsl Hcap
        ipureintro
        refine ⟨mvcc.takeMembers_subseteq _ _ _, ?_, mvcc.takeMembers_isSome W keys _ hkW⟩
        have h0 : sint.Z (W64 0) = 0 := by decide
        omega
      -- add the watcher
      icases (BigSepM.bigSepM_lookup_acc hr).1 $$ Hfixed with ⟨⟨%fcs, #Hfx⟩, -⟩
      obtain ⟨hT, hN⟩ := mvcc.takeMembers_succ W keys i.toNat key r Hkey Hknodup hr
      wp_apply (hAdd ret_ptr _ key r fcs) $$ [$Hret $Hfx] as Hret
      · ipureintro
        exact ⟨hN, by have := GMap.map_subseteq_size (mvcc.takeMembers_subseteq W keys i.toNat); omega⟩
      (try wp_auto)
      wp_apply wp_slice_literal (l := [key])
      isplitr
      · ipureintro; rfl
      iintro %lit ⟨Hlit, -⟩
      (try wp_auto)
      wp_apply wp_slice_append $$ [$Hsl $Hcap $Hlit] as %s' ⟨Hsl, Hcap, -⟩
      (try wp_auto)
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _, _, _
      simp only [named]
      have htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
        rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
      rw [show (i + 1).toNat = i.toNat + 1 by omega, hT]
      rw [show (i + 1).toNat = i.toNat + 1 by omega] at htake
      rw [htake]
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
    iexists _, _, _, _, _
    iframe Hret maxWatchers w selected Hsl Hcap
    ipureintro
    refine ⟨mvcc.takeMembers_subseteq _ _ _, ?_, mvcc.takeMembers_isSome W keys _ hkW⟩
    rw [Hi.2.2.2]
    have hsW : (GMap.size (domSet W) : Int) = GMap.size W := by rw [hs]
    rw [hsz] at Hif
    omega
  iintro %bv ⟨%Hbv, Hws, %W', %mw, %wv, %s, %sel, Hmw, Hw, Hret, Hsel, Hsl, Hcap, %HW'⟩
  subst Hbv
  ihave Hg := Hback $$ Hwg [Hws]
  · iunfold mvcc.ownWatcherSet; iexact Hws
  wp_auto
  wp_apply (hAll ret_ptr W') $$ [$Hret $HP] as %m ⟨%K, %HK, Hret, HQ⟩
  · ipureintro; exact hOk W' W HW'.1 HokW
  (try wp_auto)
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  have hselW : ∀ k, k ∈ sel → ∃ r, W !! k = some r := by
    intro k hk
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 ((HW'.2.2 k).2 hk)
    exact ⟨r, GMap.lookup_weaken hr HW'.1⟩
  ihave IH : iprop(∃ (n : w64) (wv : Loc),
      "i" ∷ i_ptr ↦ n ∗ "w" ∷ w_ptr ↦ wv ∗ "Hsl" ∷ s ↦* sel ∗
      "Hret" ∷ mvcc.ownWatcherGroup ret_ptr K ∗
      "Hg" ∷ mvcc.ownWatcherGroup wg (mvcc.retirePrefix W K sel (sint.nat n)) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ sel.length⌝) $$ [i w Hsl Hret Hg]
  · iexists W64 0, _
    rw [show sint.nat (W64 0) = 0 from rfl, mvcc.retirePrefix_zero]
    iframe i w Hsl Hret Hg
    ipureintro
    exact ⟨by decide, Nat.zero_le _⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < sel.length := by word
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z s.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd, and_self, ↓reduceIte]
    obtain ⟨e, He⟩ : ∃ e, sel[sint.nat n]? = some e := ⟨_, List.getElem?_eq_getElem Hlt⟩
    wp_apply wp_load_slice_index s (sint.Z n) sel _ e Hn.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact He
    (try wp_auto)
    icases mvcc.ownWatcherGroup_watchers ret_ptr K $$ Hret with ⟨%rv, Hrwg, Hrws, Hrback⟩
    iunfold mvcc.ownWatcherSet at Hrws
    (try wp_auto)
    wp_apply wp_map_lookup2 $$ Hrws as Hrws
    ihave Hret := Hrback $$ Hrwg [Hrws]
    · iunfold mvcc.ownWatcherSet; iexact Hrws
    (try wp_auto)
    have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    have hen : e ∈ sel := List.mem_of_getElem? He
    cases hKe : K !! e with
    | some re =>
      -- kept by `chooseAll`: nothing to retire
      simp only [Option.map_some, Option.isSome_some, decide_true, Bool.not_true]
      (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, e
      rw [hn1, mvcc.retirePrefix_keep W K sel _ e He (by rw [hKe]; rfl)]
      iframe
      ipureintro
      exact ⟨by word, by omega⟩
    | none =>
      -- retired by `chooseAll`: delete it from `wg`
      simp only [Option.map_none, Option.isSome_none, decide_false, Bool.not_false]
      obtain ⟨r, hr⟩ := hselW e hen
      icases (BigSepM.bigSepM_lookup_acc hr).1 $$ Hfixed with ⟨⟨%fcs, #Hfx⟩, -⟩
      (try wp_auto)
      wp_apply (hDel wg _ e r fcs) $$ [$Hg $Hfx] as Hg
      (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, e
      rw [hn1, mvcc.retirePrefix_del W K sel _ e He hKe]
      iframe
      ipureintro
      exact ⟨by word, by omega⟩
  -- the loop is done
  have hnl : sint.nat n = sel.length := by word
  rw [hnl, mvcc.retirePrefix_full W W' K sel HW'.2.2]
  (try wp_auto)
  iapply HΦ
  iright
  iexists W', K
  iframe Hret Hg HQ
  ipureintro
  exact ⟨HW'.1, Hcap0, HW'.2.1, HK⟩

/-- `spec` (nothing retired: no member below `compactRev`), as the instance of `specC` at
`chooseAll.spec`. -/
theorem mvcc.watcherGroup.choose.wp_proof
    (hNew : mvcc.newWatcherGroup.spec (GF := GF) (hG := hG))
    (hAdd : mvcc.watcherGroup.add.spec (GF := GF) (hG := hG))
    (hDel : mvcc.watcherGroup.delete.spec (GF := GF) (hG := hG))
    (hAll : mvcc.watcherGroup.chooseAll.spec (GF := GF) (hG := hG)) :
    mvcc.watcherGroup.choose.spec (GF := GF) (hG := hG) := by
  intro wg W ST maxWatchers curRev compactRev
  iintro %Φ ⟨#Hpkg, Hg, HST, %Hok, %Hpre⟩ HΦ
  have hMono : ∀ W1 W2 : GMap Loc mvcc.WatchRange, W1 ⊆ W2 →
      ((∀ w, (W2 !! w).isSome → (ST !! w).isSome) ∧
        ∀ w st, ST !! w = some st → sint.Z compactRev ≤ sint.Z st.minRev ∧
          sint.Z st.minRev ≤ sint.Z curRev ∧ st.restore = false) →
      ((∀ w, (W1 !! w).isSome → (ST !! w).isSome) ∧
        ∀ w st, ST !! w = some st → sint.Z compactRev ≤ sint.Z st.minRev ∧
          sint.Z st.minRev ≤ sint.Z curRev ∧ st.restore = false) := by
    intro W1 W2 h12 ⟨hd, hs⟩
    refine ⟨fun w hw => ?_, hs⟩
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hw
    exact hd w (by rw [GMap.lookup_weaken hr h12]; rfl)
  iapply (mvcc.watcherGroup.choose.wp_proofC hNew hAdd hDel wg W maxWatchers curRev compactRev _
    (mvcc.ownStates ST) _ (mvcc.watcherGroup.chooseAll.spec_G hAll ST curRev compactRev) hMono)
    $$ [Hg HST] [HΦ]
  · iframe Hpkg Hg HST; ipureintro; exact ⟨Hok, Hpre.1, Hpre.2⟩
  inext
  iintro %g %m Hpost
  icases Hpost with (⟨%Hg1, %K, %HK, Hg, %HQ, HST⟩ | ⟨%W', %K, %H', Hret, Hg, %HQ, HST⟩)
  · obtain ⟨rfl, Hm⟩ := HQ
    iapply HΦ
    iframe HST
    ileft
    iframe Hg
    ipureintro; exact ⟨Hg1, Hm⟩
  · obtain ⟨rfl, Hm⟩ := HQ
    rw [mvcc.retireChosen_self]
    iapply HΦ
    iframe HST
    iright
    iexists K
    iframe Hg Hret
    ipureintro
    exact ⟨⟨H'.1, H'.2.1, by rw [H'.2.2.1]; omega⟩, Hm⟩

end proof

end EtcdGrove
end Perennial
