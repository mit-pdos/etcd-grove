/- Lean-first (no Rocq counterpart).

# The invariant's resources across a cut's rename (W2, `notes/wal-fsext-plan.md`, "W2 implementation log")

The Iris parts of `walCut_osAUnc` (`CutAu.lean`) besides the claims: the past states give the
synced mark and the naming of the WAL (`walGhost_synced`, `walGhost_named`); the tail record moves
to the new layout (`walTailsRes_cut`); the segments' parts gain the new segment (`laysResF_cut`); the
parked halves gain the old tail's, the new segment and the new claim out (`walParked_cut`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutCommit

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- A WAL directory's claims with a layout replaced by one of the same directory. -/
theorem walDirClaimOf_insert {Ls : GMap GoString WalLay} {dir : GoString} {lay lay' : WalLay}
    (hl : Ls !! dir = some lay) (hj : lay'.j = lay.j) (c : Claim) :
    WalDirClaimOf (<[dir := lay']> Ls) c ↔ WalDirClaimOf Ls c := by
  constructor
  · rintro ⟨dir', lay1, hl', hj', hX⟩
    by_cases e : dir' = dir
    · subst e
      rw [GMap.lookup_insert] at hl'; cases hl'
      exact ⟨dir', lay, hl, hj ▸ hj', hX⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hl'
      exact ⟨dir', lay1, hl', hj', hX⟩
  · rintro ⟨dir', lay1, hl', hj', hX⟩
    by_cases e : dir' = dir
    · subst e
      rw [hl] at hl'; cases hl'
      exact ⟨dir', lay', GMap.lookup_insert _ _ _, hj.symm ▸ hj', hX⟩
    · exact ⟨dir', lay1, by rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hl', hj', hX⟩

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **The synced mark is at least a lower bound's** (the past states' authority). -/
theorem walGhost_synced (s : AbsDiskState) (dir : GoString) (n : Nat) :
    ⊢ walGhost (W := W) s -∗ walSyncedLb (W := W) dir n -∗
      ⌜∀ d, s.wal !! dir = some d → n ≤ d.m⌝ ∗ walGhost (W := W) s := by
  unfold walGhost walSyncedLb walPast
  iintro ⟨HG, HA, Hh, %Hk⟩ ⟨%s', %d', #Hp, %Hd'⟩
  icases absPast_le W.hA s s' $$ HA Hp with %Hle
  iframe HG HA Hh
  isplit
  · ipureintro
    intro d hd
    obtain ⟨d'', hd'', hm, -⟩ := Hle.2.2 dir d' Hd'.1
    rw [hd] at hd''; cases hd''
    exact Nat.le_trans Hd'.2 hm
  · ipureintro; exact Hk

/-- **A named WAL stays named** (the past states' authority). -/
theorem walGhost_named (s : AbsDiskState) (dir : GoString) :
    ⊢ walGhost (W := W) s -∗ walNamed (W := W) dir -∗
      ⌜∀ d, s.wal !! dir = some d → d.named = true⌝ ∗ walGhost (W := W) s := by
  unfold walGhost walNamed walPast
  iintro ⟨HG, HA, Hh, %Hk⟩ ⟨%s', %d', #Hp, %Hd'⟩
  icases absPast_le W.hA s s' $$ HA Hp with %Hle
  iframe HG HA Hh
  isplit
  · ipureintro
    intro d hd
    obtain ⟨d'', hd'', -, -, hn⟩ := Hle.2.2 dir d' Hd'.1
    rw [hd] at hd''; cases hd''
    exact hn Hd'.2
  · ipureintro; exact Hk

/-- **The tail record of `dir`, its other half**: the WAL, layout and last segment it records; given
back with the layout of `dir` replaced (`lay'`, its last segment `g`, F-Z and the record boundary),
the writes in flight unchanged on the other layouts' segments, a write in flight only on the new last
segment or one in flight before off the old (`TailsOnly`), and the invariant's new half. -/
theorem walTailsRes_cut (C : WalCodec) (Mr : WalMarshal) (s : AbsDiskState) (Ls : GMap GoString WalLay)
    (F : GMap Ino SegFl) (dir : GoString) (γ : GName) (tg : TailG) :
    ⊢ walTailsRes (W := W) C Mr s Ls F -∗ walTailKey (W := W) dir γ -∗ tailVar (W := W) γ tg -∗
      ∃ (d : WalDur) (lay : WalLay) (g0 : SegG),
        ⌜s.wal !! dir = some d ∧ Ls !! dir = some lay ∧ lay.segs.getLast? = some g0 ∧
          tg = tailG d lay g0.ino (F !! g0.ino)⌝ ∗
        walTailKey (W := W) dir γ ∗ tailVar (W := W) γ tg ∗ tailVar (W := W) γ tg ∗
        ∀ (lay' : WalLay) (g : SegG) (F' : GMap Ino SegFl),
          ⌜lay'.segs.getLast? = some g ∧ TailZeros lay' ∧ TailBound C Mr d lay' ∧
            (∀ k la, k ≠ dir → Ls !! k = some la → ∀ g' ∈ la.segs, F' !! g'.ino = F !! g'.ino) ∧
            (∀ i, F' !! i ≠ none → i = g.ino ∨ (F !! i ≠ none ∧ i ≠ g0.ino))⌝ -∗
          tailVar (W := W) γ (tailG d lay' g.ino (F' !! g.ino)) -∗
          walTailsRes (W := W) C Mr s (<[dir := lay']> Ls) F' := by
  letI := walAllG (W := W)
  unfold walTailsRes tailVar
  iintro ⟨%T, HTa, %HTo, %HTi, HTm⟩ Hk Hv
  icases walTailKey_lookup T dir γ $$ HTa Hk with %HT
  ihave ⟨Hent, HTm⟩ := (BigSepM.bigSepM_delete (Φ := fun (dir : GoString) (γ : GName) =>
    iprop(∃ (d : WalDur) (lay : WalLay) (g : SegG),
      ⌜s.wal !! dir = some d ∧ Ls !! dir = some lay ∧ lay.segs.getLast? = some g ∧ TailZeros lay ∧
        TailBound C Mr d lay⌝ ∗
      ghostVar γ (1 : Qp).half (tailG d lay g.ino (F !! g.ino)))) HT).1 $$ HTm
  icases Hent with ⟨%d, %lay, %g0, %hp, Hv'⟩
  obtain ⟨hd, hl, hg, -, -⟩ := hp
  icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Htg
  iexists d, lay, g0
  isplitr
  · ipureintro; exact ⟨hd, hl, hg, Htg⟩
  rw [Htg]
  iframe Hk Hv Hv'
  iintro %lay' %g %F' %hp Hvn
  obtain ⟨hg', hZ, hB, hF, hFo⟩ := hp
  iexists T
  iframe HTa
  isplitr
  · ipureintro; exact HTo.insert HT hl hg hg' hFo
  isplitr
  · ipureintro
    exact HTi.of_reg dir (fun h => by rw [HT] at h; cases h) (fun _ _ => rfl)
      (fun k hk => GMap.lookup_insert_ne _ _ (Ne.symm hk))
  iapply (BigSepM.bigSepM_delete (Φ := fun (k : GoString) (γ' : GName) =>
    iprop(∃ (d' : WalDur) (la : WalLay) (g' : SegG),
      ⌜s.wal !! k = some d' ∧ (<[dir := lay']> Ls) !! k = some la ∧
        la.segs.getLast? = some g' ∧ TailZeros la ∧ TailBound C Mr d' la⌝ ∗
      ghostVar γ' (1 : Qp).half (tailG d' la g'.ino (F' !! g'.ino)))) HT).2
  isplitl [Hvn]
  · iexists d, lay', g
    iframe Hvn
    ipureintro
    exact ⟨hd, GMap.lookup_insert _ _ _, hg', hZ, hB⟩
  · iapply BigSepM.bigSepM_mono (fun {k γ'} hk => ?_) $$ HTm
    have hne : k ≠ dir := by
      change GMap.delete dir T !! k = some γ' at hk
      rintro rfl; rw [GMap.lookup_delete_eq] at hk; cases hk
    iintro ⟨%d', %lay1, %g', %hp', Hv''⟩
    obtain ⟨hd', hl', hg1, hZ', hB'⟩ := hp'
    have he : F' !! g'.ino = F !! g'.ino := hF k lay1 hne hl' g' (List.mem_of_getLast? hg1)
    iexists d', lay1, g'
    rw [he]
    iframe Hv''
    ipureintro
    exact ⟨hd', by rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]; exact hl', hg1, hZ', hB'⟩

/-- **The segments' parts after the cut**: the layout of `dir` gains the new segment `g` (its halves,
no change in flight on it), the changes in flight unchanged off it. -/
theorem laysResF_cut (F : GMap Ino SegFl) (Ls : GMap GoString WalLay) (dir : GoString) (lay : WalLay)
    (b : Nat) (g : SegG) (wr : Nat) (hl : Ls !! dir = some lay)
    (hino : ∀ g' ∈ segsAll Ls, g'.ino ≠ g.ino) :
    laysResF (L := L) F Ls ∗ segRes (L := L) g ⊢
      laysResF (L := L) (GMap.delete g.ino F) (<[dir := cutLay lay b g wr]> Ls) := by
  have hF : ∀ g' ∈ segsAll Ls, (GMap.delete g.ino F) !! g'.ino = F !! g'.ino := fun g' hg' =>
    GMap.lookup_delete_ne _ (hino g' hg').symm
  iintro ⟨Hl, Hg⟩
  ihave Hl := laysResF_congr (L := L) F (GMap.delete g.ino F) Ls hF $$ Hl
  icases (laysResF_del (L := L) _ Ls dir lay hl).1 $$ Hl with ⟨Hs, Hrest⟩
  iapply (laysResF_map (L := L) _ _).2
  iapply (BigSepM.bigSepM_insert_delete (Φ := fun (_ : GoString) (la : WalLay) =>
    iprop([∗list] x ∈ la.segs, segResF (L := L) (GMap.delete g.ino F) x))).2
  isplitl [Hs Hg]
  · simp only [cutLay]
    iapply (BigSepL.bigSepL_append (PROP := IProp GF)).2
    iframe Hs
    iapply (BigSepL.bigSepL_singleton (PROP := IProp GF)).2
    unfold segResF
    rw [GMap.lookup_delete_eq]
    iexact Hg
  · iapply (laysResF_map (L := L) _ _).1 $$ Hrest

/-- **The parked halves after the cut**: the handle (holding the record of what is out, `o`) takes
the new segment out and deposits the old tail's halves (`segResP g0`, idle: no change in flight on
it); its directory's claim, out by key, keeps its key in the new history `c'` (in place of the old
`c`). -/
theorem walParked_cut (Ls : GMap GoString WalLay) (l1 l2 : List Claim) (c c' : Claim) (dir : GoString)
    (lay : WalLay) (g0 g : SegG) (b wr : Nat) (F : GMap Ino SegFl) (o : WalOut)
    (hl : Ls !! dir = some lay)
    (hg0 : lay.segs.getLast? = some g0) (hnd : ((segsAll Ls).map (·.ino)).Nodup)
    (hino : ∀ g' ∈ segsAll Ls, g'.ino ≠ g.ino) (hkey : c'.1 = c.1 ∧ c'.2.1 = c.2.1)
    (hD : (c.1, c.2.1) ∈ o.D) (hF0 : F !! g0.ino = none) :
    ⊢ walParked (L := L) (W := W) Ls (l1 ++ c :: l2) F -∗ walOutFrag (W := W) o -∗
        segResP (L := L) g0 ==∗
      walParked (L := L) (W := W) (<[dir := cutLay lay b g wr]> Ls) (l1 ++ c' :: l2) (GMap.delete g.ino F) ∗
        walOutFrag (W := W) ((o.delSeg g0.ino).addSeg g.ino) := by
  classical
  have hnd' := (segsAll_nodup_iff Ls).1 hnd
  obtain ⟨pre, hs⟩ := List.getLast?_eq_some_iff.1 hg0
  have hg0m : g0 ∈ lay.segs := by rw [hs]; simp
  have hpre : ∀ g' ∈ pre, g'.ino ≠ g0.ino := by
    intro g' hg' he
    have h := hnd'.1 dir lay hl
    rw [hs, List.map_append, List.nodup_append] at h
    exact h.2.2 g'.ino (List.mem_map_of_mem hg') g0.ino (by simp) he
  have hother : ∀ k la, k ≠ dir → Ls !! k = some la → ∀ g' ∈ la.segs, g'.ino ≠ g0.ino :=
    fun k la hk hla g' hg' => hnd'.2 k dir la lay hk hla hl g' hg' g0 hg0m
  unfold walParked
  iintro ⟨%bf, %o', Ha, Hoa, %hb, Hs, Hc, Ht⟩ Hf Hp
  icases walOut_agree (W := W) o' o $$ Hoa Hf with %ho
  subst ho
  imod walOut_set (W := W) o' o' ((o'.delSeg g0.ino).addSeg g.ino) $$ Hoa Hf with ⟨Hoa, Hf⟩
  imodintro
  iframe Hf
  obtain ⟨O, D, T⟩ := o'
  dsimp only [WalOut.delSeg, WalOut.addSeg] at hb hD ⊢
  iexists bf, ⟨g.ino :: O.filter (· ≠ g0.ino), D, T⟩
  dsimp only
  iframe Ha Hoa
  isplitr
  · ipureintro
    intro i hi
    by_cases he : i = g.ino
    · rw [he]; exact List.mem_cons_self ..
    · rw [GMap.lookup_delete_ne _ (Ne.symm he)] at hi
      have hi0 : i ≠ g0.ino := by rintro rfl; exact hi hF0
      refine List.mem_cons_of_mem _ ?_
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨hb i hi, hi0⟩
  isplitl [Hs Hp]
  · -- the segments
    iapply (segsAll_sep_map _ _).2
    ihave Hs := (segsAll_sep_map _ _).1 $$ Hs
    ihave ⟨Hd, Hrest⟩ := (BigSepM.bigSepM_delete (Φ := fun (_ : GoString) (la : WalLay) =>
      iprop([∗list] x ∈ la.segs, if x.ino ∈ O then emp else segResP (L := L) x)) hl).1 $$ Hs
    iapply (BigSepM.bigSepM_insert_delete (Φ := fun (_ : GoString) (la : WalLay) =>
      iprop([∗list] x ∈ la.segs, if x.ino ∈ g.ino :: O.filter (· ≠ g0.ino) then emp
        else segResP (L := L) x))).2
    isplitl [Hd Hp]
    · simp only [cutLay]
      rw [hs]
      icases (BigSepL.bigSepL_append (PROP := IProp GF)).1 $$ Hd with ⟨Hpre, Hlast⟩
      iapply (BigSepL.bigSepL_append (PROP := IProp GF)).2
      isplitl [Hpre Hlast Hp]
      · iapply (BigSepL.bigSepL_append (PROP := IProp GF)).2
        isplitl [Hpre]
        · iapply BigSepL.bigSepL_mono (fun {k x} hk => ?_) $$ Hpre
          have hx := List.mem_of_getElem? hk
          have h1 : x.ino ≠ g0.ino := hpre x hx
          have h2 : x.ino ≠ g.ino := hino x (mem_segsAll hl (by rw [hs]; simp [hx]))
          have e : (x.ino ∈ g.ino :: O.filter (· ≠ g0.ino)) ↔ x.ino ∈ O := by
            simp [h1, h2]
          simp only [propext e]
          exact .rfl
        · icases (BigSepL.bigSepL_singleton (PROP := IProp GF)).1 $$ Hlast with Hlast
          iapply (BigSepL.bigSepL_singleton (PROP := IProp GF)).2
          have h2 : g0.ino ≠ g.ino := hino g0 (mem_segsAll hl hg0m)
          have e : ¬ (g0.ino ∈ g.ino :: O.filter (· ≠ g0.ino)) := by simp [h2]
          rw [if_neg e]
          by_cases hO : g0.ino ∈ O
          · iexact Hp
          · rw [if_neg hO]; iexact Hlast
      · iapply (BigSepL.bigSepL_singleton (PROP := IProp GF)).2
        rw [if_pos (List.mem_cons_self ..)]
        iempintro
    · iapply BigSepM.bigSepM_mono (fun {k la} hk => ?_) $$ Hrest
      have hne : k ≠ dir := by
        change GMap.delete dir Ls !! k = some la at hk
        rintro rfl; rw [GMap.lookup_delete_eq] at hk; cases hk
      have hk' : Ls !! k = some la := by
        change GMap.delete dir Ls !! k = some la at hk
        rwa [GMap.lookup_delete_ne _ (Ne.symm hne)] at hk
      refine BigSepL.bigSepL_mono (fun {i x} hi => ?_)
      have hx := List.mem_of_getElem? hi
      have h1 : x.ino ≠ g0.ino := hother k la hne hk' x hx
      have h2 : x.ino ≠ g.ino := hino x (mem_segsAll hk' hx)
      have e : (x.ino ∈ g.ino :: O.filter (· ≠ g0.ino)) ↔ x.ino ∈ O := by
        simp [h1, h2]
      simp only [propext e]
      exact .rfl
  isplitl [Hc]
  · -- the claims
    icases (BigSepL.bigSepL_append (PROP := IProp GF)).1 $$ Hc with ⟨H1, H2⟩
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ H2 with ⟨-, H2⟩
    iapply (BigSepL.bigSepL_append (PROP := IProp GF)).2
    have hP : ∀ c1 ∈ l1 ++ l2, ParkedClaim (<[dir := cutLay lay b g wr]> Ls) D c1 ↔
        ParkedClaim Ls D c1 := by
      intro c1 _
      unfold ParkedClaim
      rw [walDirClaimOf_insert hl (by simp [cutLay]) c1]
    isplitl [H1]
    · iapply BigSepL.bigSepL_mono (fun {k c1} hk => ?_) $$ H1
      have e := hP c1 (List.mem_append_left _ (List.mem_of_getElem? hk))
      simp only [propext e]
      exact .rfl
    · iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
      isplitr
      · have e : ¬ ParkedClaim (<[dir := cutLay lay b g wr]> Ls) D c' := fun h =>
          h.2 (by rw [hkey.1, hkey.2]; exact hD)
        rw [if_neg e]
        iempintro
      · iapply BigSepL.bigSepL_mono (fun {k c1} hk => ?_) $$ H2
        have e := hP c1 (List.mem_append_right _ (List.mem_of_getElem? hk))
        simp only [propext e]
        exact .rfl
  · -- the pipeline names: the same directory
    iapply walTmpParked_insert Ls T dir lay (cutLay lay b g wr) hl rfl $$ Ht

end iris

end WalFs
end EtcdGrove
end Perennial

end
