/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/CntL.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`cntL`'s reader bundles (fork change P2-B, notes/prove-swift.md §13 and §17): `getCmdDescWith`
checks `routineCount < MaxDescRoutines` and increments it in one `cntL` section, so at most
`MaxDescRoutines` descriptor goroutines are live. `cntL`'s ghost part `swift.cntLGhost` holds the
spawned goroutines' registry (a ghost map `γn` of loan ids, listed by `T`, `routineCount = |T|`)
and `MaxDescRoutines - routineCount` reader bundles of `delivered`; a spawned goroutine owns a
`swift.descSlot` (its loan id and its bundle) instead of the persistent `readerBorrowV`.

* `swift.cntLGhost_init`: from `d` bundles (New's `cmapReaders` ones), no goroutine, the run
  loop's freeze half at `false`;
* `swift.cntLGhost_spawn` (the run loop, its half at `false`) / `swift.cntLGhost_spawn_slot` (a
  running goroutine, by its own slot): `c < d`: one more goroutine, its slot handed out;
* `swift.cntLGhost_exit`: a goroutine's slot back (`routineCount--`; then `c ≥ 1`);
* round 17 (SWB-14's fix, fork 982c3e9): `swift.cntLGhost_freeze` (`stopDescs` read
  `routineCount <= 0`: no goroutine registered, the flag set) and `swift.cntLGhost_unfreeze`
  (`handleSync`'s `routineCount = 0`: the count is already 0, the flag cleared).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Defs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]

/-- `delivered`'s reader bundle (the map `dm`, its view `γdl`). -/
abbrev swift.delReader (dm : GoSlice) (γdl : GName) : IProp netDistGF :=
  github_com.orcaman.concurrent_map.readerV dm γdl swift.deliveredR

/-- A live descriptor goroutine's slot: its loan id `i` (never `0`, the freeze flag's key) in
the registry `γn` and its reader bundle of `delivered`. -/
def swift.descSlot (γn : GName) (dm : GoSlice) (γdl : GName) (i : Nat) : IProp netDistGF :=
  iprop(⌜i ≠ 0⌝ ∗ ghostMapElem γn i (DFrac.own 1) false ∗ swift.delReader dm γdl)

/-- **The run loop's half of `cntL`'s freeze flag** (round 17, SWB-14's fix): key `0` of the
registry `γn` holds a flag `f`, half in `cntL`'s invariant, half the run loop's. `f = true`
(frozen) means no goroutine is registered and `routineCount = 0`; a spawn needs `f = false`
(shown by the spawner's own slot, or by the run loop's half at `false`). `stopDescs` freezes
when it reads `routineCount <= 0`; `handleSync`'s `routineCount = 0` unfreezes (then it is a
no-op: the count is already 0). -/
def swift.cntFrozen (γn : GName) (f : Bool) : IProp netDistGF :=
  ghostMapElem γn 0 (DFrac.own (1 : Qp).half) f

/-- The registry's map: key `0` the freeze flag `f`, the registered loans `T` at `false`. -/
def swift.cntLMap (L : GMap Nat Bool) (f : Bool) (T : List Nat) : Prop :=
  ∀ i, L.lookup i = if i = 0 then some f else if i ∈ T then some false else none

/-- `cntL`'s ghost part at `routineCount = c` with the registered loans `T` (see the file
header); `d` is `MaxDescRoutines`. Round 17: with the freeze flag (`swift.cntFrozen`). -/
def swift.cntLGhost (γn : GName) (dm : GoSlice) (γdl : GName) (d c : w64) (T : List Nat) :
    IProp netDistGF :=
  iprop(∃ (L : GMap Nat Bool) (f : Bool), ghostMapAuth γn 1 L ∗
    ghostMapElem γn 0 (DFrac.own (1 : Qp).half) f ∗
    ⌜swift.cntLMap L f T ∧ 0 ∉ T ∧ T.Nodup ∧ T.length = sint.nat c ∧
      0 ≤ sint.Z c ∧ sint.Z c ≤ sint.Z d ∧ (f = true → T = [])⌝ ∗
    [∗list] _x ∈ List.replicate (sint.nat d - sint.nat c) (), swift.delReader dm γdl)

end defs

theorem swift.fresh_lt (T : List Nat) : ∀ x ∈ T, x < T.foldr max 0 + 1 := by
  induction T with
  | nil => intro x h; cases h
  | cons a t ih =>
    intro x hx
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 hx with rfl | h
    · omega
    · have := ih x h; omega

theorem swift.fresh_not_mem (T : List Nat) : T.foldr max 0 + 1 ∉ T :=
  fun h => by have := swift.fresh_lt T _ h; omega

theorem swift.cntLMap_insert {L : GMap Nat Bool} {f : Bool} {T : List Nat} {j : Nat}
    (h : swift.cntLMap L f T) (hj : j ≠ 0) :
    swift.cntLMap (L.insert j false) f (j :: T) := by
  intro i
  by_cases hij : j = i
  · subst hij; rw [GMap.lookup_insert]; simp [hj]
  · rw [GMap.lookup_insert_ne _ _ hij, h i]
    by_cases hi0 : i = 0
    · simp [hi0]
    · simp [hi0, Ne.symm hij]

theorem swift.cntLMap_delete {L : GMap Nat Bool} {f : Bool} {T : List Nat} {i : Nat}
    (h : swift.cntLMap L f T) (hnd : T.Nodup) (hi : i ≠ 0) :
    swift.cntLMap (L.delete i) f (T.erase i) := by
  intro j
  by_cases hij : i = j
  · subst hij; rw [GMap.lookup_delete]; simp [hi, hnd.mem_erase_iff]
  · rw [GMap.lookup_delete_ne _ hij, h j]
    by_cases hj0 : j = 0
    · simp [hj0]
    · simp [hj0, hnd.mem_erase_iff, Ne.symm hij]

theorem swift.cntLMap_flag {L : GMap Nat Bool} {f : Bool} {T : List Nat}
    (h : swift.cntLMap L f T) (f' : Bool) : swift.cntLMap (L.insert 0 f') f' T := by
  intro j
  by_cases hj : 0 = j
  · subst hj; rw [GMap.lookup_insert]; simp
  · rw [GMap.lookup_insert_ne _ _ hj, h j]; simp [Ne.symm hj]

theorem swift.cntLMap_slot {L : GMap Nat Bool} {f : Bool} {T : List Nat} {i : Nat}
    (h : swift.cntLMap L f T) (hi : i ≠ 0) (hl : L.lookup i = some false) : i ∈ T := by
  rw [h i, if_neg hi] at hl
  by_cases hm : i ∈ T
  · exact hm
  · rw [if_neg hm] at hl; cases hl

theorem swift.w64_zero_of (c : w64) (h0 : 0 ≤ sint.Z c) (h1 : sint.Z c ≤ 0) : c = W64 0 := by
  apply BitVec.eq_of_toInt_eq; simp only [sint.Z] at h0 h1
  rw [show (W64 0).toInt = 0 from rfl]; omega

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]

theorem swift.cntLGhost_init (dm : GoSlice) (γdl : GName) (d : w64) (hd : 0 ≤ sint.Z d) :
    ([∗list] _x ∈ List.replicate (sint.nat d) (), swift.delReader dm γdl) ⊢
      |==> ∃ γn, swift.cntLGhost γn dm γdl d (W64 0) [] ∗ swift.cntFrozen γn false := by
  iintro Hr
  imod ghost_map_alloc_empty (GF := netDistGF) (K := Nat) (V := Bool) with ⟨%γn, Ha⟩
  imod ghost_map_insert (γ := γn) (0 : Nat) false (GMap.lookup_empty _) $$ Ha with ⟨Ha, He⟩
  icases (ghostMapElem_halves γn (0 : Nat) false).1 $$ He with ⟨He1, He2⟩
  imodintro
  iexists γn
  unfold swift.cntFrozen swift.cntLGhost
  isplitl [Ha He1 Hr]
  rotate_left
  · iexact He2
  iexists _, false
  iframe Ha He1
  isplitr
  · ipureintro
    refine ⟨fun i => ?_, List.not_mem_nil, List.nodup_nil, rfl, by decide, by
      rw [show sint.Z (W64 0) = 0 from rfl]; exact hd, fun _ => rfl⟩
    by_cases hi : 0 = i
    · subst hi; rw [GMap.lookup_insert]; simp
    · rw [GMap.lookup_insert_ne _ _ hi]; simp [Ne.symm hi]
  rw [show sint.nat (W64 0) = 0 from rfl, Nat.sub_zero]
  iexact Hr

/-- The spawn at `f = false` (the two wrappers below show it). -/
theorem swift.cntLGhost_spawn_core (γn : GName) (dm : GoSlice) (γdl : GName) (d c : w64)
    (T : List Nat) (L : GMap Nat Bool) (hc : sint.Z c < sint.Z d)
    (hP : swift.cntLMap L false T ∧ 0 ∉ T ∧ T.Nodup ∧ T.length = sint.nat c ∧
      0 ≤ sint.Z c ∧ sint.Z c ≤ sint.Z d) :
    ghostMapAuth γn 1 L ∗ ghostMapElem γn 0 (DFrac.own (1 : Qp).half) false ∗
      ([∗list] _x ∈ List.replicate (sint.nat d - sint.nat c) (), swift.delReader dm γdl) ⊢
    |==> ∃ i, (swift.cntLGhost γn dm γdl d (c + W64 1) (i :: T) ∗ swift.descSlot γn dm γdl i) := by
  iintro ⟨Ha, H0, Hr⟩
  obtain ⟨hL, h0T, hnd, hlen, h0, hd⟩ := hP
  have hfr := swift.fresh_not_mem T
  have hne : T.foldr max 0 + 1 ≠ 0 := by omega
  have hnone : L.lookup (T.foldr max 0 + 1) = none := by
    rw [hL]; simp [hfr]
  imod ghost_map_insert (T.foldr max 0 + 1) false hnone $$ Ha with ⟨Ha, He⟩
  have hc1 : sint.Z (c + W64 1) = sint.Z c + 1 := by
    have : sint.Z d < 2 ^ 63 := by have := d.toInt_lt; simp [sint.Z] at *; omega
    word
  have hL' := swift.cntLMap_insert hL hne
  simp only [sint.nat, sint.Z] at hc1 hc hlen h0 hd ⊢
  have hn1 : (c + W64 1).toInt.toNat = c.toInt.toNat + 1 := by rw [hc1]; omega
  have hk : d.toInt.toNat - c.toInt.toNat = (d.toInt.toNat - (c.toInt.toNat + 1)) + 1 := by
    omega
  rw [hk, List.replicate_succ]
  icases (BigSepL.bigSepL_cons).1 $$ Hr with ⟨Hr1, Hr⟩
  imodintro
  iexists T.foldr max 0 + 1
  isplitr [He Hr1]
  · unfold swift.cntLGhost
    iexists _, false
    iframe Ha H0
    simp only [sint.nat, sint.Z]
    rw [hn1]
    iframe Hr
    ipureintro
    refine ⟨hL', ?_, List.nodup_cons.2 ⟨hfr, hnd⟩, by simp [hlen], by omega, by omega,
      fun h => nomatch h⟩
    simp only [List.mem_cons, not_or]; exact ⟨fun h => hne h.symm, h0T⟩
  · unfold swift.descSlot
    iframe
    ipureintro; exact hne

/-- A spawn by the run loop (its freeze flag's half at `false`). -/
theorem swift.cntLGhost_spawn (γn : GName) (dm : GoSlice) (γdl : GName) (d c : w64)
    (T : List Nat) (hc : sint.Z c < sint.Z d) :
    swift.cntLGhost γn dm γdl d c T ∗ swift.cntFrozen γn false ⊢
      |==> ∃ i, (swift.cntLGhost γn dm γdl d (c + W64 1) (i :: T) ∗ swift.descSlot γn dm γdl i ∗
        swift.cntFrozen γn false) := by
  unfold swift.cntFrozen
  iintro ⟨Hg, Hf⟩
  iunfold swift.cntLGhost at Hg
  icases Hg with ⟨%L, %f, Ha, H0, %Hp, Hr⟩
  icombine H0 Hf gives %Hc0
  obtain ⟨-, Hff⟩ := Hc0
  subst Hff
  imod swift.cntLGhost_spawn_core γn dm γdl d c T L hc
    ⟨Hp.1, Hp.2.1, Hp.2.2.1, Hp.2.2.2.1, Hp.2.2.2.2.1, Hp.2.2.2.2.2.1⟩ $$ [$Ha $H0 $Hr] with
    ⟨%i, Hg, Hs⟩
  imodintro
  iexists i
  iframe

/-- A spawn by a running descriptor goroutine (its own slot shows the flag is `false`). -/
theorem swift.cntLGhost_spawn_slot (γn : GName) (dm : GoSlice) (γdl : GName) (d c : w64)
    (T : List Nat) (j : Nat) (hc : sint.Z c < sint.Z d) :
    swift.cntLGhost γn dm γdl d c T ∗ swift.descSlot γn dm γdl j ⊢
      |==> ∃ i, (swift.cntLGhost γn dm γdl d (c + W64 1) (i :: T) ∗ swift.descSlot γn dm γdl i ∗
        swift.descSlot γn dm γdl j) := by
  iintro ⟨Hg, Hj⟩
  iunfold swift.cntLGhost at Hg
  icases Hg with ⟨%L, %f, Ha, H0, %Hp, Hr⟩
  iunfold swift.descSlot at Hj
  icases Hj with ⟨%hj0, Hje, Hjr⟩
  icombine Ha Hje gives %Hl
  have hjT := swift.cntLMap_slot Hp.1 hj0 Hl
  have hf : f = false := by
    cases f
    · rfl
    · have := Hp.2.2.2.2.2.2 rfl; subst this; cases hjT
  subst hf
  imod swift.cntLGhost_spawn_core γn dm γdl d c T L hc
    ⟨Hp.1, Hp.2.1, Hp.2.2.1, Hp.2.2.2.1, Hp.2.2.2.2.1, Hp.2.2.2.2.2.1⟩ $$ [$Ha $H0 $Hr] with
    ⟨%i, Hg, Hs⟩
  imodintro
  iexists i
  iframe Hg Hs
  iunfold swift.descSlot
  iframe
  ipureintro; exact hj0

/-- **A spawn by a loan holder** (round 38, plan R8b.1 (6), table rev 9 T4 by G/I): any share of a
registry element at `false` shows the flag is `false` (key `0`: it is the flag; else the holder
is registered, and a frozen registry has none). G uses `envK`'s `γn j ↦{¼}`, I the inline loan
record's `γn 0` share via its receipt. -/
theorem swift.cntLGhost_spawn_frac (γn : GName) (dm : GoSlice) (γdl : GName) (d c : w64)
    (T : List Nat) (j : Nat) (q : Qp) (hc : sint.Z c < sint.Z d) :
    swift.cntLGhost γn dm γdl d c T ∗ ghostMapElem γn j (DFrac.own q) false ⊢
      |==> ∃ i, (swift.cntLGhost γn dm γdl d (c + W64 1) (i :: T) ∗ swift.descSlot γn dm γdl i ∗
        ghostMapElem γn j (DFrac.own q) false) := by
  iintro ⟨Hg, Hj⟩
  iunfold swift.cntLGhost at Hg
  icases Hg with ⟨%L, %f, Ha, H0, %Hp, Hr⟩
  ihave %Hl := ghost_map_lookup $$ Ha Hj
  have hf : f = false := by
    by_cases hj0 : j = 0
    · subst hj0
      have := Hp.1 0
      rw [Hl] at this
      simp at this
      exact this
    · have hjT := swift.cntLMap_slot Hp.1 hj0 Hl
      cases f
      · rfl
      · have := Hp.2.2.2.2.2.2 rfl; subst this; cases hjT
  subst hf
  imod swift.cntLGhost_spawn_core γn dm γdl d c T L hc
    ⟨Hp.1, Hp.2.1, Hp.2.2.1, Hp.2.2.2.1, Hp.2.2.2.2.1, Hp.2.2.2.2.2.1⟩ $$ [$Ha $H0 $Hr] with
    ⟨%i, Hg, Hs⟩
  imodintro
  iexists i
  iframe Hg Hs Hj

theorem swift.cntLGhost_exit (γn : GName) (dm : GoSlice) (γdl : GName) (d c : w64)
    (T : List Nat) (i : Nat) :
    swift.cntLGhost γn dm γdl d c T ∗ swift.descSlot γn dm γdl i ⊢
      |==> (⌜1 ≤ sint.Z c⌝ ∗ swift.cntLGhost γn dm γdl d (c - W64 1) (T.erase i)) := by
  unfold swift.cntLGhost swift.descSlot
  iintro ⟨⟨%L, %f, Ha, H0, %Hp, Hr⟩, %hi0, He, Hr1⟩
  obtain ⟨hL, h0T, hnd, hlen, h0, hd, hfT⟩ := Hp
  icombine Ha He gives %Hl
  have hi : i ∈ T := swift.cntLMap_slot hL hi0 Hl
  have hc : 1 ≤ sint.Z c := by
    have := List.length_pos_of_mem hi
    simp only [sint.nat, sint.Z] at hlen h0 ⊢; omega
  imod (ghost_map_delete (γ := γn) (m := L) (k := i) (v := false)) $$ Ha He with Ha
  have hc1 : sint.Z (c - W64 1) = sint.Z c - 1 := by word
  have hL' := swift.cntLMap_delete hL hnd hi0
  simp only [sint.nat, sint.Z] at hc1 hc hlen h0 hd ⊢
  have hk : d.toInt.toNat - (c - W64 1).toInt.toNat = (d.toInt.toNat - c.toInt.toNat) + 1 := by
    rw [hc1]; omega
  imodintro
  isplitr
  · ipureintro; exact hc
  iexists _, f
  iframe Ha H0
  rw [hk, List.replicate_succ]
  isplitr
  · ipureintro
    refine ⟨hL', fun h => h0T (List.mem_of_mem_erase h), hnd.erase i, ?_, by omega, by omega,
      fun hf => by rw [hfT hf]; rfl⟩
    rw [List.length_erase_of_mem hi, hlen, hc1]; omega
  iapply BigSepL.bigSepL_cons.2
  iframe

/-- **The freeze** (`stopDescs`' exit, round 17): at `routineCount <= 0` no goroutine is
registered; the run loop's half and the invariant's go to `true`. -/
theorem swift.cntLGhost_freeze (γn : GName) (dm : GoSlice) (γdl : GName) (d c : w64)
    (T : List Nat) (hc : sint.Z c ≤ 0) :
    swift.cntLGhost γn dm γdl d c T ∗ swift.cntFrozen γn false ⊢
      |==> (⌜c = W64 0 ∧ T = []⌝ ∗ swift.cntLGhost γn dm γdl d c T ∗ swift.cntFrozen γn true) := by
  unfold swift.cntLGhost swift.cntFrozen
  iintro ⟨⟨%L, %f, Ha, H0, %Hp, Hr⟩, Hf⟩
  obtain ⟨hL, h0T, hnd, hlen, h0, hd, hfT⟩ := Hp
  icombine H0 Hf gives %Hc0
  obtain ⟨-, Hff⟩ := Hc0
  subst Hff
  have hc0 : c = W64 0 := swift.w64_zero_of c h0 hc
  have hT : T = [] := by
    apply List.eq_nil_of_length_eq_zero; rw [hlen, hc0]; rfl
  ihave He := (ghostMapElem_halves γn (0 : Nat) false).2 $$ [H0 Hf]
  · iframe
  imod ghost_map_update (γ := γn) (m := L) (k := (0 : Nat)) (v := false) true $$ Ha He with ⟨Ha, He⟩
  icases (ghostMapElem_halves γn (0 : Nat) true).1 $$ He with ⟨He1, He2⟩
  imodintro
  isplitr
  · ipureintro; exact ⟨hc0, hT⟩
  isplitl [Ha He1 Hr]
  rotate_left
  · iexact He2
  iexists _, true
  iframe Ha He1 Hr
  ipureintro
  exact ⟨swift.cntLMap_flag hL true, h0T, hnd, hlen, h0, hd, fun _ => hT⟩

/-- **The unfreeze** (`handleSync`'s `routineCount = 0`, round 17): the count is already 0. -/
theorem swift.cntLGhost_unfreeze (γn : GName) (dm : GoSlice) (γdl : GName) (d c : w64)
    (T : List Nat) :
    swift.cntLGhost γn dm γdl d c T ∗ swift.cntFrozen γn true ⊢
      |==> (⌜c = W64 0 ∧ T = []⌝ ∗ swift.cntLGhost γn dm γdl d c T ∗
        swift.cntFrozen γn false) := by
  unfold swift.cntLGhost swift.cntFrozen
  iintro ⟨⟨%L, %f, Ha, H0, %Hp, Hr⟩, Hf⟩
  obtain ⟨hL, h0T, hnd, hlen, h0, hd, hfT⟩ := Hp
  icombine H0 Hf gives %Hc0
  obtain ⟨-, Hff⟩ := Hc0
  subst Hff
  have hT : T = [] := hfT rfl
  have hc0 : c = W64 0 := by
    apply swift.w64_zero_of c h0
    rw [hT] at hlen; simp only [List.length_nil, sint.nat] at hlen; simp only [sint.Z]; omega
  ihave He := (ghostMapElem_halves γn (0 : Nat) true).2 $$ [H0 Hf]
  · iframe
  imod ghost_map_update (γ := γn) (m := L) (k := (0 : Nat)) (v := true) false $$ Ha He with ⟨Ha, He⟩
  icases (ghostMapElem_halves γn (0 : Nat) false).1 $$ He with ⟨He1, He2⟩
  imodintro
  isplitr
  · ipureintro; exact ⟨hc0, hT⟩
  isplitl [Ha He1 Hr]
  rotate_left
  · iexact He2
  iexists _, false
  iframe Ha He1 Hr
  ipureintro
  exact ⟨swift.cntLMap_flag hL false, h0T, hnd, hlen, h0, hd, fun h => nomatch h⟩

end lemmas

end Perennial.github_com.imdea_software.swiftpaxos
