/- Lean-first (no Rocq counterpart).

# The cleanup's rename, pure part (W4, `notes/wal-units/create.md`, session 4)

`Create`'s `cleanupWAL` renames the directory `J` of the WAL being created from its name `nm` to
`brk` (`nm.broken.<time>`, which holds nothing or an empty directory) in the area claim `(jr, N, h)`
the cleanup pinned (`walCreatingAuth`'s `cleanKey`), logged at `x` by a call begun at `st ≥ h.next`.
The WAL stays in the real state (the client's `walDirIs dir` keeps it: `Create` has no fragment to
change it), unnamed (`walNamesRes`), its layout unchanged; only the area claim changes
(`movClaims`). `walsOk_moved` and its companions: the invariant's pure facts after it.

* A crash dropping the rename is a crash of the claims before it (`regionCrashedK_unlog`).
* A crash keeping it keeps every earlier entry of the claim (their calls began before the rename's):
  `nm` holds nothing (`CrashTo`'s left disjunct, the WAL unnamed), and the tree with the rename undone
  (`movUndo`: `nm` and `brk` as the claim had them) is a crash of the claims before it, which the
  other WALs' conditions see as the crashed tree itself: they read their own names in the area
  (neither `nm` nor `brk`) and their directories' entries (not the area's, `WalsAt`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CutCommitPure
public import Spec.os.RenameAny

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section pure
variable [GooseExts]

/-- The cleanup's rename's entry (`renDirOutA`'s), by a call begun at `st`. -/
def movEnt (jr J : Ino) (nm brk : GoString) (h : NamesH) (st : Nat) : LogEntry :=
  renDirEntA jr nm brk J (h.cur !! brk) st

/-- The pinned claim's names after the rename (`renDirOutA`'s). -/
def movCur (N : NameSet) (h : NamesH) (nm brk : GoString) (J : Ino) : Ents :=
  restrictN N (<[brk := Node.dir J]> (GMap.delete nm h.cur))

/-- The claims after the rename: the pinned claim logged. -/
def movClaims (cl : List Claim) (jr : Ino) (N : NameSet) (h : NamesH) (x st : Nat) (nm brk : GoString)
    (J : Ino) : List Claim :=
  replClaim (jr, N, h) (jr, N, h.log x (movEnt jr J nm brk h st) (movCur N h nm brk J)) cl

/-- The tree with the rename undone: `nm` and `brk` as the claim had them. -/
def movUndo (m' : Tree) (jr : Ino) (nm brk : GoString) (h : NamesH) : Tree :=
  treeSetE (treeSetE m' jr brk (h.cur !! brk)) jr nm (h.cur !! nm)

/-- **The hypotheses of the cleanup's rename** in the claim `(jr, N, h)` of `cl`. -/
structure MovedHyp (cl : List Claim) (jr : Ino) (N : NameSet) (h : NamesH) (st : Nat)
    (nm brk : GoString) (J : Ino) : Prop where
  mem : (jr, N, h) ∈ cl
  coh : ClaimCoh h jr N
  start : h.next ≤ st
  others : ∀ c' ∈ cl, c' ≠ (jr, N, h) → c'.1 = jr → ¬ c'.2.1.Mem nm ∧ ¬ c'.2.1.Mem brk
  ne : nm ≠ brk
  nmN : N.Mem nm
  brkN : N.Mem brk
  cnm : h.cur !! nm = some (.dir J)

theorem movEnt_writes (jr J : Ino) (nm brk : GoString) (h : NamesH) (st : Nat) (j : Ino)
    (b : GoString) : (movEnt jr J nm brk h st).op.Writes j b ↔ j = jr ∧ (b = nm ∨ b = brk) := by
  unfold movEnt renDirEntA MetaOp.Writes MetaOp.slots
  constructor
  · rintro (h | ⟨j0, b0, h⟩)
    · simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨rfl, Or.inl rfl⟩
      · exact ⟨rfl, Or.inr rfl⟩
    · cases h
  · rintro ⟨rfl, rfl | rfl⟩
    · left; simp
    · left; simp

theorem movUndo_entry (m' : Tree) (jr : Ino) (nm brk : GoString) (h : NamesH) (j : Ino) (b : GoString) :
    (movUndo m' jr nm brk h).entry j b =
      if j = jr ∧ b = nm then h.cur !! nm else if j = jr ∧ b = brk then h.cur !! brk else m'.entry j b := by
  unfold movUndo
  rw [treeSetE_entry, treeSetE_entry]

theorem movUndo_entry_other {m' : Tree} {jr : Ino} {nm brk : GoString} {h : NamesH} {j : Ino}
    {b : GoString} (hb : ¬ (j = jr ∧ (b = nm ∨ b = brk))) :
    (movUndo m' jr nm brk h).entry j b = m'.entry j b := by
  rw [movUndo_entry]
  have h1 : ¬ (j = jr ∧ b = nm) := fun ⟨a, c⟩ => hb ⟨a, Or.inl c⟩
  have h2 : ¬ (j = jr ∧ b = brk) := fun ⟨a, c⟩ => hb ⟨a, Or.inr c⟩
  simp only [h1, h2, ite_false]

/-- The entries of a directory other than the area's, with the rename undone. -/
theorem entsOf_movUndo {m' : Tree} {jr : Ino} {nm brk : GoString} {h : NamesH} {j : Ino}
    (hj : j ≠ jr) : entsOf (movUndo m' jr nm brk h) j = entsOf m' j := by
  apply GMap.ext; intro b
  rw [entsOf_entry, entsOf_entry]
  exact movUndo_entry_other (fun ⟨e, _⟩ => hj e)

/-- **A crash keeping the rename** keeps every earlier entry of the coherent claim; with the rename
undone it is a crash of the claims before it, and `nm` holds nothing. -/
theorem regionCrashedK_moved_keep {cl : List Claim} {n : Nat} {m' : Tree} {K : Nat → Prop}
    {jr : Ino} {N : NameSet} {h : NamesH} {x st : Nat} {nm brk : GoString} {J : Ino}
    (H : MovedHyp cl jr N h st nm brk J)
    (hK : RegionCrashedK (movClaims cl jr N h x st nm brk J) n m' K) (hx : K x) :
    RegionCrashedK cl n (movUndo m' jr nm brk h) K ∧ m'.entry jr nm = none := by
  classical
  unfold movClaims at hK
  generalize he : movEnt jr J nm brk h st = e at hK
  generalize hcd : movCur N h nm brk J = c at hK
  have hc1 : ((jr, N, h.log x e c) : Claim) ∈ replClaim (jr, N, h) (jr, N, h.log x e c) cl :=
    mem_replClaim_new H.mem
  have hst : e.start = st := by rw [← he]; rfl
  have hold : ∀ xe ∈ h.ents, K xe.1 := by
    intro xe hxe
    exact hK.1 _ hc1 _ hc1 x e c xe.1 xe.2.1 xe.2.2 (by simp [NamesH.log])
      (by simp [NamesH.log, hxe]) hx (Nat.lt_of_lt_of_le (H.coh.1 xe hxe) (by rw [hst]; exact H.start))
  let f : Claim → Claim := fun c' => if c' = (jr, N, h) then (jr, N, h.log x e c) else c'
  have hfm : ∀ c' ∈ cl, f c' ∈ replClaim (jr, N, h) (jr, N, h.log x e c) cl := fun c' hc' =>
    mem_replClaim hc'
  have hfe : ∀ c' y, y ∈ c'.2.2.ents → y ∈ (f c').2.2.ents := fun c' y hy => by
    simp only [f]; split
    · rename_i hc'; subst hc'; simp [NamesH.log, hy]
    · exact hy
  obtain ⟨h1, h2, h3⟩ := hK
  have hwnm : e.op.Writes jr nm := by rw [← he]; exact (movEnt_writes _ _ _ _ _ _ _ _).2 ⟨rfl, Or.inl rfl⟩
  refine ⟨⟨fun c1 hc1' c2 hc2 x' e' E y e'' E' hx' hy hKx hlt => ?_, fun c1 hc1' y e' E hy hlt => ?_,
    fun c1 hc1' b hb => ?_⟩, ?_⟩
  · exact h1 (f c1) (hfm c1 hc1') (f c2) (hfm c2 hc2) x' e' E y e'' E'
      (hfe c1 _ hx') (hfe c2 _ hy) hKx hlt
  · exact h2 (f c1) (hfm c1 hc1') y e' E (hfe c1 _ hy) hlt
  · have h3' := h3 (f c1) (hfm c1 hc1')
    by_cases hcc : c1 = (jr, N, h)
    · subst hcc
      simp only [f, ite_true] at h3'
      simp only at hb ⊢
      rw [movUndo_entry]
      by_cases hbn : b = nm
      · subst hbn
        simp only [and_self, ite_true]
        rw [H.coh.2 K hold b hb]
      · by_cases hbt : b = brk
        · subst hbt
          simp only [hbn, and_false, ite_false, and_self, ite_true]
          rw [H.coh.2 K hold b hb]
        · simp only [hbn, hbt, and_false, ite_false]
          rw [h3' b hb]
          refine valAfter_log_notWrites _ _ _ _ _ _ _ (fun hw => ?_)
          rw [← he] at hw
          rcases ((movEnt_writes _ _ _ _ _ _ _ _).1 hw).2 with h' | h'
          · exact hbn h'
          · exact hbt h'
    · simp only [f, hcc, ite_false] at h3'
      rw [movUndo_entry_other]
      · exact h3' b hb
      · rintro ⟨hj, hb' | hb'⟩
        · exact (H.others c1 hc1' hcc hj).1 (hb' ▸ hb)
        · exact (H.others c1 hc1' hcc hj).2 (hb' ▸ hb)
  · have := h3 _ hc1 nm H.nmN
    simp only at this
    rw [this, valAfter_log_last _ _ _ _ _ _ _ hx hwnm, ← hcd]
    unfold movCur
    rw [restrictN_lookup _ _ _ H.nmN, GMap.lookup_insert_ne _ _ (Ne.symm H.ne), GMap.lookup_delete_eq]

/-- **A crash of the claims after the rename**: of the claims before it, or, the rename kept, with the
rename undone, `nm` holding nothing. -/
theorem regionCrashed_moved {cl : List Claim} {n : Nat} {m' : Tree}
    {jr : Ino} {N : NameSet} {h : NamesH} {x st : Nat} {nm brk : GoString} {J : Ino}
    (H : MovedHyp cl jr N h st nm brk J) (hr : RegionCrashed (movClaims cl jr N h x st nm brk J) n m') :
    RegionCrashed cl n m' ∨ (RegionCrashed cl n (movUndo m' jr nm brk h) ∧ m'.entry jr nm = none) := by
  obtain ⟨K, hK⟩ := (regionCrashed_iff _ _ _).1 hr
  by_cases hx : K x
  · obtain ⟨hK', hn⟩ := regionCrashedK_moved_keep H hK hx
    exact Or.inr ⟨(regionCrashed_iff _ _ _).2 ⟨K, hK'⟩, hn⟩
  · exact Or.inl ((regionCrashed_iff _ _ _).2 ⟨K, regionCrashedK_unlog cl n m' K jr N h x _ _ hK hx⟩)

/-! ## The invariant's facts after the rename -/

/-- **Another WAL's crash condition** (its name neither `nm` nor `brk`, its directory not the area's;
its alternative, if any, on the same names). -/
theorem crashOkA_moved_other {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {alt : Option WalLay} {cl : List Claim} {n : Nat}
    {jr : Ino} {N : NameSet} {h : NamesH} {x st : Nat} {nm brk : GoString} {J : Ino}
    (H : MovedHyp cl jr N h st nm brk J) (hok : CrashOkA C Mr d lay alt cl n)
    (halt : ∀ lay0, alt = some lay0 → lay0.jr = lay.jr ∧ lay0.nm = lay.nm ∧ lay0.j = lay.j)
    (hjr : lay.jr = jr) (h1 : lay.nm ≠ nm) (h2 : lay.nm ≠ brk) (hj : lay.j ≠ jr) :
    CrashOkA C Mr d lay alt (movClaims cl jr N h x st nm brk J) n := by
  intro m' fo hr hf hn hw
  rcases regionCrashed_moved H hr with hr' | ⟨hr', -⟩
  · exact hok m' fo hr' hf hn hw
  · have hwi : entsOf (movUndo m' jr nm brk h) lay.j = entsOf m' lay.j := entsOf_movUndo hj
    have hent : (movUndo m' jr nm brk h).entry lay.jr lay.nm = m'.entry lay.jr lay.nm :=
      movUndo_entry_other (fun ⟨_, hb⟩ => hb.elim h1 h2)
    rcases hok _ fo hr' hf (fun g hg hin => hn g hg (by rw [← hwi]; exact hin)) (by rw [hwi]; exact hw)
      with hct | ⟨lay0, h0, hct⟩
    · exact Or.inl (crashTo_congr hent (by rw [hwi]) hct)
    · obtain ⟨e1, e2, e3⟩ := halt lay0 h0
      refine Or.inr ⟨lay0, h0, crashTo_congr ?_ (by rw [e3, hwi]) hct⟩
      rw [e1, e2]; exact hent

/-- **The renamed WAL's crash condition**: unnamed, a crash keeping the rename leaves its name
empty (`CrashTo`'s left disjunct); one dropping it is a crash of the claims before. -/
theorem crashOkA_moved_self {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {alt : Option WalLay} {cl : List Claim} {n : Nat}
    {jr : Ino} {N : NameSet} {h : NamesH} {x st : Nat} {nm brk : GoString} {J : Ino}
    (H : MovedHyp cl jr N h st nm brk J) (hok : CrashOkA C Mr d lay alt cl n)
    (hjr : lay.jr = jr) (hnm : lay.nm = nm) (hnamed : d.named = false) :
    CrashOkA C Mr d lay alt (movClaims cl jr N h x st nm brk J) n := by
  intro m' fo hr hf hn hw
  rcases regionCrashed_moved H hr with hr' | ⟨-, hnone⟩
  · exact hok m' fo hr' hf hn hw
  · exact Or.inl (Or.inl ⟨hnamed, by rw [hjr, hnm]; exact hnone⟩)

theorem crashOkW_moved {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {cl : List Claim} {n : Nat}
    {jr : Ino} {N : NameSet} {h : NamesH} {x st : Nat} {nm brk : GoString} {J : Ino}
    (H : MovedHyp cl jr N h st nm brk J) (hok : CrashOkW C Mr d lay cl n) (hjr : lay.jr = jr)
    (hj : lay.j ≠ jr) (hcase : (lay.nm = nm ∧ d.named = false) ∨ (lay.nm ≠ nm ∧ lay.nm ≠ brk)) :
    CrashOkW C Mr d lay (movClaims cl jr N h x st nm brk J) n := by
  obtain ⟨alt, halt, hc⟩ := hok
  refine ⟨alt, halt, ?_⟩
  rcases hcase with ⟨e, hn⟩ | ⟨h1, h2⟩
  · exact crashOkA_moved_self H hc hjr e hn
  · refine crashOkA_moved_other H hc (fun lay0 h0 => ?_) hjr h1 h2 hj
    obtain ⟨-, e1, e2, e3, -⟩ := halt lay0 h0
    exact ⟨e1, e2, e3⟩

/-- The claims of another directory than the area's are those before. -/
theorem mem_movClaims_ne {cl : List Claim} {jr : Ino} {N : NameSet} {h : NamesH} {x st : Nat}
    {nm brk : GoString} {J : Ino} {c : Claim} (hc : c.1 ≠ jr) :
    c ∈ movClaims cl jr N h x st nm brk J ↔ c ∈ cl := by
  unfold movClaims
  constructor
  · intro hm
    rcases mem_replClaim_cases hm with rfl | ⟨hm, -⟩
    · exact absurd rfl hc
    · exact hm
  · intro hm
    exact mem_replClaim_of_ne hm (fun e => hc (by rw [e]))

theorem walDirClaim_moved {cl : List Claim} {jr : Ino} {N : NameSet} {h : NamesH} {x st : Nat}
    {nm brk : GoString} {J : Ino} {j : Ino} {hj : NamesH} (hne : j ≠ jr) :
    WalDirClaim j hj (movClaims cl jr N h x st nm brk J) ↔ WalDirClaim j hj cl := by
  constructor
  · rintro ⟨X, hX, hm, hco⟩
    exact ⟨X, hX, (mem_movClaims_ne (c := (j, .except X, hj)) hne).1 hm, hco⟩
  · rintro ⟨X, hX, hm, hco⟩
    exact ⟨X, hX, (mem_movClaims_ne (c := (j, .except X, hj)) hne).2 hm, hco⟩

/-- A layout of another WAL is at another name than `nm`, and than `brk` (no WAL name). -/
theorem moved_other_names {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {dir nm brk : GoString}
    (hok : WalsOk C Mr R jr s Ls cl n) (hin : InArea s.area dir nm) (hbrk : ¬ walNameOk brk)
    {dir' : GoString} {lay' : WalLay} (hl' : Ls !! dir' = some lay') (hdd : dir' ≠ dir) :
    lay'.nm ≠ nm ∧ lay'.nm ≠ brk := by
  obtain ⟨d', hd'⟩ : ∃ d', s.wal !! dir' = some d' := by
    cases hw : s.wal !! dir' with
    | none => rw [hok.2.1 dir' hw] at hl'; cases hl'
    | some d' => exact ⟨d', rfl⟩
  obtain ⟨lay'', nm', -, hl'', hin', -, hnm', -⟩ := hok.1 dir' d' hd'
  rw [hl'] at hl''; cases hl''
  rw [hnm']
  exact ⟨inArea_ne hin hin' hdd, fun e => hbrk (e ▸ hin'.1)⟩

/-- The pinned claim's names after the rename, off `nm` and `brk`. -/
theorem movCur_other {N : NameSet} {h : NamesH} {nm brk b : GoString} {J : Ino} (hN : N.Mem b)
    (h1 : b ≠ nm) (h2 : b ≠ brk) : movCur N h nm brk J !! b = h.cur !! b := by
  unfold movCur
  rw [restrictN_lookup _ _ _ hN, GMap.lookup_insert_ne _ _ (Ne.symm h2), GMap.lookup_delete_ne _ (Ne.symm h1)]

/-- **Strong absence after the rename**: the WAL-less names are neither `nm` (its WAL is present) nor
`brk` (no WAL name). -/
theorem absentNone_moved {s : AbsDiskState} {jr : Ino} {cl : List Claim} {n : Nat}
    {N : NameSet} {h : NamesH} {x st : Nat} {dir nm brk : GoString} {J : Ino}
    (H : MovedHyp cl jr N h st nm brk J) (han : AbsentNone s jr cl n)
    (hin : InArea s.area dir nm) (hpres : s.wal !! dir ≠ none) (hbrk : ¬ walNameOk brk) :
    AbsentNone s jr (movClaims cl jr N h x st nm brk J) n := by
  intro dir' nm' hia hn
  have hn1 : nm' ≠ nm := by
    rintro rfl
    have : dir' = dir := hia.2.trans hin.2.symm
    subst this; exact hpres hn
  have hn2 : nm' ≠ brk := fun e => hbrk (e ▸ hia.1)
  obtain ⟨h1, h2⟩ := han dir' nm' hia hn
  refine ⟨fun N0 h0 hm hN => ?_, fun m' hr => ?_⟩
  · unfold movClaims at hm
    rcases mem_replClaim_cases hm with he | ⟨hm', -⟩
    · simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl, rfl⟩ := he
      simp only [NamesH.log]
      rw [movCur_other hN hn1 hn2]
      exact h1 N0 h H.mem hN
    · exact h1 N0 h0 hm' hN
  · rcases regionCrashed_moved H hr with hr' | ⟨hr', -⟩
    · exact h2 m' hr'
    · rw [← movUndo_entry_other (m' := m') (jr := jr) (nm := nm) (brk := brk) (h := h) (j := jr)
        (b := nm') (fun ⟨_, hb⟩ => hb.elim hn1 hn2)]
      exact h2 _ hr'

/-- **The durable directories after the rename** (they resolve through neither `nm` nor `brk`). -/
theorem dirsOk_moved {R : Roots} {s : AbsDiskState} {jr : Ino} {cl : List Claim} {n : Nat}
    {N : NameSet} {h : NamesH} {x st : Nat} {nm brk : GoString} {J : Ino}
    (H : MovedHyp cl jr N h st nm brk J) (hdo : DirsOk R s cl n) (hav : DirsAvoid R jr s)
    (hnmS : AreaSlot nm) (hbS : AreaSlot brk) :
    DirsOk R s (movClaims cl jr N h x st nm brk J) n := by
  intro dd hdd m' hr
  rcases regionCrashed_moved H hr with hr' | ⟨hr', -⟩
  · exact hdo dd hdd m' hr'
  · obtain ⟨J', hJ'⟩ := hdo dd hdd _ hr'
    refine ⟨J', ?_⟩
    rw [← hav dd hdd (movUndo m' jr nm brk h) m' (fun j b hjb => movUndo_entry_other
      (fun ⟨h1, h2⟩ => hjb ⟨h1, h2.elim (fun e => e ▸ hnmS) (fun e => e ▸ hbS)⟩))]
    exact hJ'

/-- **`WalsOk` after the rename** (the WAL in `dir`, named `nm`, present and unnamed). -/
theorem walsOk_moved {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat}
    {N : NameSet} {h : NamesH} {x st : Nat} {dir nm brk : GoString} {J : Ino}
    (H : MovedHyp cl jr N h st nm brk J) (hok : WalsOk C Mr R jr s Ls cl n) (hA : WalsAt jr Ls cl)
    (han : AbsentNone s jr cl n) (hav : DirsAvoid R jr s)
    (hin : InArea s.area dir nm) (hpres : s.wal !! dir ≠ none)
    (hnamed : ∀ d, s.wal !! dir = some d → d.named = false)
    (hbrk : ¬ walNameOk brk) (hbS : AreaSlot brk) :
    WalsOk C Mr R jr s Ls (movClaims cl jr N h x st nm brk J) n := by
  have hok0 := hok
  obtain ⟨hw, hnone, hnd, hcut, -, hdirs⟩ := hok
  refine ⟨fun dir' d' hd' => ?_, hnone, hnd, hcut,
    absentOk_of_absentNone (absentNone_moved H han hin hpres hbrk),
    dirsOk_moved H hdirs hav ⟨nm, hin.1, .inl rfl⟩ hbS⟩
  obtain ⟨lay, nm', hj, hl, hia, hjr, hnm, hwd, hab, hco⟩ := hw dir' d' hd'
  have hjne := hA.ne hl
  refine ⟨lay, nm', hj, hl, hia, hjr, hnm, (walDirClaim_moved (hA.ne hl)).2 hwd, hab,
    hco.1, crashOkW_moved H hco.2.1 hjr hjne ?_, hco.2.2⟩
  by_cases hdd : dir' = dir
  · subst hdd
    left
    have e : nm' = nm := List.append_cancel_left (hia.2.symm.trans hin.2)
    exact ⟨hnm.trans e, hnamed d' hd'⟩
  · right
    have := moved_other_names hok0 hin hbrk hl hdd
    exact this

/-- **`WalsCreateOk` after the rename** (the claim keeps its names). -/
theorem walsCreateOk_moved {jr : Ino} {cl : List Claim} {N : NameSet} {h : NamesH} {x st : Nat}
    {nm brk : GoString} {J : Ino} (hw : WalsCreateOk jr cl) :
    WalsCreateOk jr (movClaims cl jr N h x st nm brk J) := by
  classical
  intro nm' hnm'
  obtain ⟨N', h', hc, hN⟩ := hw nm' hnm'
  unfold movClaims
  by_cases hcc : (jr, N', h') = (jr, N, h)
  · simp only [Prod.mk.injEq] at hcc
    obtain ⟨-, rfl, rfl⟩ := hcc
    exact ⟨N', _, mem_replClaim_new hc, hN⟩
  · exact ⟨N', h', mem_replClaim_of_ne hc hcc, hN⟩

/-- **`WalsNamed` after the rename** (the WAL directories' claims and entries unchanged). -/
theorem walsNamed_moved {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {jr : Ino}
    {N : NameSet} {h : NamesH} {x st : Nat} {nm brk : GoString} {J : Ino}
    (H : MovedHyp cl jr N h st nm brk J) (hA : WalsAt jr Ls cl) (hok : WalsNamed Ls cl n) :
    WalsNamed Ls (movClaims cl jr N h x st nm brk J) n := by
  intro dir lay hl
  obtain ⟨h1, h2, h3⟩ := hok dir lay hl
  refine ⟨fun hj hw => h1 hj ((walDirClaim_moved (hA.ne hl)).1 hw), fun m' hr => ?_,
    fun N' hj hm => h3 N' hj ((mem_movClaims_ne (c := (lay.j, N', hj)) (hA.ne hl)).1 hm)⟩
  rcases regionCrashed_moved H hr with hr' | ⟨hr', -⟩
  · exact h2 m' hr'
  · have := h2 _ hr'
    rwa [entsOf_movUndo (hA.ne hl)] at this

/-- **`DirKeysOk` after the rename** (the keyed claims are of other directories than the area's). -/
theorem dirKeysOk_moved {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat}
    {K : GMap GoString (Ino × List GoString)} {c : Option GoString}
    {N : NameSet} {h : NamesH} {x st : Nat} {dir nm brk : GoString} {J : Ino}
    (H : MovedHyp cl jr N h st nm brk J) (hwo : WalsOk C Mr R jr s Ls cl n) (hA : WalsAt jr Ls cl)
    (hin : InArea s.area dir nm) (hnamed : ∀ d, s.wal !! dir = some d → d.named = false)
    (hbrk : ¬ walNameOk brk) (hok : DirKeysOk C Mr jr s Ls cl n K c) :
    DirKeysOk C Mr jr s Ls (movClaims cl jr N h x st nm brk J) n K c := by
  have hne0 : ∀ c' : Claim, c'.1 ≠ jr → c' ≠ (jr, N, h) := fun c' hc e => hc (by rw [e])
  have hne1 : ∀ c' : Claim, c'.1 ≠ jr →
      c' ≠ (jr, N, h.log x (movEnt jr J nm brk h st) (movCur N h nm brk J)) :=
    fun c' hc e => hc (by rw [e])
  obtain ⟨h1, h2, h3⟩ := hok
  refine ⟨fun dir' j X hk => ?_, fun dir' d lay hd hl hcc => ?_,
    h3.mono_cl (fun _ lay _ X hj ⟨hjr, hX, ho, hco, hoth⟩ => ⟨hjr, hX,
      claimOnce_repl_other ho (hne0 _ hjr) (hne1 _ hjr), hco,
      fun c' hc' hne hj' => hoth c' ((mem_movClaims_ne (by rw [hj']; exact hjr)).1 hc') hne hj'⟩)
      fun _ _ _ _ _ hD c' hc' hj' _ => (mem_movClaims_ne (by rw [hj']; exact hD.1)).1 hc'⟩
  · obtain ⟨lay, hj, hl, hlj, hjr, hX, ho, hco, hoth⟩ := h1 dir' j X hk
    refine ⟨lay, hj, hl, hlj, hjr, hX, claimOnce_repl_other ho (hne0 _ hjr) (hne1 _ hjr), hco,
      fun c' hc' hne hj' => ?_⟩
    exact hoth c' ((mem_movClaims_ne (by rw [hj']; exact hjr)).1 hc') hne hj'
  · have hc0 := h2 dir' d lay hd hl hcc
    obtain ⟨lay', nm', -, hl', hia, hjr, hnm, -⟩ := hwo.1 dir' d hd
    rw [hl] at hl'; cases hl'
    by_cases hdd : dir' = dir
    · subst hdd
      have e : nm' = nm := List.append_cancel_left (hia.2.symm.trans hin.2)
      exact crashOkA_moved_self H hc0 hjr (hnm.trans e) (hnamed d hd)
    · obtain ⟨n1, n2⟩ := moved_other_names hwo hin hbrk hl hdd
      have hjne := hA.ne hl
      exact crashOkA_moved_other H hc0 (fun _ h0 => by cases h0) hjr n1 n2 hjne

/-- **`WalsAt` after the rename**: the renamed WAL's name holds nothing in the logged claim. -/
theorem walsAt_moved {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat}
    {N : NameSet} {h : NamesH} {x st : Nat} {dir nm brk : GoString} {J : Ino}
    (hwo : WalsOk C Mr R jr s Ls cl n) (hA : WalsAt jr Ls cl)
    (hin : InArea s.area dir nm) (hbrk : ¬ walNameOk brk) (hne : nm ≠ brk) (hc : (jr, N, h) ∈ cl) :
    WalsAt jr Ls (movClaims cl jr N h x st nm brk J) := by
  intro dir' lay hl
  refine ⟨hA.ne hl, fun N' h' hm hN => ?_⟩
  unfold movClaims at hm
  rcases mem_replClaim_cases hm with he | ⟨hm', -⟩
  · simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl, rfl⟩ := he
    simp only [NamesH.log]
    by_cases hdd : dir' = dir
    · subst hdd
      right
      obtain ⟨d, hd⟩ : ∃ d, s.wal !! dir' = some d := by
        cases hw : s.wal !! dir' with
        | none => rw [hwo.2.1 dir' hw] at hl; cases hl
        | some d => exact ⟨d, rfl⟩
      obtain ⟨lay', nm', -, hl', hia, -, hnm, -⟩ := hwo.1 dir' d hd
      rw [hl] at hl'; cases hl'
      have e : lay.nm = nm := hnm.trans (List.append_cancel_left (hia.2.symm.trans hin.2))
      rw [e]
      unfold movCur
      rw [restrictN_lookup _ _ _ (e ▸ hN), GMap.lookup_insert_ne _ _ (Ne.symm hne),
        GMap.lookup_delete_eq]
    · obtain ⟨n1, n2⟩ := moved_other_names hwo hin hbrk hl hdd
      rw [movCur_other hN n1 n2]
      exact hA.at hl hc hN
  · exact hA.at hl hm' hN

end pure

end WalFs
end EtcdGrove
end Perennial

end
