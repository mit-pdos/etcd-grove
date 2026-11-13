/- Lean-first (no Rocq counterpart).

# The parked state's moves (W3/W5's gaps A and B; `notes/wal-fsext-plan.md`, W1 log, ninth session)

`walParked` (`Inv.lean`) holds the program's halves of the WALs' segments, of the WAL directories'
claims and of the pipeline names' claims, but those a holder took out, which the record of what is out
(`WalOut`, `Ghost.lean`) lists: the invariant holds half of the record (`walOutAuth`), the holder the
other (`walOutFrag`; the lock token holds it empty). Every move below updates both halves of the record
with what it moves, so a put-back knows that what it returns is exactly what is out:

* the lock (`walParked_lock`: nothing is out, so no change is in flight, gap B), the unlock
  (`walParked_unlock`: the empty record back to the lock token);
* taking out (`Open`'s pin): `walParked_takeSeg`/`_takeSegs` (a parked segment is idle, gap B: its
  halves are the layout's by agreement with the invariant's), `walParked_takeClaim`,
  `walParked_takeTmps`;
* putting back (`openAtIndex`'s error arms, a failed `ReadAll`, `Close`): `walParked_putSeg` (the
  segment idle), `walParked_putClaim`, `walParked_putTmps`;
* the tail's steps (`TailAcc.lean`'s `walParked_tail`, over `walParkedIn`: the tail is out, either a
  change is in flight on it, gap B, or the caller holds its half besides the invariant's, so the
  parked one would be a third), a cut's rename (`CutAuLemmas.lean`'s `walParked_cut`), `Create`'s commit
  (`CreateKeys.lean`'s `walParked_create`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CrashPure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section parked
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- Two parts of an `OsMeta` agree. -/
theorem parked_osMeta_agree (i : Ino) (dq1 dq2 : DFrac) (m1 m2 : OsMeta) :
    ⊢@{IProp GF} osMeta (L := L) i dq1 m1 -∗ osMeta (L := L) i dq2 m2 -∗ ⌜m1 = m2⌝ := by
  unfold osMeta
  iintro H1 H2
  icases gElem_valid_2 _ _ _ _ _ _ _ $$ H1 H2 with %hv
  ipureintro; exact hv.2

/-- Three halves of an `OsMeta`: impossible. -/
theorem osMeta_three_halves (i : Ino) (m1 m2 m3 : OsMeta) :
    ⊢@{IProp GF} osMeta (L := L) i (DFrac.own (1 : Qp).half) m1 -∗
      osMeta (L := L) i (DFrac.own (1 : Qp).half) m2 -∗
      osMeta (L := L) i (DFrac.own (1 : Qp).half) m3 -∗ False := by
  iintro H1 H2 H3
  icases parked_osMeta_agree i _ _ m1 m2 $$ H1 H2 with %e
  subst e
  ihave H := (osMeta_halves (L := L) i m1).2 $$ [H1 H2]
  · iframe H1 H2
  unfold osMeta
  icases gElem_valid_2 _ _ _ _ _ _ _ $$ H H3 with %hv
  exfalso
  have := DFrac.valid_own_op hv.1
  simp at this

/-! ## The parked segments, generically -/

theorem segP_weaken {O O' : List Ino} (x : SegG) (h : x.ino ∈ O → x.ino ∈ O') :
    (if x.ino ∈ O then emp else segResP (L := L) x : IProp GF) ⊢
      if x.ino ∈ O' then emp else segResP (L := L) x := by
  by_cases h' : x.ino ∈ O'
  · rw [if_pos h']; iintro -; iempintro
  · rw [if_neg h', if_neg (fun hm => h' (h hm))]

theorem segP_congr {O O' : List Ino} (x : SegG) (h : x.ino ∈ O ↔ x.ino ∈ O') :
    (if x.ino ∈ O then emp else segResP (L := L) x : IProp GF) ⊢
      if x.ino ∈ O' then emp else segResP (L := L) x :=
  segP_weaken x h.1

/-- **A parked segment taken out** (its inode into `O`). -/
theorem segsP_take (S : List SegG) (O : List Ino) (g : SegG) (hg : g ∈ S) (hO : g.ino ∉ O) :
    ([∗list] x ∈ S, if x.ino ∈ O then emp else segResP (L := L) x) ⊢
      segResP (L := L) g ∗ [∗list] x ∈ S, if x.ino ∈ g.ino :: O then emp else segResP (L := L) x := by
  induction S with
  | nil => cases hg
  | cons y ys ih =>
    iintro H
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ H with ⟨Hy, Hys⟩
    by_cases hy : y = g
    · subst hy
      rw [if_neg hO]
      iframe Hy
      iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
      isplitr
      · rw [if_pos (List.mem_cons_self ..)]; iempintro
      iapply BigSepL.bigSepL_mono (fun {k x} _ => segP_weaken (L := L) x
        (fun h => List.mem_cons_of_mem _ h)) $$ Hys
    · have hg' : g ∈ ys := (List.mem_cons.1 hg).resolve_left (Ne.symm hy)
      icases ih hg' $$ Hys with ⟨Hg, Hys⟩
      iframe Hg
      iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
      iframe Hys
      iapply segP_weaken (L := L) y (fun h => List.mem_cons_of_mem _ h) $$ Hy

/-- **A segment put back** (its inode off `O`), the inodes distinct. -/
theorem segsP_put (S : List SegG) (O : List Ino) (g : SegG) (hg : g ∈ S)
    (hnd : (S.map (·.ino)).Nodup) :
    ([∗list] x ∈ S, if x.ino ∈ O then emp else segResP (L := L) x) ∗ segResP (L := L) g ⊢
      [∗list] x ∈ S, if x.ino ∈ O.filter (· ≠ g.ino) then emp else segResP (L := L) x := by
  induction S with
  | nil => cases hg
  | cons y ys ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    iintro ⟨H, Hg⟩
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ H with ⟨Hy, Hys⟩
    iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
    by_cases hy : y = g
    · subst hy
      rw [if_neg (show y.ino ∉ O.filter (· ≠ y.ino) by simp)]
      iframe Hg
      iapply BigSepL.bigSepL_mono (fun {k x} hk => segP_congr (L := L) x ?_) $$ Hys
      have hx : x.ino ≠ y.ino := fun e =>
        hnd.1 (e ▸ List.mem_map_of_mem (f := (·.ino)) (List.mem_of_getElem? hk))
      simp [hx]
    · have hg' : g ∈ ys := (List.mem_cons.1 hg).resolve_left (Ne.symm hy)
      have hyg : y.ino ≠ g.ino := fun e => hnd.1 (e ▸ List.mem_map_of_mem (f := (·.ino)) hg')
      isplitl [Hy]
      · iapply segP_congr (L := L) y (by simp [hyg]) $$ Hy
      iapply ih hg' hnd.2
      iframe Hys Hg

/-- **A segment's two halves outside**: a parked entry of its inode would be a third, so its inode is
out. -/
theorem segsP_meta (S : List SegG) (O : List Ino) (i : Ino) (m1 m2 : OsMeta) :
    ([∗list] x ∈ S, if x.ino ∈ O then emp else segResP (L := L) x) ∗
        osMeta (L := L) i (DFrac.own (1 : Qp).half) m1 ∗ osMeta (L := L) i (DFrac.own (1 : Qp).half) m2 ⊢
      ([∗list] x ∈ S, if x.ino ∈ O then emp else segResP (L := L) x) ∗
        osMeta (L := L) i (DFrac.own (1 : Qp).half) m1 ∗ osMeta (L := L) i (DFrac.own (1 : Qp).half) m2 ∗
        ⌜∀ x ∈ S, x.ino = i → i ∈ O⌝ := by
  classical
  by_cases h : ∀ x ∈ S, x.ino = i → i ∈ O
  · iintro ⟨H, H1, H2⟩
    iframe H H1 H2
    ipureintro; exact h
  · have h' : ∃ x ∈ S, x.ino = i ∧ i ∉ O := Classical.byContradiction fun hc =>
      h fun x hx hxi => Classical.byContradiction fun hi => hc ⟨x, hx, hxi, hi⟩
    obtain ⟨x, hx, hxi, hiO⟩ := h'
    subst hxi
    iintro ⟨H, H1, H2⟩
    iexfalso
    ihave Hx := (BigSepL.bigSepL_mem (Φ := fun x => iprop(if x.ino ∈ O then emp else
      segResP (L := L) x)) hx) $$ H
    rw [if_neg hiO]
    unfold segResP
    icases Hx with ⟨%m, %bs, Hm, -, -⟩
    iapply osMeta_three_halves (L := L) x.ino m1 m2 m $$ H1 H2 Hm

/-! ## The parked claims, generically -/

theorem claimP_weaken {Ls : GMap GoString WalLay} {D D' : List (Ino × NameSet)} (c : Claim)
    (h : ParkedClaim Ls D' c → ParkedClaim Ls D c) :
    (if ParkedClaim Ls D c then osNames (L := L) c.1 c.2.1 (DFrac.own (1 : Qp).half) c.2.2 else emp :
        IProp GF) ⊢
      if ParkedClaim Ls D' c then osNames (L := L) c.1 c.2.1 (DFrac.own (1 : Qp).half) c.2.2 else emp := by
  by_cases h' : ParkedClaim Ls D' c
  · rw [if_pos h', if_pos (h h')]
  · rw [if_neg h']; iintro -; iempintro

/-- **A parked claim taken out** (its key into `D`). -/
theorem claimsP_take (Ls : GMap GoString WalLay) (cl : List Claim) (D : List (Ino × NameSet))
    (c : Claim) (hc : c ∈ cl) (hP : ParkedClaim Ls D c) :
    ([∗list] x ∈ cl, if ParkedClaim Ls D x then
        osNames (L := L) x.1 x.2.1 (DFrac.own (1 : Qp).half) x.2.2 else emp) ⊢
      osNames (L := L) c.1 c.2.1 (DFrac.own (1 : Qp).half) c.2.2 ∗
      [∗list] x ∈ cl, if ParkedClaim Ls ((c.1, c.2.1) :: D) x then
        osNames (L := L) x.1 x.2.1 (DFrac.own (1 : Qp).half) x.2.2 else emp := by
  have hw : ∀ x : Claim, ParkedClaim Ls ((c.1, c.2.1) :: D) x → ParkedClaim Ls D x :=
    fun x hx => ⟨hx.1, fun hm => hx.2 (List.mem_cons_of_mem _ hm)⟩
  induction cl with
  | nil => cases hc
  | cons y ys ih =>
    iintro H
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ H with ⟨Hy, Hys⟩
    by_cases hy : y = c
    · subst hy
      rw [if_pos hP]
      iframe Hy
      iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
      isplitr
      · rw [if_neg (fun hp => hp.2 (List.mem_cons_self ..))]; iempintro
      iapply BigSepL.bigSepL_mono (fun {k x} _ => claimP_weaken (L := L) x (hw x)) $$ Hys
    · have hc' : c ∈ ys := (List.mem_cons.1 hc).resolve_left (Ne.symm hy)
      icases ih hc' $$ Hys with ⟨Hc, Hys⟩
      iframe Hc
      iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
      iframe Hys
      iapply claimP_weaken (L := L) y (hw y) $$ Hy

/-- **A claim put back** (its key off `D`): the claim once in `cl`, no other of its key. -/
theorem claimsP_put (Ls : GMap GoString WalLay) (l1 l2 : List Claim) (D : List (Ino × NameSet))
    (c : Claim) (hkey : ∀ c' ∈ l1 ++ l2, (c'.1, c'.2.1) ≠ (c.1, c.2.1)) :
    ([∗list] x ∈ l1 ++ c :: l2, if ParkedClaim Ls D x then
        osNames (L := L) x.1 x.2.1 (DFrac.own (1 : Qp).half) x.2.2 else emp) ∗
      osNames (L := L) c.1 c.2.1 (DFrac.own (1 : Qp).half) c.2.2 ⊢
      [∗list] x ∈ l1 ++ c :: l2, if ParkedClaim Ls (D.filter (· ≠ (c.1, c.2.1))) x then
        osNames (L := L) x.1 x.2.1 (DFrac.own (1 : Qp).half) x.2.2 else emp := by
  have hiff : ∀ x ∈ l1 ++ l2, ParkedClaim Ls (D.filter (· ≠ (c.1, c.2.1))) x ↔ ParkedClaim Ls D x := by
    intro x hx
    unfold ParkedClaim
    have hne := hkey x hx
    simp [hne]
  iintro ⟨H, Hc⟩
  icases (BigSepL.bigSepL_append (PROP := IProp GF)).1 $$ H with ⟨H1, H2⟩
  icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ H2 with ⟨-, H2⟩
  iapply (BigSepL.bigSepL_append (PROP := IProp GF)).2
  isplitl [H1]
  · iapply BigSepL.bigSepL_mono (fun {k x} hk => claimP_weaken (L := L) x
      (hiff x (List.mem_append_left _ (List.mem_of_getElem? hk))).1) $$ H1
  iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
  isplitl [Hc]
  · by_cases hP : ParkedClaim Ls (D.filter (· ≠ (c.1, c.2.1))) c
    · rw [if_pos hP]; iexact Hc
    · rw [if_neg hP]; iclear Hc; iempintro
  iapply BigSepL.bigSepL_mono (fun {k x} hk => claimP_weaken (L := L) x
    (hiff x (List.mem_append_right _ (List.mem_of_getElem? hk))).1) $$ H2

/-! ## The moves -/

/-- **`walParked` with the inode `i` known out** (`walParked_tail`'s premise, `TailAcc.lean`). -/
def walParkedIn (Ls : GMap GoString WalLay) (cl : List Claim) (F : GMap Ino SegFl) (i : Ino) :
    IProp GF :=
  iprop(∃ (b : Bool) (o : WalOut), walParkAuth (W := W) b ∗ walOutAuth (W := W) o ∗
    ⌜(∀ i, F !! i ≠ none → i ∈ o.O) ∧ i ∈ o.O⌝ ∗
    ([∗list] g ∈ segsAll Ls, if g.ino ∈ o.O then emp else segResP (L := L) g) ∗
    ([∗list] c ∈ cl, if ParkedClaim Ls o.D c then
      osNames (L := L) c.1 c.2.1 (DFrac.own (1 : Qp).half) c.2.2 else emp) ∗
    walTmpParked (G := G) (L := L) Ls o.T)

/-- A change in flight on `i`: `i` is out (gap B). -/
theorem walParkedIn_of_fl (Ls : GMap GoString WalLay) (cl : List Claim) (F : GMap Ino SegFl)
    (i : Ino) (hF : F !! i ≠ none) :
    walParked (L := L) (W := W) Ls cl F ⊢ walParkedIn (L := L) (W := W) Ls cl F i := by
  unfold walParked walParkedIn
  iintro ⟨%b, %o, Hpa, Hoa, %hp, Hs, Hc, Ht⟩
  iexists b, o
  iframe Hpa Hoa Hs Hc Ht
  ipureintro; exact ⟨hp, hp i hF⟩

/-- A segment's two halves outside the parked state: its inode is out. -/
theorem walParkedIn_of_halves (Ls : GMap GoString WalLay) (cl : List Claim) (F : GMap Ino SegFl)
    (g : SegG) (hg : g ∈ segsAll Ls) (m1 m2 : OsMeta) :
    walParked (L := L) (W := W) Ls cl F ∗ osMeta (L := L) g.ino (DFrac.own (1 : Qp).half) m1 ∗
        osMeta (L := L) g.ino (DFrac.own (1 : Qp).half) m2 ⊢
      walParkedIn (L := L) (W := W) Ls cl F g.ino ∗ osMeta (L := L) g.ino (DFrac.own (1 : Qp).half) m1 ∗
        osMeta (L := L) g.ino (DFrac.own (1 : Qp).half) m2 := by
  unfold walParked walParkedIn
  iintro ⟨⟨%b, %o, Hpa, Hoa, %hp, Hs, Hc, Ht⟩, H1, H2⟩
  icases segsP_meta (L := L) (segsAll Ls) o.O g.ino m1 m2 $$ [Hs H1 H2] with ⟨Hs, H1, H2, %hin⟩
  · iframe Hs H1 H2
  iframe H1 H2
  iexists b, o
  iframe Hpa Hoa Hs Hc Ht
  ipureintro; exact ⟨hp, hin g hg rfl⟩

/-- **Taking the lock** (`Open`, at its pin): nothing is out (the lock token's record is empty), so
no change is in flight (gap B); the taker gets the lock token's record. -/
theorem walParked_lock (Ls : GMap GoString WalLay) (cl : List Claim) (F : GMap Ino SegFl) :
    ⊢ walParked (L := L) (W := W) Ls cl F -∗ walUnlockedTok (W := W) ==∗
      walParked (L := L) (W := W) Ls cl F ∗ walLockedTok (W := W) ∗ walOutFrag (W := W) WalOut.empty ∗
        ⌜∀ i, F !! i = none⌝ := by
  unfold walParked
  iintro ⟨%b, %o, Hpa, Hoa, %hp, Hs, Hc, Ht⟩ Hu
  imod walUnlockedTok_lock (W := W) b $$ Hpa Hu with ⟨-, Hpa, Hl, Ho⟩
  icases walOut_agree (W := W) o WalOut.empty $$ Hoa Ho with %ho
  subst ho
  imodintro
  iframe Hl Ho
  isplitl [Hpa Hoa Hs Hc Ht]
  · iexists false, WalOut.empty
    iframe Hpa Hoa Hs Hc Ht
    ipureintro; exact hp
  ipureintro
  intro i
  exact Classical.byContradiction fun h => List.not_mem_nil (hp i h)

/-- **Releasing the lock** (`Close`, an `Open` failing after its pin): everything put back (the
record empty). -/
theorem walParked_unlock (Ls : GMap GoString WalLay) (cl : List Claim) (F : GMap Ino SegFl) :
    ⊢ walParked (L := L) (W := W) Ls cl F -∗ walLockedTok (W := W) -∗ walOutFrag (W := W) WalOut.empty ==∗
      walParked (L := L) (W := W) Ls cl F ∗ walUnlockedTok (W := W) := by
  unfold walParked
  iintro ⟨%b, %o, Hpa, Hoa, %hp, Hs, Hc, Ht⟩ Hl Ho
  imod walLockedTok_unlock (W := W) b $$ Hpa Hl Ho with ⟨-, Hpa, Hu⟩
  imodintro
  iframe Hu
  iexists true, o
  iframe Hpa Hoa Hs Hc Ht
  ipureintro; exact hp

/-- **A parked segment taken out** (`Open`'s pin): it is idle (gap B), so its halves agree with the
invariant's `segRes`. -/
theorem walParked_takeSeg (Ls : GMap GoString WalLay) (cl : List Claim) (F : GMap Ino SegFl)
    (o : WalOut) (g : SegG) (hg : g ∈ segsAll Ls) (hO : g.ino ∉ o.O) :
    ⊢ walParked (L := L) (W := W) Ls cl F -∗ walOutFrag (W := W) o ==∗
      walParked (L := L) (W := W) Ls cl F ∗ walOutFrag (W := W) (o.addSeg g.ino) ∗ segResP (L := L) g ∗
        ⌜F !! g.ino = none⌝ := by
  unfold walParked
  iintro ⟨%b, %o', Hpa, Hoa, %hp, Hs, Hc, Ht⟩ Ho
  icases walOut_agree (W := W) o' o $$ Hoa Ho with %ho
  subst ho
  imod walOut_set (W := W) o' o' (o'.addSeg g.ino) $$ Hoa Ho with ⟨Hoa, Ho⟩
  icases segsP_take (L := L) (segsAll Ls) o'.O g hg hO $$ Hs with ⟨Hg, Hs⟩
  imodintro
  iframe Ho Hg
  isplitl [Hpa Hoa Hs Hc Ht]
  · iexists b, o'.addSeg g.ino
    dsimp only [WalOut.addSeg]
    iframe Hpa Hoa Hs Hc Ht
    ipureintro
    intro i hi
    exact List.mem_cons_of_mem _ (hp i hi)
  ipureintro
  exact Classical.byContradiction fun h => hO (hp _ h)

/-- **Several parked segments taken out** (`Open`'s pin: the segments from the selected one on),
their inodes distinct. -/
theorem walParked_takeSegs (Ls : GMap GoString WalLay) (cl : List Claim) (F : GMap Ino SegFl)
    (o : WalOut) (S : List SegG) (hS : ∀ g ∈ S, g ∈ segsAll Ls) (hO : ∀ g ∈ S, g.ino ∉ o.O)
    (hnd : (S.map (·.ino)).Nodup) :
    ⊢ walParked (L := L) (W := W) Ls cl F -∗ walOutFrag (W := W) o ==∗
      walParked (L := L) (W := W) Ls cl F ∗ walOutFrag (W := W) ⟨S.map (·.ino) ++ o.O, o.D, o.T⟩ ∗
        ([∗list] g ∈ S, segResP (L := L) g) ∗ ⌜∀ g ∈ S, F !! g.ino = none⌝ := by
  induction S with
  | nil =>
    iintro Hp Ho
    imodintro
    iframe Hp
    have e : (⟨List.map (·.ino) ([] : List SegG) ++ o.O, o.D, o.T⟩ : WalOut) = o := rfl
    rw [e]
    iframe Ho
    isplitl
    · iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro; intro g hg; cases hg
  | cons g S ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    iintro Hp Ho
    imod ih (fun x hx => hS x (List.mem_cons_of_mem _ hx)) (fun x hx => hO x (List.mem_cons_of_mem _ hx))
      hnd.2 $$ Hp Ho with ⟨Hp, Ho, HS, %hF⟩
    have hgO : g.ino ∉ (⟨S.map (·.ino) ++ o.O, o.D, o.T⟩ : WalOut).O := by
      intro hm
      rcases List.mem_append.1 hm with h | h
      · exact hnd.1 h
      · exact hO g (List.mem_cons_self ..) h
    imod walParked_takeSeg (L := L) Ls cl F _ g (hS g (List.mem_cons_self ..)) hgO $$ Hp Ho
      with ⟨Hp, Ho, Hg, %hFg⟩
    imodintro
    iframe Hp
    have e : (⟨List.map (·.ino) (g :: S) ++ o.O, o.D, o.T⟩ : WalOut) =
        (⟨S.map (·.ino) ++ o.O, o.D, o.T⟩ : WalOut).addSeg g.ino := rfl
    rw [e]
    iframe Ho
    isplitl [Hg HS]
    · iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
      iframe Hg HS
    ipureintro
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hFg
    · exact hF x hx

/-- **A segment put back** (`openAtIndex`'s error arms, a failed `ReadAll`, `Close`): idle (no change
in flight on it), the layouts' inodes distinct. -/
theorem walParked_putSeg (Ls : GMap GoString WalLay) (cl : List Claim) (F : GMap Ino SegFl)
    (o : WalOut) (g : SegG) (hg : g ∈ segsAll Ls) (hnd : ((segsAll Ls).map (·.ino)).Nodup)
    (hF : F !! g.ino = none) :
    ⊢ walParked (L := L) (W := W) Ls cl F -∗ walOutFrag (W := W) o -∗ segResP (L := L) g ==∗
      walParked (L := L) (W := W) Ls cl F ∗ walOutFrag (W := W) (o.delSeg g.ino) := by
  unfold walParked
  iintro ⟨%b, %o', Hpa, Hoa, %hp, Hs, Hc, Ht⟩ Ho Hg
  icases walOut_agree (W := W) o' o $$ Hoa Ho with %ho
  subst ho
  imod walOut_set (W := W) o' o' (o'.delSeg g.ino) $$ Hoa Ho with ⟨Hoa, Ho⟩
  ihave Hs := segsP_put (L := L) (segsAll Ls) o'.O g hg hnd $$ [Hs Hg]
  · iframe Hs Hg
  imodintro
  iframe Ho
  iexists b, o'.delSeg g.ino
  dsimp only [WalOut.delSeg]
  iframe Hpa Hoa Hs Hc Ht
  ipureintro
  intro i hi
  have hne : i ≠ g.ino := by rintro rfl; exact hi hF
  simp only [List.mem_filter, decide_eq_true_eq]
  exact ⟨hp i hi, hne⟩

/-- **A parked WAL directory's claim taken out** (`Open`'s pin). -/
theorem walParked_takeClaim (Ls : GMap GoString WalLay) (cl : List Claim) (F : GMap Ino SegFl)
    (o : WalOut) (c : Claim) (hc : c ∈ cl) (hW : WalDirClaimOf Ls c) (hD : (c.1, c.2.1) ∉ o.D) :
    ⊢ walParked (L := L) (W := W) Ls cl F -∗ walOutFrag (W := W) o ==∗
      walParked (L := L) (W := W) Ls cl F ∗ walOutFrag (W := W) (o.addClaim (c.1, c.2.1)) ∗
        osNames (L := L) c.1 c.2.1 (DFrac.own (1 : Qp).half) c.2.2 := by
  unfold walParked
  iintro ⟨%b, %o', Hpa, Hoa, %hp, Hs, Hc, Ht⟩ Ho
  icases walOut_agree (W := W) o' o $$ Hoa Ho with %ho
  subst ho
  imod walOut_set (W := W) o' o' (o'.addClaim (c.1, c.2.1)) $$ Hoa Ho with ⟨Hoa, Ho⟩
  icases claimsP_take (L := L) Ls cl o'.D c hc ⟨hW, hD⟩ $$ Hc with ⟨Hn, Hc⟩
  imodintro
  iframe Ho Hn
  iexists b, o'.addClaim (c.1, c.2.1)
  dsimp only [WalOut.addClaim]
  iframe Hpa Hoa Hs Hc Ht
  ipureintro; exact hp

/-- **A WAL directory's claim put back**: once in the claims, no other of its key (`DirKeysOk`). -/
theorem walParked_putClaim (Ls : GMap GoString WalLay) (l1 l2 : List Claim) (F : GMap Ino SegFl)
    (o : WalOut) (c : Claim) (hkey : ∀ c' ∈ l1 ++ l2, (c'.1, c'.2.1) ≠ (c.1, c.2.1)) :
    ⊢ walParked (L := L) (W := W) Ls (l1 ++ c :: l2) F -∗ walOutFrag (W := W) o -∗
        osNames (L := L) c.1 c.2.1 (DFrac.own (1 : Qp).half) c.2.2 ==∗
      walParked (L := L) (W := W) Ls (l1 ++ c :: l2) F ∗ walOutFrag (W := W) (o.delClaim (c.1, c.2.1)) := by
  unfold walParked
  iintro ⟨%b, %o', Hpa, Hoa, %hp, Hs, Hc, Ht⟩ Ho Hn
  icases walOut_agree (W := W) o' o $$ Hoa Ho with %ho
  subst ho
  imod walOut_set (W := W) o' o' (o'.delClaim (c.1, c.2.1)) $$ Hoa Ho with ⟨Hoa, Ho⟩
  ihave Hc := claimsP_put (L := L) Ls l1 l2 o'.D c hkey $$ [Hc Hn]
  · iframe Hc Hn
  imodintro
  iframe Ho
  iexists b, o'.delClaim (c.1, c.2.1)
  dsimp only [WalOut.delClaim]
  iframe Hpa Hoa Hs Hc Ht
  ipureintro; exact hp

/-- **A WAL's pipeline names taken out** (`Open`'s pin, write mode). -/
theorem walParked_takeTmps (Ls : GMap GoString WalLay) (cl : List Claim) (F : GMap Ino SegFl)
    (o : WalOut) (dir : GoString) (lay : WalLay) (hl : Ls !! dir = some lay) (hT : dir ∉ o.T) :
    ⊢ walParked (L := L) (W := W) Ls cl F -∗ walOutFrag (W := W) o ==∗
      walParked (L := L) (W := W) Ls cl F ∗ walOutFrag (W := W) (o.addTmp dir) ∗
        walTmpsRes (hG := ⟨G, L⟩) lay.j := by
  unfold walParked
  iintro ⟨%b, %o', Hpa, Hoa, %hp, Hs, Hc, Ht⟩ Ho
  icases walOut_agree (W := W) o' o $$ Hoa Ho with %ho
  subst ho
  imod walOut_set (W := W) o' o' (o'.addTmp dir) $$ Hoa Ho with ⟨Hoa, Ho⟩
  icases walTmpParked_take (G := G) (L := L) Ls o'.T dir lay hl hT $$ Ht with ⟨Ht, Hd⟩
  imodintro
  iframe Ho Hd
  iexists b, o'.addTmp dir
  dsimp only [WalOut.addTmp]
  iframe Hpa Hoa Hs Hc Ht
  ipureintro; exact hp

/-- **A WAL's pipeline names put back** (`Close`, an `Open` failing after its pin). -/
theorem walParked_putTmps (Ls : GMap GoString WalLay) (cl : List Claim) (F : GMap Ino SegFl)
    (o : WalOut) (dir : GoString) (lay : WalLay) (hl : Ls !! dir = some lay) :
    ⊢ walParked (L := L) (W := W) Ls cl F -∗ walOutFrag (W := W) o -∗ walTmpsRes (hG := ⟨G, L⟩) lay.j ==∗
      walParked (L := L) (W := W) Ls cl F ∗ walOutFrag (W := W) (o.delTmp dir) := by
  unfold walParked
  iintro ⟨%b, %o', Hpa, Hoa, %hp, Hs, Hc, Ht⟩ Ho Hd
  icases walOut_agree (W := W) o' o $$ Hoa Ho with %ho
  subst ho
  imod walOut_set (W := W) o' o' (o'.delTmp dir) $$ Hoa Ho with ⟨Hoa, Ho⟩
  ihave Ht := walTmpParked_put (G := G) (L := L) Ls o'.T dir lay hl $$ [Ht Hd]
  · iframe Ht Hd
  imodintro
  iframe Ho
  iexists b, o'.delTmp dir
  dsimp only [WalOut.delTmp]
  iframe Hpa Hoa Hs Hc Ht
  ipureintro; exact hp

end parked

end WalFs
end EtcdGrove
end Perennial

end
