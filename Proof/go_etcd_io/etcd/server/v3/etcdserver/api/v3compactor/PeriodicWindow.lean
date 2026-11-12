/-
`Periodic.Run`'s loop invariant (its proof's only; moved out of `Defs.lean` at the spec-first
pilot's freeze, 2026-10-27, review round 5: the specs' importers do not need it). The window of
samples `pc.revs` (`windowOk`, pure), their clock stamps (`stampsOk`), the window's head
(`firstOk`), their step lemmas, and C1's periodic permit from them (`perPermit_of_window`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3compactor

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.api.v3

/-! ### The window (pure) -/

/-- A full window's oldest sample has waited at least `period`: `retentions` waits of `retry`. -/
theorem window_full_age (p : Int) (hp : 10 ≤ p) : p ≤ retentionsOf p * retryOf p := by
  unfold retentionsOf
  have hr : 0 < retryOf p := by unfold retryOf; omega
  have := Int.lt_ediv_add_one_mul_self p hr
  omega

/-- **The window's pure invariant** (`Periodic.Run`'s loop): sorted, non-negative, bounded by the
last sample `m`, no longer than `retentions`, and `lastRevision` (`lr`) at most its head (`0` while
it is empty: before the first round). -/
def windowOk (xs : List w64) (m rn lr : Int) : Prop :=
  List.Pairwise (fun a b => sint.Z a ≤ sint.Z b) xs ∧ (∀ x ∈ xs, 0 ≤ sint.Z x ∧ sint.Z x ≤ m) ∧
    0 ≤ m ∧ (xs.length : Int) ≤ rn ∧ 0 ≤ lr ∧ (∀ x ∈ xs.head?, lr ≤ sint.Z x) ∧ (xs = [] → lr = 0)

/-- A round's sample `v`, no smaller than `m`, appended to the window and the window trimmed if it
grew past `retentions`: the invariant holds of the new window, at `v`. -/
theorem windowOk_step (xs ys : List w64) (v : w64) (m rn lr : Int) (hw : windowOk xs m rn lr)
    (hv : m ≤ sint.Z v ∧ 0 ≤ sint.Z v) (hrn : 1 ≤ rn)
    (hys : (ys = xs ++ [v] ∧ (xs.length : Int) + 1 ≤ rn) ∨
      (rn < (xs.length : Int) + 1 ∧ ys = (xs ++ [v]).tail)) :
    windowOk ys (sint.Z v) rn lr := by
  obtain ⟨hpw, hall, hm, hlen, hlr, hhd, hemp⟩ := hw
  have hpw' : List.Pairwise (fun a b => sint.Z a ≤ sint.Z b) (xs ++ [v]) := by
    refine List.pairwise_append.2 ⟨hpw, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb; subst hb
    exact Int.le_trans (hall a ha).2 hv.1
  have hall' : ∀ x ∈ xs ++ [v], 0 ≤ sint.Z x ∧ sint.Z x ≤ sint.Z v := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact ⟨(hall x hx).1, Int.le_trans (hall x hx).2 hv.1⟩
    · rw [List.mem_singleton] at hx; subst hx; exact ⟨hv.2, Int.le_refl _⟩
  rcases hys with ⟨rfl, hl⟩ | ⟨hl, rfl⟩
  · refine ⟨hpw', hall', hv.2, by simp; omega, hlr, ?_, by simp⟩
    intro x hx
    cases xs with
    | nil => simp at hx; subst hx; rw [hemp rfl]; exact hv.2
    | cons x0 rest => simp at hx; subst hx; exact hhd x0 (by simp)
  · cases xs with
    | nil => simp at hl; omega
    | cons x0 rest =>
      simp only [List.cons_append, List.tail_cons] at hpw' hall' ⊢
      have hpc := List.pairwise_cons.1 hpw'
      refine ⟨hpc.2, fun x hx => hall' x (List.mem_cons_of_mem _ hx), hv.2, ?_, hlr, ?_, ?_⟩
      · simp at hl hlen ⊢; omega
      · intro x hx
        have hx' : x ∈ rest ++ [v] := List.mem_of_mem_head? hx
        exact Int.le_trans (hhd x0 (by simp)) (hpc.1 x hx')
      · simp

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! ### The stamps and the window's head -/

/-- **The window's stamps**, at a clock bound `n`: each sample `xs[i]`, oldest first, was reached by
the store at a stamped clock time `T` that the clock is `len - i` waits of `retry` past (the
sample was waited on once in the round that took it, and once in every round since). -/
def stampsOk (RevLb : Int → IProp GF) (retry n : Int) (xs : List w64) : IProp GF :=
  iprop([∗list] i ↦ x ∈ xs, ∃ T : Int,
    clockwork.stampAt clockwork.realClock iprop(□ RevLb (sint.Z x)) T ∗
    ⌜T + ((xs.length : Int) - i) * retry ≤ n⌝)

instance stampsOk_persistent (RevLb : Int → IProp GF) (retry n : Int) (xs : List w64) :
    Persistent (stampsOk (GF := GF) RevLb retry n xs) := by
  unfold stampsOk; infer_instance

/-- A round's sample `v`, stamped at `T` (at least the clock bound `n` the stamps were at) and then
waited on (the clock now `T + r`): one more wait for every sample. -/
theorem stampsOk_snoc (RevLb : Int → IProp GF) (r n T : Int) (xs : List w64) (v : w64)
    (hT : n ≤ T) :
    stampsOk RevLb r n xs ∗ clockwork.stampAt clockwork.realClock iprop(□ RevLb (sint.Z v)) T ⊢
      stampsOk RevLb r (T + r) (xs ++ [v]) := by
  unfold stampsOk
  iintro ⟨Hs, Hv⟩
  iapply BigSepL.bigSepL_snoc.2
  isplitl [Hs]
  · iapply (BigSepL.bigSepL_mono_of_forall (fun {k x} => ?_)) $$ Hs
    iintro ⟨%T', HT', %Hb⟩
    iexists T'
    iframe HT'
    ipureintro
    rw [List.length_append, List.length_singleton]
    have h : (((xs.length + 1 : Nat) : Int) - (k : Int)) * r = ((xs.length : Int) - k) * r + r := by
      rw [show (((xs.length + 1 : Nat) : Int) - (k : Int)) = ((xs.length : Int) - k) + 1 by omega,
        Int.add_mul, Int.one_mul]
    omega
  · iexists T
    iframe Hv
    ipureintro
    rw [List.length_append, List.length_singleton]
    have h : (((xs.length + 1 : Nat) : Int) - (xs.length : Int)) * r = r := by
      rw [show (((xs.length + 1 : Nat) : Int) - (xs.length : Int)) = 1 by omega, Int.one_mul]
    omega

/-- The window trimmed (`revs = revs[1:]`): the samples keep their ages. -/
theorem stampsOk_tail (RevLb : Int → IProp GF) (r n : Int) (x : w64) (xs : List w64) :
    stampsOk RevLb r n (x :: xs) ⊢ stampsOk RevLb r n xs := by
  unfold stampsOk
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨-, H⟩
  iapply (BigSepL.bigSepL_mono_of_forall (fun {k y} => ?_)) $$ H
  iintro ⟨%T, HT, %Hb⟩
  iexists T
  iframe HT
  ipureintro
  rw [List.length_cons] at Hb
  rw [show (((xs.length + 1 : Nat) : Int) - ((k + 1 : Nat) : Int)) = (xs.length : Int) - k by omega] at Hb
  exact Hb

/-- The window's oldest sample and its stamp: as old as the window is long. -/
theorem stampsOk_head (RevLb : Int → IProp GF) (r n : Int) (x : w64) (xs : List w64) :
    stampsOk RevLb r n (x :: xs) ⊢ ∃ T : Int,
      clockwork.stampAt clockwork.realClock iprop(□ RevLb (sint.Z x)) T ∗
      ⌜T + ((x :: xs).length : Int) * r ≤ n⌝ := by
  unfold stampsOk
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨%T, HT, %Hb⟩, -⟩
  iexists T
  iframe HT
  ipureintro
  simpa using Hb

/-- **The window's head**: none and the first sample unset; or the run's first sample; or a full
window (trimmed: its head is `retentions` waits old). -/
def firstOk (γf : GName) (retentions : Int) : List w64 → IProp GF
  | [] => firstUnset γf
  | x :: rest => iprop(firstSample γf (sint.Z x) ∨ ⌜((x :: rest).length : Int) = retentions⌝)

/-- The window's head after a round: the first round sets the first sample (the ghost variable,
unset until then, to the round's sample); an untrimmed window keeps its head; a trimmed one is
full. -/
theorem firstOk_step (γf : GName) (rn : Int) (xs ys : List w64) (v : w64) (hrn : 1 ≤ rn)
    (hlen : (xs.length : Int) ≤ rn)
    (hys : (ys = xs ++ [v] ∧ (xs.length : Int) + 1 ≤ rn) ∨
      (rn < (xs.length : Int) + 1 ∧ ys = (xs ++ [v]).tail)) :
    firstOk (GF := GF) γf rn xs ⊢ |==> firstOk γf rn ys := by
  cases xs with
  | nil =>
    rcases hys with ⟨rfl, -⟩ | ⟨hl, -⟩
    · simp only [firstOk, firstUnset, firstSample, List.nil_append]
      iintro H
      imod dghostVar_update (some (sint.Z v)) γf none $$ H with H
      imod dghostVar_persist γf 1 _ $$ H with #H
      imodintro
      ileft
      iexact H
    · simp at hl; omega
  | cons x0 rest =>
    rcases hys with ⟨rfl, hl⟩ | ⟨hl, rfl⟩
    · simp only [firstOk, List.cons_append]
      iintro (#H | %H)
      · imodintro; ileft; iexact H
      · simp at hl H; omega
    · simp only [List.cons_append, List.tail_cons]
      cases rest with
      | nil =>
        simp only [firstOk, List.nil_append]
        iintro -
        imodintro; iright; ipureintro; simp at hl hlen ⊢; omega
      | cons r0 rest' =>
        simp only [firstOk, List.cons_append]
        iintro -
        imodintro; iright; ipureintro; simp at hl hlen ⊢; omega

/-- **C1 from the window** (`Periodic.Run`'s compaction of the window's head `x`): its stamp is the
window's length of waits behind the clock, so the clock is `period` past it when the window is full
(`window_full_age`), and `retry` past it when `x` is the run's first sample. -/
theorem perPermit_of_window (RevLb : Int → IProp GF) (period ri rn n : Int) (γf : GName) (x : w64)
    (rest : List w64) (hp : 10 ≤ period) (hri : ri = retryOf period) (hrn : rn = retentionsOf period)
    (hx : 0 < sint.Z x) :
    stampsOk RevLb ri n (x :: rest) ∗ firstOk γf rn (x :: rest) ∗ clockwork.clockLb clockwork.realClock n ⊢
      perPermit RevLb period γf (sint.Z x) ∗ firstOk γf rn (x :: rest) := by
  iintro ⟨Hst, Hf, #Hn⟩
  icases stampsOk_head $$ Hst with ⟨%T, #HT, %Hb⟩
  have hr : 1 ≤ ri := by subst hri; unfold retryOf; omega
  simp only [firstOk]
  icases Hf with (#Hf | %Hf)
  · have hl : ri ≤ (((x :: rest).length : Int)) * ri := by
      have h1 : (1 : Int) ≤ ((x :: rest).length : Int) := by simp; omega
      have := Int.mul_le_mul_of_nonneg_right h1 (show (0 : Int) ≤ ri by omega)
      omega
    unfold perPermit
    isplitr
    · isplitr
      · ipureintro; exact hx
      iexists T; iframe HT
      iright; iframe Hf
      rw [← hri]
      iapply clockwork.clockLb_le _ _ _ (by omega) $$ Hn
    ileft; iexact Hf
  · have hw := window_full_age period hp
    rw [← hri, ← hrn, ← Hf] at hw
    unfold perPermit
    isplitr
    · isplitr
      · ipureintro; exact hx
      iexists T; iframe HT
      ileft
      iapply clockwork.clockLb_le _ _ _ (by omega) $$ Hn
    iright; ipureintro; exact Hf

end defs

end v3compactor
end EtcdGrove
end Perennial
