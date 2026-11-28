/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/Threads/QTok.lean (241f27e).
Re-proved over Perennial's leveled thread tokens (a token is one exclusive slot at each of the `T`
levels, `threadTok = levelsToks 0 T 1`, Perennial `Threads.lean`); the interface (`rtok`,
`threadTok_rtoks`, `threadTok_split`/`_merge`, `rtoks_le`, `rtoks_lt_pow`, the two forks) is the
lab's, statements unchanged. What changed is `rtok t`'s definition: `t` now names the token's list
of slots, one per level (`slotsId`, injective), instead of its one slot.
-/
/-
**Quarter thread tokens** (decision D15, notes/decisions.md): the per-thread capability of this
project is `rtok t`, a quarter of the thread token named `t` (`Perennial/GooseLang/Threads.lean`:
a token is, at each level `l < T`, the exclusive `levelKey l k ↪[threadTokName] ()` of one slot
`k + 1 < T`; `t = slotsId ks` names the slots `ks`, one per level).

Why quarters: a goroutine started by raft's `goFunc` must run `f` with a capability *and* back the
routines group's counter (`WaitGroup.Add(1)`, counter `< 2^31`) until its `Done`, while the fork
yields one token. With quarters, the goroutine keeps one quarter for `f` and the routines group
holds another one (notes/core-notes.md, hub request CORE-1). Every bound that whole tokens gave by
`threadToks n ⊢ ⌜n < T⌝` is given by quarters with a factor 4 (`rtoks_le`):
`m` quarters (of any tokens) are at most `4 * (T - 1)` (counted at level `0`).

Why the name is explicit: a forked thread must end with a *whole* token (`wp_fork_tok*`), i.e. the
four quarters of one token. So a thread's code returns the quarter of the token it was given:
every spec takes `rtok t` and gives back `rtok t` for the same `t` (a universally quantified
"thread slot" of the spec).

* `rtok t`: a quarter of token `t` (timeless).
* `threadTok_rtoks : threadTok ⊣⊢ ∃ t, rtok t ∗ rtok t ∗ rtok t ∗ rtok t`.
* `rtoks_le : ([∗list] t ∈ ts, rtok t) ⊢ ⌜ts.length ≤ 4 * (threadBound GF - 1)⌝`
  (and `rtoks_lt_pow` for `threadBound GF ≤ 2 ^ 28`: fewer than `2 ^ 30` quarters).
* `wp_fork_rtok` (the spawned body runs with a quarter `rtok t` of its fresh token and returns it)
  and `wp_fork_rtok_upd` (the four quarters of the fresh token at the fork, with an update at the
  forking thread's mask to deposit some in an invariant; the body must return all four).
-/
module

public import Perennial.GooseLang.Threads
public import Perennial.GooseLang.Lifting
public import Perennial.ProgramLogic.Bounds

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProofMode

section defs
variable {GF : BundledGFunctors} [AllG GF] [hT : ThreadGS GF]

/-- The fraction `q` of the level tokens of the slots `ks`, the `i`-th at level `l + i`. -/
def qrow (q : Qp) : Nat → List Nat → IProp GF
  | _, [] => iprop(emp)
  | l, k :: ks => iprop((levelKey (GF := GF) l k ↪[hT.threadTokName]{#q} ()) ∗ qrow q (l + 1) ks)

/-- The name of a thread token whose slots (one per level) are `ks`: injective (`slotsId_inj`). -/
def slotsId (ks : List Nat) : Nat := (Pos.Countable.encode ks).toNat

/-- `rtok t`: a quarter of the thread token named `t`: the per-thread capability (D15). -/
def rtok (t : Nat) : IProp GF :=
  iprop(∃ ks : List Nat,
    ⌜slotsId ks = t ∧ ks.length = hT.threadBound ∧ ∀ k ∈ ks, k + 1 < hT.threadBound⌝ ∗
      qrow Qp.quarter 0 ks)

instance qrow_timeless (q : Qp) (l : Nat) (ks : List Nat) : Timeless (qrow (GF := GF) q l ks) := by
  induction ks generalizing l with
  | nil => unfold qrow; infer_instance
  | cons k ks ih => unfold qrow; infer_instance

instance rtok_timeless (t : Nat) : Timeless (rtok (GF := GF) t) := by
  unfold rtok; infer_instance

end defs

theorem slotsId_inj {a b : List Nat} (h : slotsId a = slotsId b) : a = b :=
  Pos.encode_inj (Pos.Pos_toNat_inj h)


/-! ## Splitting a token into quarters -/

namespace qtok

/-- A quarter fraction `k/4` (for `k ≥ 1`). -/
def qk (k : Nat) (hk : 0 < k) : Qp := ⟨(k : Rat) / 4, by
  have : (0 : Rat) < k := by exact_mod_cast hk
  grind⟩

theorem qk_one : qk 1 (by decide) = Qp.quarter := Subtype.ext (by simp [qk])

theorem qk_succ (k : Nat) (hk : 0 < k) :
    qk k hk + Qp.quarter = qk (k + 1) (by omega) := by
  apply Subtype.ext
  simp only [qk, Qp.val_add, Qp.val_quarter]
  push_cast
  grind

theorem quarters_one :
    (1 : Qp) = (Qp.quarter + Qp.quarter) + (Qp.quarter + Qp.quarter) :=
  Subtype.ext (by simp only [Qp.val_add, Qp.val_quarter, Qp.val_one]; grind)

/-- Counting the quarters of one slot `j`, starting from `k` of them already combined. -/
theorem count_aux {GF : BundledGFunctors} [AllG GF] (γ : GName) (j : Nat) :
    ∀ (ts : List Nat) (k : Nat) (hk : 0 < k),
      (j ↪[γ]{#qk k hk} ()) ∗ ([∗list] t ∈ ts, t ↪[γ]{#Qp.quarter} ()) ⊢@{IProp GF}
        ⌜k + ts.count j ≤ 4⌝
  | [], k, hk => by
    iintro ⟨Hj, -⟩
    icases ghostMapElem_valid j γ _ () $$ Hj with %Hv
    ipureintro
    have h : ((k : Rat) / 4) ≤ 1 := Hv
    have h' : (k : Rat) ≤ 4 := by grind
    have : k ≤ 4 := by exact_mod_cast h'
    simpa using this
  | t :: ts, k, hk => by
    iintro ⟨Hj, Ht, Hts⟩
    by_cases h : t = j
    · subst h
      icombine Hj Ht as Hj
      rw [qk_succ k hk]
      icases count_aux γ t ts (k + 1) (by omega) $$ [Hj Hts] with %H
      · iframe
      ipureintro
      simp only [List.count_cons_self]; omega
    · iclear Ht
      icases count_aux γ j ts k hk $$ [Hj Hts] with %H
      · iframe
      ipureintro
      have : (t :: ts).count j = ts.count j := by
        simp [h]
      omega

/-- At most four quarters of any slot. -/
theorem count_le {GF : BundledGFunctors} [AllG GF] (γ : GName) (j : Nat) :
    ∀ ts : List Nat, ([∗list] t ∈ ts, t ↪[γ]{#Qp.quarter} ()) ⊢@{IProp GF} ⌜ts.count j ≤ 4⌝
  | [] => by iintro -; ipureintro; simp
  | t :: ts => by
    iintro ⟨Ht, Hts⟩
    by_cases h : t = j
    · subst h
      icases count_aux γ t ts 1 (by decide) $$ [Ht Hts] with %H
      · isplitl [Ht]
        · rw [qk_one]; iexact Ht
        · iexact Hts
      ipureintro
      simp only [List.count_cons_self]; omega
    · iclear Ht
      icases count_le γ j ts $$ Hts with %H
      ipureintro
      have : (t :: ts).count j = ts.count j := by
        simp [h]
      omega

/-- The counting argument: a list of slots below `n`, each at most four times, has length at most
`4 * n`. -/
theorem length_le_of_count (n : Nat) :
    ∀ ts : List Nat, (∀ t ∈ ts, t < n) → (∀ j, ts.count j ≤ 4) → ts.length ≤ 4 * n := by
  induction n with
  | zero =>
    intro ts hlt _
    cases ts with
    | nil => simp
    | cons t _ => exact absurd (hlt t (by simp)) (by omega)
  | succ n ih =>
    intro ts hlt hc
    rw [List.length_eq_countP_add_countP (fun a => a == n)]
    have h1 : ts.countP (fun a => a == n) ≤ 4 := by
      have := hc n; rw [List.count_eq_countP] at this
      exact this
    have h2 : ts.countP (fun a => ¬ (a == n) = true) ≤ 4 * n := by
      rw [List.countP_eq_length_filter]
      apply ih
      · intro t ht
        have := List.mem_filter.mp ht
        have h := hlt t this.1
        have : t ≠ n := by simpa using this.2
        omega
      · intro j
        exact Nat.le_trans (List.Sublist.count_le _ (List.filter_sublist)) (hc j)
    omega

end qtok

section laws
variable {GF : BundledGFunctors} [AllG GF] [hT : ThreadGS GF]

theorem qrow_nil (q : Qp) (l : Nat) : qrow (GF := GF) q l [] = iprop(emp) := rfl

theorem qrow_cons (q : Qp) (l k : Nat) (ks : List Nat) :
    qrow (GF := GF) q l (k :: ks) =
      iprop((levelKey (GF := GF) l k ↪[hT.threadTokName]{#q} ()) ∗ qrow q (l + 1) ks) := rfl

private theorem levelsToks_succ (l c n : Nat) :
    levelsToks (GF := GF) l (c + 1) n = iprop(levelToks l n ∗ levelsToks (l + 1) c n) := rfl

private theorem levelTokList_single (l k : Nat) :
    levelTokList (GF := GF) l [k] =
      iprop(⌜k + 1 < hT.threadBound⌝ ∗ (levelKey (GF := GF) l k ↪[hT.threadTokName] ()) ∗ emp) :=
  rfl

/-- A row of fractions splits as its fraction does. -/
theorem qrow_split (q1 q2 : Qp) (l : Nat) (ks : List Nat) :
    qrow (GF := GF) (q1 + q2) l ks ⊣⊢ qrow q1 l ks ∗ qrow q2 l ks := by
  induction ks generalizing l with
  | nil =>
    rw [qrow_nil, qrow_nil, qrow_nil]
    constructor
    · iintro -; isplitl []
      · iempintro
      · iempintro
    · iintro ⟨-, -⟩; iempintro
  | cons k ks ih =>
    have hfr := (ghostMapElem_fractional (GF := GF) (levelKey (GF := GF) l k)
      hT.threadTokName ()).fractional
    rw [qrow_cons, qrow_cons, qrow_cons]
    constructor
    · iintro ⟨Hk, Hr⟩
      icases (hfr q1 q2).1 $$ Hk with ⟨H1, H2⟩
      icases (ih (l + 1)).1 $$ Hr with ⟨R1, R2⟩
      isplitl [H1 R1]
      · iframe
      · iframe
    · iintro ⟨⟨H1, R1⟩, ⟨H2, R2⟩⟩
      isplitl [H1 H2]
      · iapply (hfr q1 q2).2; iframe
      · iapply (ih (l + 1)).2; iframe

/-- A whole row is four quarter rows. -/
theorem qrow_quarters (l : Nat) (ks : List Nat) :
    qrow (GF := GF) 1 l ks ⊣⊢
      qrow Qp.quarter l ks ∗ qrow Qp.quarter l ks ∗ qrow Qp.quarter l ks ∗ qrow Qp.quarter l ks := by
  rw [qtok.quarters_one]
  constructor
  · iintro H
    icases (qrow_split _ _ l ks).1 $$ H with ⟨H12, H34⟩
    icases (qrow_split _ _ l ks).1 $$ H12 with ⟨H1, H2⟩
    icases (qrow_split _ _ l ks).1 $$ H34 with ⟨H3, H4⟩
    iframe
  · iintro ⟨H1, H2, H3, H4⟩
    iapply (qrow_split _ _ l ks).2
    isplitl [H1 H2]
    · iapply (qrow_split _ _ l ks).2; iframe
    · iapply (qrow_split _ _ l ks).2; iframe

/-- One token of each of the `c` levels from `l`: a row of slots. -/
theorem levelsToks_rows (l c : Nat) :
    levelsToks (GF := GF) l c 1 ⊣⊢
      ∃ ks : List Nat, ⌜ks.length = c ∧ ∀ k ∈ ks, k + 1 < hT.threadBound⌝ ∗ qrow 1 l ks := by
  induction c generalizing l with
  | zero =>
    constructor
    · iintro -
      iexists []
      rw [qrow_nil]
      isplitl []
      · ipureintro; simp
      · iempintro
    · iintro -
      unfold levelsToks
      iempintro
  | succ c ih =>
    rw [levelsToks_succ]
    unfold levelToks
    constructor
    · iintro ⟨⟨%ks1, %H1, Hk⟩, Hr⟩
      obtain ⟨k, rfl⟩ : ∃ k, ks1 = [k] := by
        match ks1, H1 with
        | [k], _ => exact ⟨k, rfl⟩
      rw [levelTokList_single]
      icases Hk with ⟨%Hlt, Hk, -⟩
      icases (ih (l + 1)).1 $$ Hr with ⟨%ks, %Hks, Hr⟩
      iexists k :: ks
      rw [qrow_cons]
      isplitl []
      · ipureintro
        refine ⟨by simp [Hks.1], fun k' hk' => ?_⟩
        rcases List.mem_cons.mp hk' with rfl | h
        · exact Hlt
        · exact Hks.2 k' h
      · iframe
    · iintro ⟨%ks, %Hks, Hr⟩
      cases ks with
      | nil => simp at Hks
      | cons k ks =>
        rw [qrow_cons]
        icases Hr with ⟨Hk, Hr⟩
        isplitl [Hk]
        · iexists [k]
          rw [levelTokList_single]
          isplitl []
          · ipureintro; rfl
          · isplitl []
            · ipureintro; exact Hks.2 k (by simp)
            · isplitl [Hk]
              · iexact Hk
              · iempintro
        · iapply (ih (l + 1)).2
          iexists ks
          iframe Hr
          ipureintro
          exact ⟨by simpa using Hks.1, fun k' h => Hks.2 k' (by simp [h])⟩

/-- A thread token is a row of `T` slots, one per level. -/
theorem threadTok_rows :
    threadTok (GF := GF) ⊣⊢
      ∃ ks : List Nat, ⌜ks.length = hT.threadBound ∧ ∀ k ∈ ks, k + 1 < hT.threadBound⌝ ∗
        qrow 1 0 ks := by
  show threadToks (GF := GF) 1 ⊣⊢ _
  rw [threadToks_eq_levels]
  exact levelsToks_rows 0 _

private theorem rtok_of (ks : List Nat)
    (h : ks.length = hT.threadBound ∧ ∀ k ∈ ks, k + 1 < hT.threadBound) :
    qrow (GF := GF) Qp.quarter 0 ks ⊢ rtok (slotsId ks) := by
  iintro H
  unfold rtok
  iexists ks
  iframe H
  ipureintro
  exact ⟨rfl, h⟩

/-- A whole thread token is the four quarters of its name. -/
theorem threadTok_rtoks :
    threadTok (GF := GF) ⊣⊢ ∃ t, rtok t ∗ rtok t ∗ rtok t ∗ rtok t := by
  constructor
  · iintro H
    icases threadTok_rows.1 $$ H with ⟨%ks, %Hks, Hr⟩
    icases (qrow_quarters 0 ks).1 $$ Hr with ⟨H1, H2, H3, H4⟩
    iexists slotsId ks
    isplitl [H1]
    · iapply (rtok_of ks Hks) $$ H1
    isplitl [H2]
    · iapply (rtok_of ks Hks) $$ H2
    isplitl [H3]
    · iapply (rtok_of ks Hks) $$ H3
    · iapply (rtok_of ks Hks) $$ H4
  · unfold rtok
    iintro ⟨%t, ⟨%ks1, %P1, H1⟩, ⟨%ks2, %P2, H2⟩, ⟨%ks3, %P3, H3⟩, ⟨%ks4, %P4, H4⟩⟩
    obtain ⟨e2, -, -⟩ := P2
    obtain ⟨e3, -, -⟩ := P3
    obtain ⟨e4, -, -⟩ := P4
    obtain ⟨e1, Hl, Ha⟩ := P1
    rw [slotsId_inj (e2.trans e1.symm), slotsId_inj (e3.trans e1.symm),
      slotsId_inj (e4.trans e1.symm)]
    iapply threadTok_rows.2
    iexists ks1
    isplitl []
    · ipureintro; exact ⟨Hl, Ha⟩
    · iapply (qrow_quarters 0 ks1).2; iframe

/-- Splitting a token into its four quarters. -/
theorem threadTok_split : threadTok (GF := GF) ⊢ ∃ t, rtok t ∗ rtok t ∗ rtok t ∗ rtok t :=
  threadTok_rtoks.1

/-- Merging the four quarters of one token into a token. -/
theorem threadTok_merge (t : Nat) :
    rtok (GF := GF) t ∗ rtok t ∗ rtok t ∗ rtok t ⊢ threadTok := by
  iintro H
  iapply threadTok_rtoks.2
  iexists t
  iexact H

/-- **The counting law**: `m` quarters, of any tokens, are at most `4 * (threadBound GF - 1)`
(counted by their level-`0` slots, below `threadBound GF - 1`, each at most four times). -/
theorem rtoks_le (ts : List Nat) :
    ([∗list] t ∈ ts, rtok (GF := GF) t) ⊢ ⌜ts.length ≤ 4 * (hT.threadBound - 1)⌝ := by
  have hsplit : ([∗list] t ∈ ts, rtok (GF := GF) t) ⊢
      ∃ ks0 : List Nat, ⌜ks0.length = ts.length ∧ ∀ k ∈ ks0, k + 1 < hT.threadBound⌝ ∗
        [∗list] k ∈ ks0, k ↪[hT.threadTokName]{#Qp.quarter} () := by
    induction ts with
    | nil =>
      iintro -
      iexists []
      isplitl []
      · ipureintro; simp
      · iapply BigSepL.bigSepL_nil.2; iempintro
    | cons t ts ih =>
      iintro ⟨Ht, Hts⟩
      icases ih $$ Hts with ⟨%ks0, %Hk0, Hts⟩
      unfold rtok
      icases Ht with ⟨%ks, %Hp, Hr⟩
      obtain ⟨-, Hl, Ha⟩ := Hp
      cases ks with
      | nil => have := hT.threadBound_gt; simp at Hl; omega
      | cons k ks =>
        have hk0 : levelKey (GF := GF) 0 k = k := by simp [levelKey]
        rw [qrow_cons, hk0]
        icases Hr with ⟨Hk, -⟩
        iexists k :: ks0
        isplitl []
        · ipureintro
          refine ⟨by simp [Hk0.1], fun k' hk' => ?_⟩
          rcases List.mem_cons.mp hk' with rfl | h
          · exact Ha k' (by simp)
          · exact Hk0.2 k' h
        · iapply BigSepL.bigSepL_cons.2; iframe
  iintro H
  icases hsplit $$ H with ⟨%ks0, %Hk0, H⟩
  ihave %Hc : ⌜∀ j, ks0.count j ≤ 4⌝ $$ [H]
  · iintro %j
    iapply qtok.count_le _ j ks0 $$ H
  ipureintro
  rw [← Hk0.1]
  exact qtok.length_le_of_count (hT.threadBound - 1) ks0
    (fun t ht => by have := Hk0.2 t ht; omega) Hc

/-- The counting law under the project's bound `threadBound GF ≤ 2 ^ 28`: fewer than `2 ^ 30`
quarters. -/
theorem rtoks_lt_pow [ThreadBoundLe GF (2 ^ 28)] (ts : List Nat) :
    ([∗list] t ∈ ts, rtok (GF := GF) t) ⊢ ⌜ts.length < 2 ^ 30⌝ := by
  refine (rtoks_le ts).trans ?_
  iintro %H
  ipureintro
  have := ThreadBoundLe.le (GF := GF) (k := 2 ^ 28)
  have := hT.threadBound_gt
  omega

end laws


/-! ## Forks -/

section fork
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- `Fork e`, with the four quarters of the fresh slot `t` at the fork and an update at the forking
thread's mask (e.g. to deposit some quarters in an invariant): the forked body must end with the
four quarters of `t` (its token, returned at its `ThreadExit`). -/
theorem wp_fork_rtok_upd (e : Expr) (Φ : val → IProp GF) :
    ⊢ ▷ (∀ t, rtok t -∗ rtok t -∗ rtok t -∗ rtok t -∗ £ 1 -∗
        |={E}=> (WP e @ s; ⊤ {{ v, ⌜v.isPanic = false⌝ ∗ rtok t ∗ rtok t ∗ rtok t ∗ rtok t }} ∗
          Φ #())) -∗
      WP (Fork e) @ s; E {{ Φ }} := by
  iintro H
  iapply wp_fork_tok_upd
  inext
  iintro Htok Hlc
  icases threadTok_split $$ Htok with ⟨%t, H1, H2, H3, H4⟩
  imod H $$ %t H1 H2 H3 H4 Hlc with ⟨Hwp, HΦ⟩
  imodintro
  iframe HΦ
  iapply wp_wand $$ Hwp
  iintro %v ⟨%Hv, Ht⟩
  isplitr
  · ipureintro; exact Hv
  iapply threadTok_merge t $$ Ht

/-- `Fork e`, the forked body running with a quarter `rtok t` of its fresh slot (the other three
quarters stay with it) and returning it. -/
theorem wp_fork_rtok (e : Expr) (Φ : val → IProp GF) :
    ⊢ ▷ (∀ t, rtok t -∗ WP e @ s; ⊤ {{ v, ⌜v.isPanic = false⌝ ∗ rtok t }}) -∗ ▷ Φ #() -∗
      WP (Fork e) @ s; E {{ Φ }} := by
  iintro He HΦ
  iapply wp_fork_rtok_upd
  inext
  iintro %t H1 H2 H3 H4 _
  imodintro
  iframe HΦ
  ispecialize He $$ %t H1
  iapply wp_wand $$ He
  iintro %v ⟨%Hv, H1⟩
  iframe
  ipureintro; exact Hv

end fork

end Perennial
