/-
Deciders for the net extension's relations (`Impl.lean`, `Deploy.lean`), for the Lean replay of
the conformance checker's witnesses (`Replay.lean`; `examples/net/conform/check/README.md`,
"Certification in Lean"). Proved, outside the trust base: each decider is a `Bool` function with a
proved `= true ↔` lemma against the relation it decides, so that a replay that runs a decider
establishes the relation itself, not a transcription of it.

A relation with an existential is decided at the instance it is given, all its arguments given:

* `ReadAvail st d n r d'`: its `∃ k` is the length of the bytes `r` returns (`readAvailB`);
* `ReadOutcome st d n r d'`: its cut's `∃ k` (the prefix the cut keeps) is determined by `r` and
  `d'` (`cutKeep`: the bytes returned and the bytes left, or nothing for EOF, or the bytes left),
  so the decider tries that one only (`readOutcomeB`, `cut_unique`);
* `lisAccepts la a`: its `∃ p` is `wildPort la` (`lisAcceptsB`);
* `WriteOutcome st d rs k res d'` has none: the step's count `k` is an argument.

The other relations (`WriteOutcome`, `CloseOutcome`, `CloseWriteOutcome`, `DeadlineOutcome`,
`LisCloseOutcome`, `IsEnd`) are decided by the same case split as their definitions. `addrOk`,
`listenOk` and `timeIsZero` are `Bool` already (`Impl.lean`).

The atoms avoid walking a direction's bytes where they can (the probe's directions hold megabytes):
`lenGe` decides `k ≤ l.length` in `k` cells, `appendEqB` decides `a = b ++ c` without building
`b ++ c`, and `bytesEqB` is list equality that answers at once for the same object in memory
(Lean's `withPtrEqDecEq`, a `Decidable` instance: its lemma is `decide_eq_true_iff`), which is what
a read's direction after (a `drop` of the one before) shares with the decider's own `drop`. The
proofs use no axiom but `propext` and `Quot.sound`.
-/
module

public import GooseLang.Ext.Net.Deploy

@[expose] public section

namespace Perennial

namespace Net


/-! ## Cheap atoms

The replay decides relations on directions of megabytes (the probe's runs fill the socket
buffers): its atoms avoid walking a direction's bytes where they can. -/

/-- Decides `k ≤ l.length`, walking at most `k` cells. -/
def lenGe {α : Type} : List α → Nat → Bool
  | _, 0 => true
  | [], _ + 1 => false
  | _ :: l, k + 1 => lenGe l k

theorem lenGe_iff {α : Type} {l : List α} {k : Nat} : lenGe l k = true ↔ k ≤ l.length := by
  induction l generalizing k with
  | nil => cases k <;> simp [lenGe]
  | cons x l ih => cases k <;> simp [lenGe, ih]

/-- Decides `a = b ++ c`, walking `a` and `b` together (no `b ++ c` built). -/
def appendEqB {α : Type} [DecidableEq α] : List α → List α → List α → Bool
  | a, [], c => decide (a = c)
  | [], _ :: _, _ => false
  | x :: a, y :: b, c => decide (x = y) && appendEqB a b c

theorem appendEqB_iff {α : Type} [DecidableEq α] {a b c : List α} :
    appendEqB a b c = true ↔ a = b ++ c := by
  induction b generalizing a with
  | nil => simp [appendEqB]
  | cons y b ih =>
    cases a with
    | nil => simp [appendEqB]
    | cons x a => simp [appendEqB, ih]

/-- Decides the equality of two byte lists, at once when they are the same object in memory
(Lean's `withPtrEqDecEq`, a `Decidable` instance like any other: `decide_eq_true_iff` holds of
it), which is what a read's direction after (`drop` of the one before) shares with the decider's
own `drop`, and an unchanged direction with itself. -/
def bytesEqB (a b : List w8) : Bool :=
  @decide (a = b) (withPtrEqDecEq a b (fun _ => inferInstance))

theorem bytesEqB_iff {a b : List w8} : bytesEqB a b = true ↔ a = b :=
  @decide_eq_true_iff (a = b) (withPtrEqDecEq a b (fun _ => inferInstance))

/-- Decides the equality of two directions (`bytesEqB` on their bytes). -/
def dirEqB (a b : NetDir) : Bool := bytesEqB a.bytes b.bytes && decide (a.status = b.status)

theorem dirEqB_iff {a b : NetDir} : dirEqB a b = true ↔ a = b := by
  unfold dirEqB
  cases a; cases b
  simp [bytesEqB_iff]

/-! ## Reads -/

/-- Decides `ReadAvail st d n r d'`: its `∃ k` is the count of the bytes `r` returns. -/
def readAvailB (st : NetEnd) (d : NetDir) (n : Nat) (r : ReadRes) (d' : NetDir) : Bool :=
  (match r with
   | .bytes bs => decide (1 ≤ bs.length ∧ bs.length ≤ n) && lenGe d.bytes bs.length &&
       decide (bs = d.bytes.take bs.length) && dirEqB d' { d with bytes := d.bytes.drop bs.length }
   | _ => false) ||
  (decide (d.bytes = [] ∧ d.status ≠ .open ∧ r = .eof) && dirEqB d' d) ||
  (decide (d.status = .cut ∧ d.bytes = [] ∧ r = .err .sys) && dirEqB d' d) ||
  (decide (st.rdl = true ∧ r = .err .timeout) && dirEqB d' d)

theorem readAvailB_iff {st : NetEnd} {d : NetDir} {n : Nat} {r : ReadRes} {d' : NetDir} :
    readAvailB st d n r d' = true ↔ ReadAvail st d n r d' := by
  unfold readAvailB ReadAvail
  cases r with
  | bytes bs =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, dirEqB_iff, lenGe_iff,
      ReadRes.bytes.injEq, reduceCtorEq, and_false, false_and, or_false, and_assoc]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩
      exact ⟨bs.length, h1, h2, h3, h4, h5⟩
    · rintro ⟨k, h1, h2, h3, rfl, h5⟩
      have hl : (d.bytes.take k).length = k := by simp [List.length_take]; omega
      rw [hl]; exact ⟨h1, h2, h3, rfl, h5⟩
  | eof => simp [dirEqB_iff, and_assoc]
  | err e => simp [dirEqB_iff, and_assoc]

/-- The prefix a cut at a read keeps, as the read's result `r` and the direction after, `d'`,
determine it: the bytes returned and those left, nothing for EOF, else the bytes left. -/
def cutKeep (r : ReadRes) (d' : NetDir) : Nat :=
  match r with
  | .bytes bs => bs.length + d'.bytes.length
  | .eof => 0
  | _ => d'.bytes.length

/-- The cut's `∃ k` of `ReadOutcome` is unique: `cutKeep r d'`. -/
theorem cut_unique {st : NetEnd} {d : NetDir} {n k : Nat} {r : ReadRes} {d' : NetDir}
    (hk : k ≤ d.bytes.length) (h : ReadAvail st ⟨d.bytes.take k, .cut⟩ n r d') :
    k = cutKeep r d' := by
  have hl : (d.bytes.take k).length = k := by simp [List.length_take]; omega
  unfold ReadAvail at h
  rcases h with ⟨j, -, -, hj, rfl, rfl⟩ | ⟨hb, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
  · simp only [cutKeep]
    have := List.take_append_drop j (d.bytes.take k)
    have h2 := congrArg List.length this
    simp only [List.length_append] at h2
    simp only at hj ⊢
    omega
  · simp only at hb
    simp only [cutKeep]
    rw [hb] at hl; simp at hl; omega
  · simp only [cutKeep]; exact hl.symm
  · simp only [cutKeep]; exact hl.symm

/-- Decides `ReadOutcome st d n r d'`: a read as the direction is, or a cut keeping
`cutKeep r d'` bytes first. -/
def readOutcomeB (st : NetEnd) (d : NetDir) (n : Nat) (r : ReadRes) (d' : NetDir) : Bool :=
  if st.closed then decide (r = .err .closed) && dirEqB d' d
  else if n = 0 then decide (r = .bytes []) && dirEqB d' d
  else readAvailB st d n r d' ||
    (lenGe d.bytes (cutKeep r d') && readAvailB st ⟨d.bytes.take (cutKeep r d'), .cut⟩ n r d')

theorem readOutcomeB_iff {st : NetEnd} {d : NetDir} {n : Nat} {r : ReadRes} {d' : NetDir} :
    readOutcomeB st d n r d' = true ↔ ReadOutcome st d n r d' := by
  unfold readOutcomeB ReadOutcome
  split
  · simp [dirEqB_iff]
  split
  · simp [dirEqB_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, lenGe_iff, readAvailB_iff]
  constructor
  · rintro (h | ⟨hk, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨_, hk, h⟩
  · rintro (h | ⟨k, hk, h⟩)
    · exact Or.inl h
    · have := cut_unique hk h
      subst this
      exact Or.inr ⟨hk, h⟩

/-! ## Writes, closes, deadlines -/

/-- Decides `d' = { d with bytes := d.bytes ++ xs }` in one walk (no append built). -/
def dirAppEqB (d' d : NetDir) (xs : List w8) : Bool :=
  decide (d'.status = d.status) && appendEqB d'.bytes d.bytes xs

theorem dirAppEqB_iff {d' d : NetDir} {xs : List w8} :
    dirAppEqB d' d xs = true ↔ d' = { d with bytes := d.bytes ++ xs } := by
  obtain ⟨b', s'⟩ := d'
  obtain ⟨b, s⟩ := d
  simp [dirAppEqB, appendEqB_iff, and_comm]

/-- Decides `WriteOutcome st d rs k res d'` (one step of a `Write`, its count `k` given): the
definition's case split, its atoms decided (`lenGe`, `dirEqB`, `dirAppEqB`). -/
def writeOutcomeB (st : NetEnd) (d : NetDir) (rs : List w8) (k : Nat) (res : Option NetErr)
    (d' : NetDir) : Bool :=
  if st.closed then decide (k = 0) && (decide (res = some .closed) && dirEqB d' d)
  else match d.status with
  | .fin => decide (k = 0) && (dirEqB d' d &&
      decide (res = some .sys ∨ (st.wdl = true ∧ res = some .timeout)))
  | .cut => dirEqB d' d && ((lenGe rs k && (decide (1 ≤ k ∨ rs = []) && decide (res = none))) ||
      decide (k = 0 ∧ (res = some .sys ∨ (st.wdl = true ∧ res = some .timeout))))
  | .open =>
    (lenGe rs k && (decide (1 ≤ k ∨ rs = []) && (decide (res = none) &&
      dirAppEqB d' d (rs.take k)))) ||
    ((decide (k = 0) && (decide (res = some .sys) && dirEqB d' { d with status := .cut })) ||
     (decide (st.wdl = true) && (decide (k = 0) && (decide (res = some .timeout) && dirEqB d' d))))

theorem writeOutcomeB_iff {st : NetEnd} {d : NetDir} {rs : List w8} {k : Nat}
    {res : Option NetErr} {d' : NetDir} :
    writeOutcomeB st d rs k res d' = true ↔ WriteOutcome st d rs k res d' := by
  unfold writeOutcomeB WriteOutcome
  split
  · simp only [Bool.and_eq_true, decide_eq_true_eq, dirEqB_iff]
  · cases hs : d.status <;>
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, dirEqB_iff, lenGe_iff,
        dirAppEqB_iff, hs]

/-- Decides `CloseOutcome st d res st' d'`. -/
def closeOutcomeB (st : NetEnd) (d : NetDir) (res : Option NetErr) (st' : NetEnd) (d' : NetDir) :
    Bool :=
  if st.closed then decide (res = some .closed) && (decide (st' = st) && dirEqB d' d)
  else decide (res = none) && (decide (st' = { st with closed := true }) && dirEqB d' d.shut)

theorem closeOutcomeB_iff {st : NetEnd} {d : NetDir} {res : Option NetErr} {st' : NetEnd}
    {d' : NetDir} : closeOutcomeB st d res st' d' = true ↔ CloseOutcome st d res st' d' := by
  unfold closeOutcomeB CloseOutcome
  split <;> simp only [Bool.and_eq_true, decide_eq_true_eq, dirEqB_iff]

/-- Decides `CloseWriteOutcome st d res d'`. -/
def closeWriteOutcomeB (st : NetEnd) (d : NetDir) (res : Option NetErr) (d' : NetDir) : Bool :=
  if st.closed then decide (res = some .closed) && dirEqB d' d
  else (decide (res = none) && dirEqB d' d.shut) || (decide (res = some .sys) && dirEqB d' d)

theorem closeWriteOutcomeB_iff {st : NetEnd} {d : NetDir} {res : Option NetErr} {d' : NetDir} :
    closeWriteOutcomeB st d res d' = true ↔ CloseWriteOutcome st d res d' := by
  unfold closeWriteOutcomeB CloseWriteOutcome
  split <;> simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, dirEqB_iff]

/-- Decides `DeadlineOutcome st kind set res st'`. -/
def deadlineOutcomeB (st : NetEnd) (kind : w64) (set : Bool) (res : Option NetErr) (st' : NetEnd) :
    Bool :=
  if st.closed then decide (res = some .closed ∧ st' = st)
  else decide (res = none ∧
    st' = { st with rdl := if kind = W64 2 then st.rdl else set,
                    wdl := if kind = W64 1 then st.wdl else set })

theorem deadlineOutcomeB_iff {st : NetEnd} {kind : w64} {set : Bool} {res : Option NetErr}
    {st' : NetEnd} : deadlineOutcomeB st kind set res st' = true ↔ DeadlineOutcome st kind set res st' := by
  unfold deadlineOutcomeB DeadlineOutcome; split <;> simp

/-- Decides `LisCloseOutcome isOpen res isOpen'`. -/
def lisCloseOutcomeB (isOpen : Bool) (res : Option NetErr) (isOpen' : Bool) : Bool :=
  if isOpen then decide (res = none ∧ isOpen' = false)
  else decide (res = some .closed ∧ isOpen' = false)

theorem lisCloseOutcomeB_iff {isOpen : Bool} {res : Option NetErr} {isOpen' : Bool} :
    lisCloseOutcomeB isOpen res isOpen' = true ↔ LisCloseOutcome isOpen res isOpen' := by
  unfold lisCloseOutcomeB LisCloseOutcome; split <;> simp

/-- Decides `IsEnd e c s`. -/
def isEndB (e : w64) (c : Nat) (s : Bool) : Bool :=
  decide (2 * c + 1 < 2 ^ 64) && decide (e = endId c s)

theorem isEndB_iff {e : w64} {c : Nat} {s : Bool} : isEndB e c s = true ↔ IsEnd e c s := by
  simp [isEndB, IsEnd]

/-! ## Association lists and `lisAccepts` -/

/-- The lookup of `a` in an association list: its first pair's value. -/
def alGet {K V : Type} [DecidableEq K] (l : List (K × V)) (a : K) : Option V :=
  (l.find? (fun x => decide (x.1 = a))).map (·.2)

@[simp] theorem alGet_nil {K V : Type} [DecidableEq K] (a : K) : alGet ([] : List (K × V)) a = none :=
  rfl

theorem alGet_cons {K V : Type} [DecidableEq K] (k : K) (v : V) (l : List (K × V)) (a : K) :
    alGet ((k, v) :: l) a = if k = a then some v else alGet l a := by
  unfold alGet; by_cases h : k = a <;> simp [h]

theorem alGet_isSome {K V : Type} [DecidableEq K] (l : List (K × V)) (a : K) :
    (alGet l a).isSome ↔ ∃ x ∈ l, x.1 = a := by
  unfold alGet; simp [List.find?_isSome]

/-- The map of an association list is its lookup. -/
theorem ofList_lookup {K V : Type} [DecidableEq K] (l : List (K × V)) (a : K) :
    (GMap.ofList l).lookup a = alGet l a := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨k, v⟩ := x
    rw [alGet_cons, ← ih]; rfl

/-- Decides `lisAccepts la a`: its `∃ p` is `wildPort la`. -/
def lisAcceptsB (la a : GoString) : Bool :=
  decide (la = a) ||
  match wildPort la with
  | none => false
  | some p => decide (portOf a = some p)

theorem lisAcceptsB_iff {la a : GoString} : lisAcceptsB la a = true ↔ lisAccepts la a := by
  unfold lisAcceptsB lisAccepts
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  apply or_congr Iff.rfl
  cases hw : wildPort la with
  | none => simp
  | some p => simp

/-- The examples' addresses, decided. -/
example : addrOk go!"127.0.0.1:7101" = true := by decide
example : lisAcceptsB go!":7101" go!"127.0.0.1:7101" = true := by decide
example : lisAcceptsB go!"127.0.0.2:7101" go!"127.0.0.1:7101" = false := by decide

end Net

end Perennial
