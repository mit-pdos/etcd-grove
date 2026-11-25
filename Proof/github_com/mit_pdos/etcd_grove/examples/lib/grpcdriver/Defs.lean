/- Lean-first (no Rocq counterpart).

# `lib/grpcdriver`: the driver's own predicates

* **Random words** (`wordOk w`): at most `maxLen` (16) letters `a`-`z` (`randomWord`).
* **Fresh values** (`mkVal id w`, `freshValue`): `"v"`, the decimal digits of the call's id
  (`strconv.FormatUint(id, 10)`), then a random word. Digits are no letters, so the value determines
  the id (`mkVal_inj`): two values of distinct ids differ.
* **The client's ids** (`isCtr γid γb c`, persistent): the `counter` `c`'s mutex owns its `next`
  field, the authority of the ids issued so far (the ghost map `γid`: `issued start n`, the ids
  `start`, ..., `start + n - 1`, wrapping) and a budget: the take credits handed out (`ownToks γb`,
  `Perennial/Proof/TokSet.lean`) and `n` together never exceed `ctrBudget` (`33`: at most 4
  workers making at most 8 operations, each taking at most one id, and one call after `Close`). So
  the `n` ids are distinct (`n < 2 ^ 64`), and `take` hands out the token `idTok γid id` of a fresh
  id. As net/rpc's driver's (`Net/Proof/.../rpcdriver/Defs.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.Base
public import Perennial.Proof.TokSet
public import Perennial.Proof.internal.strconv.FormatBasics

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

/-! ## Words and fresh values -/

/-- A byte is a lower-case letter (`a`-`z`). -/
def isLetter (b : w8) : Prop := 97 ≤ b.toNat ∧ b.toNat ≤ 122

/-- A byte is a decimal digit (`0`-`9`). -/
def isDigit (b : w8) : Prop := 48 ≤ b.toNat ∧ b.toNat ≤ 57

/-- A random word (`randomWord`): at most 16 letters. -/
def wordOk (w : GoString) : Prop := w.length ≤ 16 ∧ ∀ b ∈ w, isLetter b

/-- The fresh value of the id `id` and the word `w` (`freshValue`). -/
def mkVal (id : w64) (w : GoString) : GoString :=
  go!"v" ++ internal.strconv.fmtUint id (W64 10) ++ w

theorem fmtUint10_digits (n : w64) : ∀ b ∈ internal.strconv.fmtUint n (W64 10), isDigit b := by
  intro b hb
  unfold internal.strconv.fmtUint at hb
  rw [dif_pos (by decide)] at hb
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hb
  have hd10 : d < 10 := internal.strconv.baseDigits_lt 10 (by decide) n.toNat d (by simpa using hd)
  have key : ∀ e : Fin 10, isDigit (internal.strconv.digitChar e.val) := by
    unfold isDigit; decide +kernel
  exact key ⟨d, hd10⟩

theorem fmtUint10_inj {a b : w64}
    (h : internal.strconv.fmtUint a (W64 10) = internal.strconv.fmtUint b (W64 10)) : a = b := by
  unfold internal.strconv.fmtUint at h
  rw [dif_pos (by decide), dif_pos (by decide)] at h
  have hl := internal.strconv.map_digitChar_inj 10 (by decide) _ _
    (internal.strconv.baseDigits_lt 10 (by decide) a.toNat)
    (internal.strconv.baseDigits_lt 10 (by decide) b.toNat) (by simpa using h)
  have ha := internal.strconv.digitsVal_baseDigits 10 (by decide) a.toNat
  have hb := internal.strconv.digitsVal_baseDigits 10 (by decide) b.toNat
  rw [hl] at ha
  exact BitVec.eq_of_toNat_eq (ha.symm.trans hb)

/-- Digits followed by letters: the digits are determined. -/
theorem digits_append_letters : ∀ (d d' x y : List w8), (∀ c ∈ d, isDigit c) → (∀ c ∈ d', isDigit c) →
    (∀ c ∈ x, isLetter c) → (∀ c ∈ y, isLetter c) → d ++ x = d' ++ y → d = d'
  | [], [], _, _, _, _, _, _, _ => rfl
  | [], c :: d', x, y, _, hd', hx, _, h => by
    exfalso
    cases x with
    | nil => simp at h
    | cons c' x =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      have h1 := hx c' (by simp); have h2 := hd' c (by simp)
      rw [h.1] at h1; unfold isLetter at h1; unfold isDigit at h2; omega
  | c :: d, [], x, y, hd, _, _, hy, h => by
    exfalso
    cases y with
    | nil => simp at h
    | cons c' y =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      have h1 := hy c' (by simp); have h2 := hd c (by simp)
      rw [← h.1] at h1; unfold isLetter at h1; unfold isDigit at h2; omega
  | c :: d, c' :: d', x, y, hd, hd', hx, hy, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    rw [h.1, digits_append_letters d d' x y (fun b hb => hd b (by simp [hb]))
      (fun b hb => hd' b (by simp [hb])) hx hy h.2]

/-- **A fresh value determines its id.** -/
theorem mkVal_inj {a b : w64} {w w' : GoString} (hw : wordOk w) (hw' : wordOk w')
    (h : mkVal a w = mkVal b w') : a = b := by
  unfold mkVal at h
  simp only [List.append_assoc, List.append_cancel_left_eq] at h
  exact fmtUint10_inj (digits_append_letters _ _ _ _ (fmtUint10_digits a) (fmtUint10_digits b)
    hw.2 hw'.2 h)

/-- A fresh value is short: `"v"`, at most 20 digits and at most 16 letters. -/
theorem mkVal_length (id : w64) (w : GoString) (hw : wordOk w) : (mkVal id w).length ≤ 37 := by
  unfold mkVal
  have := internal.strconv.fmtUint10_length_le id
  have := hw.1
  simp only [List.length_append]
  simp only [List.length] at *
  omega

/-! ## The client's ids -/

/-- The bound on the ids the client takes (see the file header). -/
def ctrBudget : Nat := 33

/-- The ids `start`, ..., `start + n - 1`. -/
def issued (start : w64) : Nat → GMap w64 Unit
  | 0 => ∅
  | n + 1 => (issued start n).insert (start + W64 n) ()

/-- The next id is fresh while fewer than `2 ^ 64` were issued. -/
theorem issued_fresh (start : w64) : ∀ (n j : Nat), n ≤ j → j < 2 ^ 64 →
    (issued start n).lookup (start + W64 j) = none
  | 0, _, _, _ => rfl
  | n + 1, j, h1, h2 => by
    simp only [issued]
    rw [GMap.lookup_insert_ne _ _ ?_]
    · exact issued_fresh start n j (by omega) h2
    · intro h
      have h' : (W64 n : w64) = W64 j := by
        have := congrArg (fun x => x - start) h
        simpa using this
      word

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

/-- **The package's variable** (`drvFacts`, persistent): `reached` holds a function whose calls
return (its body is empty). The package's `isPkgInit` fact is `True` (generated `Init.lean`); the
client's boot gets this from the package's first initialization. -/
def drvFacts : IProp GF :=
  iprop(∃ f : GoFunc, globalAddr reached ↦□ f ∗
    □ ∀ s : GoString, WP (App (Val #f) (Val #s)) {{ v, ⌜v = #()⌝ }})

instance drvFacts_persistent : Persistent (drvFacts (GF := GF)) := by
  unfold drvFacts; infer_instance

/-- The token of the call id `id` (exclusive): an element of the ghost map `γid`. -/
def idTok (γid : GName) (id : w64) : IProp GF :=
  ghostMapElem (K := w64) (V := Unit) γid id (DFrac.own 1) ()

/-- The counter's invariant (see the file header). -/
def ctrInv (γid γb : GName) (start : w64) (c : Loc) : IProp GF :=
  iprop(∃ n k : Nat, structFieldRef counter go!"next" c ↦ (start + W64 n) ∗
    ghostMapAuth (K := w64) (V := Unit) γid 1 (issued start n) ∗ ownTokAuth γb k ∗
    ⌜n + k ≤ ctrBudget⌝)

/-- `c` is the client's counter of ids (persistent; see the file header). -/
def isCtr (γid γb : GName) (c : Loc) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗
    ∃ start : w64, sync.isMutex (structFieldRef counter go!"mu" c) (ctrInv γid γb start c))

instance isCtr_persistent (γid γb : GName) (c : Loc) : Persistent (isCtr (GF := GF) γid γb c) := by
  unfold isCtr; infer_instance

end defs

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

end Perennial
