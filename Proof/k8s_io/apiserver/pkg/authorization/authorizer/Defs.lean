/-
Lean-first (no Rocq counterpart).

# Conditional authorization's vocabulary (KEP-5681, `k8s.io/apiserver/pkg/authorization/authorizer`)

What the specs of the authorizer package, of the union authorizer and of the driver
(`examples/k8s/authz`) are written in. The theorem they serve is robustness (no panic) of the
driver's `Main`, whose checks C1-C3 are panics; so the vocabulary says only what absence of panics
and those three checks need, and nothing about reasons, errors or the request.

**Decisions.** A `ConditionsAwareDecision` value is immutable after construction (its fields are
private, its constructors and the union builder the only producers, and they never share a slice
or set with the caller), so it is described by a *persistent* predicate `isDecision d m` against a
pure model `m : Dec`: unconditional `deny`/`allow`/`noOpinion`; `cmap dn no al`, a conditions map
of three lists of conditions (`Condition` interface values, each `isCondition`); `union ks`, a
union of sub-decisions (recursively). The decision's type tag is the model's constructor, and for a
union the memoized fields (`containsUnconditionalAllowOrDeny`, the set
`subDecisionsPossibleDecisions`) agree with the children's.

**Possible decisions.** `Dec.pd m : PD`, the set of `PossibleDecisions()` as three booleans, as
the Go code computes it: `{Deny}`, `{Allow}`, `{NoOpinion}` for the unconditional ones;
`{NoOpinion} ∪ {Deny | dn ≠ []} ∪ {Allow | al ≠ []}` for a map; for a union, the children's
Allow/Deny, and NoOpinion unless some child contains an unconditional Allow or Deny (`Dec.cuad`).
`PD.failure` is `FailureDecision()`: Deny if Deny is possible, else NoOpinion.

**The invariant (`Dec.WF`).** What every decision the constructors and the builder produce
satisfies, and what makes C2 and C3 provable: a map has a Deny or an Allow condition (the
constructor folds the other cases to unconditional decisions), and a union's children are `WF` and
it has at least two possible decisions (`ToDecision` folds a union with one possible outcome to an
unconditional decision), and unions nest less than `2 ^ 63` deep (`Dec.depth`;
`collectReasonsAndErrors`'s `slices.Concat` panics on a longer path of names: the builder keeps its
children less than `2 ^ 63 - 1` deep, `ownBuilder`, so an authorizer's decision is one level
shallower than the invariant, `caaOk`). Then:

- **C3** (`Dec.failure_mem`): a `WF` decision other than an unconditional Allow has its failure
  decision among its possible decisions (a conditional decision has two possible decisions out of
  three, so Deny or NoOpinion);
- **C2**: the union authorizer's `EvaluateConditions` returns a possible decision of a `WF` union or
  its failure decision (its spec, `Spec/.../union/unionAuthzHandler__EvaluateConditions.lean`),
  whatever the leaves answer: it guards each conditional child's evaluation with the child's
  possible decisions (`Dec.pd_child_allow`, `Dec.pd_child_deny`: a child's Allow or Deny is the
  union's), and it ends with NoOpinion only after every child has evaluated to NoOpinion, which a
  child containing an unconditional Allow or Deny cannot (`Dec.noOpinion_of_not_cuad`);
- **C1**: possible decisions are among Deny, Allow, NoOpinion (`PD.has_valid`).

**Untrusted code.** A `Condition` (`isCondition`), an `Authorizer` (`isAuthorizer`) and the
evaluation functions (`maybeEvalFnOk`, `evalFnOk`) are interface or function values supplied by the
caller (the driver's arbitrary leaves): what the library needs of them is that their methods can be
called (non-`nil`, persistent triples) and, for an authorizer's `ConditionsAwareAuthorize`, that it
returns a `WF` decision (the leaves build theirs with the library's constructors). Their results
are otherwise arbitrary: `EvaluateConditions` may return any decision word, reason and error.

**Errors** (2026-11-20, after `lean`'s fmt soundness removed `fmt.ErrorfAny`): the library formats
the errors of decisions (`collectReasonsAndErrors`: `fmt.Errorf("%s: %w", ...)`) and of evaluation
results (`conditionsToAppliedErroredUnevaluated`), so every error a decision or a result holds, and
every error the untrusted functions return, is `nil` or an error tree
(`utilerrors.errTreeOrNil`: `fmt` can call its `Error()`, and an `aggregate` of such errors is one
too): `isDecisionRaw`'s unconditional cases, `resOk`, `evalCallOk`, `authzCallOk`, and the builder's
errors (`ownBuilder`).
-/
module

public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.Base
public import Proof.k8s_io.apimachinery.pkg.util.sets.Defs
public import Proof.k8s_io.apimachinery.pkg.util.errors.Defs
public import Perennial.Proof.strings.JoinBounded

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authorizer

open Iris Iris.BI k8s_io.apiserver.pkg.authorization.authorizer

section pure
variable [GooseExts]

/-! ## Possible decisions -/

/-- A set of `Decision`s among Deny (`0`), Allow (`1`), NoOpinion (`2`): what
`PossibleDecisions()` returns. -/
structure PD where
  deny : Bool
  allow : Bool
  noOpinion : Bool
deriving DecidableEq

/-- Membership of a decision word in a `PD`. -/
def PD.has (p : PD) (k : w64) : Bool :=
  Bool.or (Bool.or (Bool.and (decide (k = W64 0)) p.deny) (Bool.and (decide (k = W64 1)) p.allow))
    (Bool.and (decide (k = W64 2)) p.noOpinion)

/-- The number of decisions in a `PD` (`Len()`). -/
def PD.card (p : PD) : Nat := p.deny.toNat + p.allow.toNat + p.noOpinion.toNat

/-- `FailureDecision()`: Deny if Deny is possible, else NoOpinion. -/
def PD.failure (p : PD) : w64 := if p.deny then W64 0 else W64 2

/-- The union of two `PD`s. -/
def PD.or (p q : PD) : PD :=
  ⟨Bool.or p.deny q.deny, Bool.or p.allow q.allow, Bool.or p.noOpinion q.noOpinion⟩

/-- The empty `PD`. -/
def PD.empty : PD := ⟨false, false, false⟩

/-- A Go set of decisions (`sets.Set[Decision]`, a map) holds exactly the decisions of `p`. -/
def setIs (s : GMap w64 sets.Elem) (p : PD) : Prop := ∀ k : w64, (s !! k).isSome = p.has k

/-- **C1**: a possible decision is Deny, Allow or NoOpinion. -/
theorem PD.has_valid (p : PD) (k : w64) (h : p.has k = true) :
    k = W64 0 ∨ k = W64 1 ∨ k = W64 2 := by
  unfold PD.has at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ((⟨h, -⟩ | ⟨h, -⟩) | ⟨h, -⟩)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-! ## The model of decisions -/

/-- The model of a `ConditionsAwareDecision`: unconditional, a conditions map (its Deny,
NoOpinion and Allow conditions), or a union of sub-decisions. Reasons, errors and the children's
names are not modelled. -/
inductive Dec where
  | deny
  | allow
  | noOpinion
  | cmap (dn no al : List GoInterface)
  | union (ks : List Dec)

mutual
/-- `ContainsUnconditionalAllowOrDeny()`. -/
def Dec.cuad : Dec → Bool
  | .deny => true
  | .allow => true
  | .noOpinion => false
  | .cmap _ _ _ => false
  | .union ks => Dec.cuadL ks
/-- Some decision of the list contains an unconditional Allow or Deny. -/
def Dec.cuadL : List Dec → Bool
  | [] => false
  | k :: ks => Bool.or (Dec.cuad k) (Dec.cuadL ks)
end

mutual
/-- `PossibleDecisions()`. -/
def Dec.pd : Dec → PD
  | .deny => ⟨true, false, false⟩
  | .allow => ⟨false, true, false⟩
  | .noOpinion => ⟨false, false, true⟩
  | .cmap dn _ al => ⟨!dn.isEmpty, !al.isEmpty, true⟩
  | .union ks => ⟨(Dec.subL ks).deny, (Dec.subL ks).allow, !Dec.cuadL ks⟩
/-- The union of the possible decisions of a list of decisions (a union's memoized
`subDecisionsPossibleDecisions`). -/
def Dec.subL : List Dec → PD
  | [] => PD.empty
  | k :: ks => PD.or (Dec.pd k) (Dec.subL ks)
end

mutual
/-- The nesting depth of unions: `0` for a leaf, one more than its deepest child for a union
(`collectReasonsAndErrors` builds, for each decision it visits, the path of names down to it in a
`[]string` of that length with `slices.Concat`, which panics when the length reaches `2 ^ 63`). -/
def Dec.depth : Dec → Nat
  | .deny => 0
  | .allow => 0
  | .noOpinion => 0
  | .cmap _ _ _ => 0
  | .union ks => Dec.depthL ks + 1
/-- The depth of the deepest decision of the list (`0` for none). -/
def Dec.depthL : List Dec → Nat
  | [] => 0
  | k :: ks => max (Dec.depth k) (Dec.depthL ks)
end

/-- A child is less deep than its union. -/
theorem Dec.depth_le_depthL : ∀ (ks : List Dec) (i : Nat) (k : Dec), ks[i]? = some k →
    k.depth ≤ Dec.depthL ks
  | [], _, _, h => by simp at h
  | k' :: ks, 0, k, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
    simp only [Dec.depthL]; omega
  | k' :: ks, i + 1, k, h => by
    simp only [List.getElem?_cons_succ] at h
    have := Dec.depth_le_depthL ks i k h
    simp only [Dec.depthL]; omega

/-- A list's depth bounded by each element's. -/
theorem Dec.depthL_le_of : ∀ (ks : List Dec) (n : Nat),
    (∀ (i : Nat) (k : Dec), ks[i]? = some k → k.depth ≤ n) → Dec.depthL ks ≤ n
  | [], _, _ => Nat.zero_le _
  | k :: ks, n, h => by
    simp only [Dec.depthL]
    have h1 := h 0 k rfl
    have h2 := Dec.depthL_le_of ks n (fun i k' hk => h (i + 1) k' (by simpa using hk))
    omega

/-- The depth of a list with one more decision. -/
theorem Dec.depthL_append : ∀ (ks : List Dec) (m : Dec),
    Dec.depthL (ks ++ [m]) = max (Dec.depthL ks) m.depth
  | [], m => by simp [Dec.depthL]
  | k :: ks, m => by
    simp only [List.cons_append, Dec.depthL, Dec.depthL_append ks m]; omega

/-- The depth of a builder's children after `Add` (which keeps them when they already contain an
unconditional Allow or Deny). -/
theorem Dec.depthL_add_le (c : Bool) (ks : List Dec) (m : Dec) (n : Nat) (h1 : Dec.depthL ks ≤ n)
    (h2 : m.depth ≤ n) : Dec.depthL (if c then ks else ks ++ [m]) ≤ n := by
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte, Dec.depthL_append]; omega
  · simpa using h1

mutual
/-- **The invariant** of the decisions the constructors and the builder produce (see the file
header). -/
def Dec.WF : Dec → Prop
  | .deny => True
  | .allow => True
  | .noOpinion => True
  | .cmap dn _ al => dn ≠ [] ∨ al ≠ []
  | .union ks => Dec.WFL ks ∧ 2 ≤ (Dec.pd (.union ks)).card ∧ Dec.depthL ks + 1 < 2 ^ 63
/-- Every decision of the list is `WF`. -/
def Dec.WFL : List Dec → Prop
  | [] => True
  | k :: ks => Dec.WF k ∧ Dec.WFL ks
end

/-- An unconditional Allow (the one decision whose failure decision is not possible). -/
def Dec.isAllow : Dec → Bool
  | .allow => true
  | _ => false

/-- The decision is a union (`IsUnion()`). -/
def Dec.isUnion : Dec → Bool
  | .union _ => true
  | _ => false

/-- The decision is a conditions map (`IsConditionsMap()`). -/
def Dec.isCMap : Dec → Bool
  | .cmap _ _ _ => true
  | _ => false

/-- The decision is unconditional (`IsUnconditional()`). -/
def Dec.isUnconditional : Dec → Bool
  | .deny => true
  | .allow => true
  | .noOpinion => true
  | _ => false

/-- The decision's type tag (`decisionType`). -/
def Dec.tag : Dec → w64
  | .deny => W64 0
  | .allow => W64 11
  | .noOpinion => W64 12
  | .cmap _ _ _ => W64 13
  | .union _ => W64 14

/-! ## The invariant's consequences: C1-C3 -/

/-- **C3**: a `WF` decision other than an unconditional Allow has its failure decision among its
possible decisions. -/
theorem Dec.failure_mem (m : Dec) (hwf : m.WF) (hna : m.isAllow = false) :
    m.pd.has m.pd.failure = true := by
  cases m with
  | deny => rfl
  | allow => simp [Dec.isAllow] at hna
  | noOpinion => rfl
  | cmap dn no al =>
    simp only [Dec.pd, PD.failure, PD.has]
    cases dn <;> rfl
  | union ks =>
    simp only [Dec.WF] at hwf
    obtain ⟨-, hc, -⟩ := hwf
    have key : ∀ sd sa sn : Bool, 2 ≤ (PD.mk sd sa sn).card →
        (PD.mk sd sa sn).has (PD.mk sd sa sn).failure = true := by decide
    exact key _ _ _ hc

/-- A union child's Allow is a possible decision of the union. -/
theorem Dec.pd_child_allow (ks : List Dec) (k : Dec) (hk : k ∈ ks) (h : k.pd.allow = true) :
    (Dec.pd (.union ks)).allow = true := by
  simp only [Dec.pd]
  induction ks with
  | nil => simp at hk
  | cons k' ks ih =>
    simp only [Dec.subL, PD.or, Bool.or_eq_true]
    rcases List.mem_cons.mp hk with rfl | hk
    · exact Or.inl h
    · exact Or.inr (ih hk)

/-- A union child's Deny is a possible decision of the union. -/
theorem Dec.pd_child_deny (ks : List Dec) (k : Dec) (hk : k ∈ ks) (h : k.pd.deny = true) :
    (Dec.pd (.union ks)).deny = true := by
  simp only [Dec.pd]
  induction ks with
  | nil => simp at hk
  | cons k' ks ih =>
    simp only [Dec.subL, PD.or, Bool.or_eq_true]
    rcases List.mem_cons.mp hk with rfl | hk
    · exact Or.inl h
    · exact Or.inr (ih hk)

/-- A union none of whose children contains an unconditional Allow or Deny may evaluate to
NoOpinion. -/
theorem Dec.noOpinion_of_not_cuad (ks : List Dec) (h : ∀ k ∈ ks, k.cuad = false) :
    (Dec.pd (.union ks)).noOpinion = true := by
  simp only [Dec.pd, Bool.not_eq_true']
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    simp only [Dec.cuadL, Bool.or_eq_false_iff]
    exact ⟨h k (List.mem_cons_self ..), ih fun k' hk' => h k' (List.mem_cons_of_mem _ hk')⟩

/-- A decision containing an unconditional Allow or Deny cannot evaluate to NoOpinion. -/
theorem Dec.not_noOpinion_of_cuad (m : Dec) (h : m.cuad = true) : m.pd.noOpinion = false := by
  cases m with
  | deny => rfl
  | allow => rfl
  | noOpinion => simp [Dec.cuad] at h
  | cmap _ _ _ => simp [Dec.cuad] at h
  | union ks => simp only [Dec.pd, Dec.cuad] at h ⊢; simp [h]

/-- A possible decision of a `WF` decision is Deny, Allow or NoOpinion, and so is its failure
decision. -/
theorem PD.failure_valid (p : PD) : p.failure = W64 0 ∨ p.failure = W64 2 := by
  unfold PD.failure; split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- An unconditional Deny (`IsDeny()`). -/
def Dec.isDeny : Dec → Bool
  | .deny => true
  | _ => false

/-- An unconditional NoOpinion (`IsNoOpinion()`). -/
def Dec.isNoOpinion : Dec → Bool
  | .noOpinion => true
  | _ => false

/-- The unconditional decision of a decision word, as `ConditionsAwareDecisionFromParts` makes it:
Allow, NoOpinion, and Deny for every other word. -/
def Dec.ofWord (k : w64) : Dec :=
  if k = W64 1 then .allow else if k = W64 2 then .noOpinion else .deny

theorem Dec.ofWord_WF (k : w64) : (Dec.ofWord k).WF := by
  unfold Dec.ofWord; split
  · trivial
  · split <;> trivial

theorem Dec.ofWord_depth (k : w64) : (Dec.ofWord k).depth = 0 := by
  unfold Dec.ofWord; split
  · rfl
  · split <;> rfl

/-! The type tests of a decision value read its tag (`decisionType`), its model's `Dec.tag`. -/

theorem Dec.tag_allow (m : Dec) : decide (m.tag = W64 11) = m.isAllow := by
  cases m <;> rfl
theorem Dec.tag_deny (m : Dec) : decide (m.tag = W64 0) = m.isDeny := by
  cases m <;> rfl
theorem Dec.tag_noOpinion (m : Dec) : decide (m.tag = W64 12) = m.isNoOpinion := by
  cases m <;> rfl
theorem Dec.tag_cmap (m : Dec) : decide (m.tag = W64 13) = m.isCMap := by
  cases m <;> rfl
theorem Dec.tag_union (m : Dec) : decide (m.tag = W64 14) = m.isUnion := by
  cases m <;> rfl

/-! ## Sizes, for `strings.Join` (fmt stage 1, #9 7126397740 (3))

`ToDecision` joins, for each leaf of its children whose decision is the one possible outcome, a
string of the leaf's path of names and its reason (`collectReasonsAndErrors`); the union
authorizer's `EvaluateConditions` joins one string per child. Go's `strings.Join` panics on an
output too long for an `int`, so their outputs are bounded: a reason is read by `len` before it is
joined, so it is at most `maxAddr` bytes long (the semantics' string bound), and the names are at
most `N` bytes each (`decNames`); a decision of `size` nodes (`Dec.size`) and `depth` gives
at most `size` strings of at most `(depth + 1) * (N + 2) + maxAddr + 4` bytes each
(`Dec.foldBound`). -/

mutual
/-- The number of nodes of a decision (a leaf is one; a union one more than its children). -/
def Dec.size : Dec → Nat
  | .deny => 1
  | .allow => 1
  | .noOpinion => 1
  | .cmap _ _ _ => 1
  | .union ks => Dec.sizeL ks + 1
/-- The number of nodes of a list of decisions. -/
def Dec.sizeL : List Dec → Nat
  | [] => 0
  | k :: ks => Dec.size k + Dec.sizeL ks
end

theorem Dec.size_pos (m : Dec) : 1 ≤ m.size := by
  cases m <;> simp only [Dec.size] <;> omega

/-- A child is no larger than its siblings together. -/
theorem Dec.size_le_sizeL : ∀ (ks : List Dec) (i : Nat) (k : Dec), ks[i]? = some k →
    k.size ≤ Dec.sizeL ks
  | [], _, _, h => by simp at h
  | k' :: ks, 0, k, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
    simp only [Dec.sizeL]; omega
  | k' :: ks, i + 1, k, h => by
    simp only [List.getElem?_cons_succ] at h
    have := Dec.size_le_sizeL ks i k h
    simp only [Dec.sizeL]; omega

/-- A list of decisions has no more elements than nodes. -/
theorem Dec.length_le_sizeL : ∀ (ks : List Dec), ks.length ≤ Dec.sizeL ks
  | [] => Nat.le_refl _
  | k :: ks => by
    have := Dec.length_le_sizeL ks
    have := Dec.size_pos k
    simp only [List.length_cons, Dec.sizeL]; omega

theorem Dec.sizeL_append : ∀ (ks : List Dec) (m : Dec),
    Dec.sizeL (ks ++ [m]) = Dec.sizeL ks + m.size
  | [], m => by simp [Dec.sizeL]
  | k :: ks, m => by
    simp only [List.cons_append, Dec.sizeL, Dec.sizeL_append ks m]; omega

/-- The size of a builder's children after `Add`. -/
theorem Dec.sizeL_add_le (c : Bool) (ks : List Dec) (m : Dec) (n : Nat)
    (h : Dec.sizeL ks + m.size ≤ n) : Dec.sizeL (if c then ks else ks ++ [m]) ≤ n := by
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte, Dec.sizeL_append]; omega
  · simp only [↓reduceIte]; omega

theorem Dec.sizeL_take_succ : ∀ (ks : List Dec) (i : Nat) (k : Dec), ks[i]? = some k →
    Dec.sizeL (ks.take (i + 1)) = Dec.sizeL (ks.take i) + k.size
  | [], _, _, h => by simp at h
  | k' :: ks, 0, k, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
    simp [Dec.sizeL]
  | k' :: ks, i + 1, k, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.take_succ_cons, Dec.sizeL, Dec.sizeL_take_succ ks i k h]; omega

theorem Dec.sizeL_take_le : ∀ (ks : List Dec) (i : Nat), Dec.sizeL (ks.take i) ≤ Dec.sizeL ks
  | [], _ => by simp [Dec.sizeL]
  | k :: ks, 0 => by simp [Dec.sizeL]
  | k :: ks, i + 1 => by
    simp only [List.take_succ_cons, Dec.sizeL]
    have := Dec.sizeL_take_le ks i; omega

/-- A decision of depth zero is a leaf. -/
theorem Dec.isUnion_of_depth_zero (m : Dec) (h : m.depth = 0) : m.isUnion = false := by
  cases m <;> simp_all [Dec.depth, Dec.isUnion]

theorem Dec.size_of_depth_zero (m : Dec) (h : m.depth = 0) : m.size = 1 := by
  cases m <;> simp_all [Dec.depth, Dec.size]

/-- The bound on what `ToDecision` and `EvaluateConditions` join for a decision of at most `S`
nodes, `D` deep, with names of at most `N` bytes: at most `S` strings of a path of names (at
most `D + 1` of them, with their separators) and a reason (at most `maxAddr` bytes) with their
punctuation and separators. -/
def Dec.foldBound (S D N : Nat) : Nat := S * ((D + 1) * (N + 2) + maxAddr.toNat + 6)

theorem Dec.foldBound_mono {S S' D D' N : Nat} (hS : S ≤ S') (hD : D ≤ D') :
    Dec.foldBound S D N ≤ Dec.foldBound S' D' N := by
  unfold Dec.foldBound
  apply Nat.mul_le_mul hS
  have := Nat.mul_le_mul_right (N + 2) (Nat.add_le_add_right hD 1)
  omega

/-- **The decision `m` fits `strings.Join`** with names of at most `N` bytes. -/
def Dec.foldFits (N : Nat) (m : Dec) : Prop :=
  Dec.foldBound m.size m.depth N < _root_.Perennial.strings.joinMax

theorem Dec.foldFits_of_le (N : Nat) (m : Dec) (S D : Nat) (hS : m.size ≤ S) (hD : m.depth ≤ D)
    (h : Dec.foldBound S D N < _root_.Perennial.strings.joinMax) : Dec.foldFits N m :=
  Nat.lt_of_le_of_lt (Dec.foldBound_mono hS hD) h

/-- A union's child fits if the union does. -/
theorem Dec.foldFits_child (N : Nat) (ks : List Dec) (i : Nat) (k : Dec) (hk : ks[i]? = some k)
    (h : Dec.foldFits N (.union ks)) : Dec.foldFits N k := by
  have h1 := Dec.size_le_sizeL ks i k hk
  have h2 := Dec.depth_le_depthL ks i k hk
  unfold Dec.foldFits at h ⊢
  simp only [Dec.size, Dec.depth] at h
  exact Dec.foldFits_of_le N k _ _ (by omega) (by omega) h

/-- A path of names down a fitting union's child, joined, fits `strings.Join`. -/
theorem Dec.foldFits_path (N : Nat) (ks : List Dec) (i : Nat) (k : Dec) (hk : ks[i]? = some k)
    (h : Dec.foldFits N (.union ks)) : (1 + k.depth) * (N + 2) < _root_.Perennial.strings.joinMax := by
  have h1 := Dec.depth_le_depthL ks i k hk
  unfold Dec.foldFits Dec.foldBound at h
  simp only [Dec.size, Dec.depth] at h
  have h2 : (1 + k.depth) * (N + 2) ≤ (Dec.depthL ks + 1 + 1) * (N + 2) :=
    Nat.mul_le_mul_right _ (by omega)
  have h3 := Nat.le_mul_of_pos_left ((Dec.depthL ks + 1 + 1) * (N + 2) + maxAddr.toNat + 6)
    (show 0 < Dec.sizeL ks + 1 by omega)
  omega

/-- At most `n ≤ sizeL ks` strings of a fitting union's paths and reasons, joined with a separator of
at most two bytes, fit `strings.Join`. -/
theorem Dec.foldFits_join (N : Nat) (ks : List Dec) (n c : Nat) (hn : n ≤ Dec.sizeL ks) (hc : c ≤ 2)
    (h : Dec.foldFits N (.union ks)) :
    n * ((1 + Dec.depthL ks) * (N + 2) + maxAddr.toNat + 4 + c) < _root_.Perennial.strings.joinMax := by
  unfold Dec.foldFits Dec.foldBound at h
  simp only [Dec.size, Dec.depth] at h
  have h2 : (1 + Dec.depthL ks) * (N + 2) ≤ (Dec.depthL ks + 1 + 1) * (N + 2) :=
    Nat.mul_le_mul_right _ (by omega)
  have h3 : n * ((1 + Dec.depthL ks) * (N + 2) + maxAddr.toNat + 4 + c) ≤
      (Dec.sizeL ks + 1) * ((Dec.depthL ks + 1 + 1) * (N + 2) + maxAddr.toNat + 6) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

theorem Dec.ofWord_isUnion (k : w64) : (Dec.ofWord k).isUnion = false := by
  unfold Dec.ofWord; split
  · rfl
  · split <;> rfl

/-- A string whose `len` was taken is at most `maxAddr` bytes long, as a `Nat`. -/
theorem length_le_maxAddr_toNat {α : Type _} (s : List α) (h : (s.length : Int) ≤ maxAddr) :
    s.length ≤ maxAddr.toNat := by
  have h0 : (0 : Int) ≤ maxAddr := by unfold maxAddr; decide
  have := Int.toNat_of_nonneg h0
  omega

/-- The names' bound of the union authorizer's chain and of the decisions its authorizers
return. -/
def authzNameMax : Nat := 64
/-- The depth bound of the decisions the union authorizer's authorizers return. -/
def authzDepthMax : Nat := 16
/-- The size bound (`Dec.size`) of the decisions the union authorizer's authorizers return. -/
def authzSizeMax : Nat := 512
/-- The bound on the length of the union authorizer's chain. -/
def authzChainMax : Nat := 16

/-- The union authorizer's decisions fit `strings.Join` (`Dec.foldFits`): its chain's
decisions, under at most `authzChainMax` names, each at most `authzSizeMax` nodes and
`authzDepthMax` deep. -/
theorem authz_foldBound_lt :
    Dec.foldBound (authzChainMax * authzSizeMax + 1) (authzDepthMax + 1) authzNameMax <
      _root_.Perennial.strings.joinMax := by
  unfold Dec.foldBound authzChainMax authzSizeMax authzDepthMax authzNameMax
    _root_.Perennial.strings.joinMax maxAddr
  simp

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.authorizer.Assumptions]

/-! ## Untrusted code: conditions, evaluation functions, authorizers -/

/-- A method of `ci` that takes nothing and returns some string. -/
def strMethodOk (ci : GoInterfaceOk) (meth : GoString) : IProp GF :=
  iprop({{ (True : IProp GF) }} (App (Val #(methods ci.ty meth ci.v)) (Val #()))
    {{ (s : GoString), RET #s; True }})

instance strMethodOk_persistent (ci : GoInterfaceOk) (meth : GoString) :
    Persistent (strMethodOk (GF := GF) ci meth) := by
  unfold strMethodOk; infer_instance

/-- **An evaluation result as the library's constructors build it** (2026-11-20): its type is one of
the four (`Unevaluatable`, `True`, `False`, `Error`: `resultType ≤ 3`, so the `default` arm of
`conditionsToAppliedErroredUnevaluated`'s switch is dead) and its error is `nil` or an error tree
(what `fmt.Errorf("%w", evalResult.Error())` needs). -/
def resOk (r : ConditionEvaluationResult) : IProp GF :=
  iprop(⌜uint.Z r.resultType' ≤ 3⌝ ∗ utilerrors.errTreeOrNil r.err')

instance resOk_persistent (r : ConditionEvaluationResult) : Persistent (resOk (GF := GF) r) := by
  unfold resOk; infer_instance

/-- `Evaluate(ctx, data)` of the condition `ci` returns some evaluation result. -/
def condEvalOk (ci : GoInterfaceOk) (ctx data : GoInterface) : IProp GF :=
  iprop({{ (True : IProp GF) }}
    (App (App (Val #(methods ci.ty go!"Evaluate" ci.v)) (Val #ctx)) (Val #data))
    {{ (r : ConditionEvaluationResult), RET #r; resOk r }})

instance condEvalOk_persistent (ci : GoInterfaceOk) (ctx data : GoInterface) :
    Persistent (condEvalOk (GF := GF) ci ctx data) := by
  unfold condEvalOk; infer_instance

/-- **A condition** (a `Condition` interface value): not `nil` (the library calls its methods
unguarded), its getters return strings, and `Evaluate(ctx, data)` returns some evaluation result,
for any context and data. -/
def isCondition (c : GoInterface) : IProp GF :=
  iprop(∃ ci : GoInterfaceOk, ⌜c = .ok ci⌝ ∗
    strMethodOk ci go!"GetID" ∗ strMethodOk ci go!"GetType" ∗
    strMethodOk ci go!"GetCondition" ∗ strMethodOk ci go!"GetDescription" ∗
    (∀ (ctx data : GoInterface), condEvalOk ci ctx data))

instance isCondition_persistent (c : GoInterface) : Persistent (isCondition (GF := GF) c) := by
  unfold isCondition; infer_instance

/-- A slice of conditions, read-only for good. -/
def condsOk (s : GoSlice) (cs : List GoInterface) : IProp GF :=
  iprop(s ↦*□ cs ∗ [∗list] c ∈ cs, isCondition c)

instance condsOk_persistent (s : GoSlice) (cs : List GoInterface) :
    Persistent (condsOk (GF := GF) s cs) := by
  unfold condsOk; infer_instance

/-- **A conditions map value** (`ConditionsMap`) whose Deny, NoOpinion and Allow conditions are
`dn`, `no`, `al`. -/
def isConditionsMap (c : ConditionsMap) (dn no al : List GoInterface) : IProp GF :=
  iprop(condsOk c.denyConditions' dn ∗ condsOk c.noOpinionConditions' no ∗
    condsOk c.allowConditions' al)

instance isConditionsMap_persistent (c : ConditionsMap) (dn no al : List GoInterface) :
    Persistent (isConditionsMap (GF := GF) c dn no al) := by
  unfold isConditionsMap; infer_instance

/-- A call `f(ctx, cond, data)` of a partial evaluation function on a condition returns some
evaluation result. -/
def maybeEvalCallOk (f : GoFunc) (ctx cond data : GoInterface) : IProp GF :=
  iprop({{ isCondition (GF := GF) cond }}
    (App (App (App (Val #f) (Val #ctx)) (Val #cond)) (Val #data))
    {{ (r : ConditionEvaluationResult), RET #r; resOk r }})

instance maybeEvalCallOk_persistent (f : GoFunc) (ctx cond data : GoInterface) :
    Persistent (maybeEvalCallOk (GF := GF) f ctx cond data) := by
  unfold maybeEvalCallOk; infer_instance

/-- **A partial evaluation function** (`MaybeEvaluateConditionFunc`): `nil` (the library checks),
or callable on a condition, returning some evaluation result. -/
def maybeEvalFnOk (f : GoFunc) : IProp GF :=
  iprop(⌜f = func.nil⌝ ∨ ∀ (ctx cond data : GoInterface), maybeEvalCallOk f ctx cond data)

instance maybeEvalFnOk_persistent (f : GoFunc) : Persistent (maybeEvalFnOk (GF := GF) f) := by
  unfold maybeEvalFnOk; infer_instance

/-- A call `f(ctx, cond, data)` of an evaluation function on a condition returns some boolean and
error. -/
def evalCallOk (f : GoFunc) (ctx cond data : GoInterface) : IProp GF :=
  iprop({{ isCondition (GF := GF) cond }}
    (App (App (App (Val #f) (Val #ctx)) (Val #cond)) (Val #data))
    {{ (b : Bool) (e : GoInterface), RET (PairV #b #e); utilerrors.errTreeOrNil e }})

instance evalCallOk_persistent (f : GoFunc) (ctx cond data : GoInterface) :
    Persistent (evalCallOk (GF := GF) f ctx cond data) := by
  unfold evalCallOk; infer_instance

/-- **An evaluation function** (`EvaluateConditionFunc`): not `nil` (`ConditionsMap.Evaluate`
calls it unguarded), callable on a condition, returning some boolean and error. -/
def evalFnOk (f : GoFunc) : IProp GF :=
  iprop(∀ (ctx cond data : GoInterface), evalCallOk f ctx cond data)

instance evalFnOk_persistent (f : GoFunc) : Persistent (evalFnOk (GF := GF) f) := by
  unfold evalFnOk; infer_instance

/-! ## Decisions -/

/-- The memoized fields of a union (builder or decision field) `u` agree with the children `ks`:
the flag is whether one contains an unconditional Allow or Deny, and the set
(`subDecisionsPossibleDecisions`, owned at `dq`) holds their possible decisions (`nil` while there is
no child). -/
def subOk (u : ConditionsAwareDecisionUnion) (dq : DFrac) (ks : List Dec) : IProp GF :=
  iprop(⌜u.containsUnconditionalAllowOrDeny' = Dec.cuadL ks⌝ ∗
    (⌜ks = [] ∧ u.subDecisionsPossibleDecisions' = zeroValDef⌝ ∨
      ∃ s : GMap w64 sets.Elem, u.subDecisionsPossibleDecisions' ↦${dq} s ∗ ⌜setIs s (Dec.subL ks)⌝))

instance subOk_persistent (u : ConditionsAwareDecisionUnion) (ks : List Dec) :
    Persistent (subOk (GF := GF) u DFrac.discard ks) := by
  unfold subOk; infer_instance

mutual
/-- The decision value `d` is described by the model `m` (without the persistence modality; see
`isDecision`). -/
def isDecisionRaw (d : ConditionsAwareDecision) : Dec → IProp GF
  | .deny => iprop(⌜d.decisionType' = W64 0⌝ ∗ utilerrors.errTreeOrNil d.err')
  | .allow => iprop(⌜d.decisionType' = W64 11⌝ ∗ utilerrors.errTreeOrNil d.err')
  | .noOpinion => iprop(⌜d.decisionType' = W64 12⌝ ∗ utilerrors.errTreeOrNil d.err')
  | .cmap dn no al => iprop(⌜d.decisionType' = W64 13⌝ ∗ isConditionsMap d.conditionsMap' dn no al ∗
      utilerrors.errTreeOrNil d.err')
  | .union ks => iprop(⌜d.decisionType' = W64 14⌝ ∗ subOk d.union' DFrac.discard ks ∗
      (∃ nds : List namedConditionsAwareDecision, d.union'.inner' ↦*□ nds ∗
        isDecisionRawL (nds.map (·.d')) ks) ∗ utilerrors.errTreeOrNil d.err')
/-- The decision values `ds` are described by the models `ks`, one by one. -/
def isDecisionRawL : List ConditionsAwareDecision → List Dec → IProp GF
  | [], [] => iprop(True)
  | d :: ds, k :: ks => iprop(isDecisionRaw d k ∗ isDecisionRawL ds ks)
  | _, _ => iprop(False)
end

/-- **A decision** (`ConditionsAwareDecision` value) described by the model `m`, persistently (the
value is immutable: see the file header). -/
def isDecision (d : ConditionsAwareDecision) (m : Dec) : IProp GF :=
  iprop(□ isDecisionRaw d m)

instance isDecision_persistent (d : ConditionsAwareDecision) (m : Dec) :
    Persistent (isDecision (GF := GF) d m) := by
  unfold isDecision; infer_instance

/-- The children of a union, described by their models (persistently). -/
def isDecisionL (ds : List ConditionsAwareDecision) (ks : List Dec) : IProp GF :=
  iprop(□ isDecisionRawL ds ks)

instance isDecisionL_persistent (ds : List ConditionsAwareDecision) (ks : List Dec) :
    Persistent (isDecisionL (GF := GF) ds ks) := by
  unfold isDecisionL; infer_instance

/-- **A well-formed decision**: some model, `WF`. -/
def isWFDecision (d : ConditionsAwareDecision) : IProp GF :=
  iprop(∃ m : Dec, isDecision d m ∗ ⌜m.WF⌝)

instance isWFDecision_persistent (d : ConditionsAwareDecision) :
    Persistent (isWFDecision (GF := GF) d) := by
  unfold isWFDecision; infer_instance

/-- A well-formed decision at most `n` deep (`Dec.depth`). -/
def isWFDecisionLe (n : Nat) (d : ConditionsAwareDecision) : IProp GF :=
  iprop(∃ m : Dec, isDecision d m ∗ ⌜m.WF ∧ m.depth ≤ n⌝)

instance isWFDecisionLe_persistent (n : Nat) (d : ConditionsAwareDecision) :
    Persistent (isWFDecisionLe (GF := GF) n d) := by
  unfold isWFDecisionLe; infer_instance

theorem isWFDecisionLe_isWFDecision (n : Nat) (d : ConditionsAwareDecision) :
    isWFDecisionLe (GF := GF) n d ⊢ isWFDecision d := by
  unfold isWFDecisionLe isWFDecision
  iintro ⟨%m, Hd, %Hm⟩
  iexists m
  iframe Hd
  ipureintro; exact Hm.1

theorem isWFDecisionLe_weaken (n n' : Nat) (d : ConditionsAwareDecision) :
    isWFDecisionLe (GF := GF) n d ∗ ⌜n ≤ n'⌝ ⊢ isWFDecisionLe n' d := by
  unfold isWFDecisionLe
  iintro ⟨⟨%m, Hd, %Hm⟩, %h⟩
  iexists m
  iframe Hd
  ipureintro; exact ⟨Hm.1, by omega⟩

/-- A decision's error is `nil` or an error tree (2026-11-20). -/
theorem isDecision_err (d : ConditionsAwareDecision) (m : Dec) :
    isDecision (GF := GF) d m ⊢ utilerrors.errTreeOrNil d.err' := by
  unfold isDecision
  cases m <;> simp only [isDecisionRaw]
  · iintro #⟨-, H⟩; iexact H
  · iintro #⟨-, H⟩; iexact H
  · iintro #⟨-, H⟩; iexact H
  · iintro #⟨-, -, H⟩; iexact H
  · iintro #⟨-, -, -, H⟩; iexact H

/-- A decision's type tag is its model's (`IsAllow`, ... read it). -/
theorem isDecision_tag (d : ConditionsAwareDecision) (m : Dec) :
    isDecision (GF := GF) d m ⊢ ⌜d.decisionType' = m.tag⌝ := by
  unfold isDecision
  cases m <;> simp only [isDecisionRaw, Dec.tag]
  all_goals first
    | (iintro #H; iexact H)
    | (iintro #⟨%H, -⟩; ipureintro; exact H)

mutual
/-- The names of the unions in the decision value `d` (model `m`) are at most `N` bytes (without
the persistence modality; see `decNames`). -/
def decNamesRaw (N : Nat) (d : ConditionsAwareDecision) : Dec → IProp GF
  | .deny => iprop(True)
  | .allow => iprop(True)
  | .noOpinion => iprop(True)
  | .cmap _ _ _ => iprop(True)
  | .union ks => iprop(∃ nds : List namedConditionsAwareDecision, d.union'.inner' ↦*□ nds ∗
      ⌜∀ nd ∈ nds, nd.conditionalAuthorizerName'.length ≤ N⌝ ∗
      decNamesRawL N (nds.map (·.d')) ks)
/-- The names in the decision values `ds` (models `ks`) are at most `N` bytes, one by one. -/
def decNamesRawL (N : Nat) : List ConditionsAwareDecision → List Dec → IProp GF
  | [], [] => iprop(True)
  | d :: ds, k :: ks => iprop(decNamesRaw N d k ∗ decNamesRawL N ds ks)
  | _, _ => iprop(False)
end

/-- **The names in a decision** `d` of model `m` (its children's `conditionalAuthorizerName`s, all
the way down) are at most `N` bytes, persistently (fmt stage 1: `ToDecision` joins them). Separate
from `isDecision`, whose users do not need it. -/
def decNames (N : Nat) (d : ConditionsAwareDecision) (m : Dec) : IProp GF :=
  iprop(□ decNamesRaw N d m)

instance decNames_persistent (N : Nat) (d : ConditionsAwareDecision) (m : Dec) :
    Persistent (decNames (GF := GF) N d m) := by
  unfold decNames; infer_instance

/-- The names in decisions `ds` of models `ks`, persistently. -/
def decNamesL (N : Nat) (ds : List ConditionsAwareDecision) (ks : List Dec) : IProp GF :=
  iprop(□ decNamesRawL N ds ks)

instance decNamesL_persistent (N : Nat) (ds : List ConditionsAwareDecision) (ks : List Dec) :
    Persistent (decNamesL (GF := GF) N ds ks) := by
  unfold decNamesL; infer_instance

/-- A leaf has no names. -/
theorem decNames_leaf (N : Nat) (d : ConditionsAwareDecision) (m : Dec) (h : m.isUnion = false) :
    ⊢ decNames (GF := GF) N d m := by
  unfold decNames
  cases m
  case union => simp only [Dec.isUnion] at h; exact absurd h (by decide)
  all_goals (simp only [decNamesRaw]; imodintro; itrivial)

theorem decNamesL_nil (N : Nat) : ⊢ decNamesL (GF := GF) N [] [] := by
  unfold decNamesL; simp only [decNamesRawL]; imodintro; itrivial

theorem decNamesRawL_snoc (N : Nat) : ∀ (ds : List ConditionsAwareDecision) (ks : List Dec)
    (d : ConditionsAwareDecision) (m : Dec),
    iprop(□ decNamesRawL N ds ks) ⊢ (□ decNamesRaw N d m -∗ □ decNamesRawL N (ds ++ [d]) (ks ++ [m]) : IProp GF)
  | [], [], d, m => by
    simp only [List.nil_append, decNamesRawL]
    iintro #- #H
    imodintro
    isplitl
    · iexact H
    · itrivial
  | [], _ :: _, _, _ => by
    simp only [decNamesRawL]
    iintro #H
    iexfalso; iexact H
  | _ :: _, [], _, _ => by
    simp only [decNamesRawL]
    iintro #H
    iexfalso; iexact H
  | d' :: ds, k :: ks, d, m => by
    simp only [List.cons_append, decNamesRawL]
    iintro #⟨#H1, #H2⟩ #H
    imodintro
    isplitl
    · iexact H1
    · iapply decNamesRawL_snoc N ds ks d m $$ H2 H

/-- A builder's children's names with a new child's. -/
theorem decNamesL_snoc (N : Nat) (ds : List ConditionsAwareDecision) (ks : List Dec)
    (d : ConditionsAwareDecision) (m : Dec) :
    decNamesL (GF := GF) N ds ks ⊢ decNames N d m -∗ decNamesL N (ds ++ [d]) (ks ++ [m]) := by
  unfold decNamesL decNames
  iintro #H1 #H2
  iapply decNamesRawL_snoc N ds ks d m $$ H1 H2

theorem decNamesRawL_lookup (N : Nat) : ∀ (ds : List ConditionsAwareDecision) (ks : List Dec)
    (i : Nat) (d : ConditionsAwareDecision) (m : Dec), ds[i]? = some d → ks[i]? = some m →
    iprop(□ decNamesRawL N ds ks) ⊢ (□ decNamesRaw N d m : IProp GF)
  | [], _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, h => by simp at h
  | d' :: ds, k :: ks, 0, d, m, h1, h2 => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
    subst h1 h2
    simp only [decNamesRawL]
    iintro #⟨#H1, -⟩
    iexact H1
  | d' :: ds, k :: ks, i + 1, d, m, h1, h2 => by
    simp only [List.getElem?_cons_succ] at h1 h2
    simp only [decNamesRawL]
    iintro #⟨-, #H2⟩
    iapply decNamesRawL_lookup N ds ks i d m h1 h2 $$ H2

/-- The names in the `i`-th child. -/
theorem decNamesL_lookup (N : Nat) (ds : List ConditionsAwareDecision) (ks : List Dec) (i : Nat)
    (d : ConditionsAwareDecision) (m : Dec) (h1 : ds[i]? = some d) (h2 : ks[i]? = some m) :
    decNamesL (GF := GF) N ds ks ⊢ decNames N d m := by
  unfold decNamesL decNames
  iintro #H
  iapply decNamesRawL_lookup N ds ks i d m h1 h2 $$ H

/-- A union decision's children, with their names (`isDecision_union` and `decNames` agree on
the children's slice). -/
theorem isDecision_union_names (N : Nat) (d : ConditionsAwareDecision) (ks : List Dec) :
    isDecision (GF := GF) d (.union ks) ⊢ decNames N d (.union ks) -∗
      ∃ nds : List namedConditionsAwareDecision, d.union'.inner' ↦*□ nds ∗
        isDecisionL (nds.map (·.d')) ks ∗
        ⌜∀ nd ∈ nds, nd.conditionalAuthorizerName'.length ≤ N⌝ ∗
        decNamesL N (nds.map (·.d')) ks := by
  unfold isDecision isDecisionL decNames decNamesL
  simp only [isDecisionRaw, decNamesRaw]
  iintro #⟨-, -, ⟨%nds, #Hs, #HL⟩, -⟩ #⟨%nds', #Hs', %Hn, #HN⟩
  icases ownSlice_agree _ _ _ _ _ $$ Hs Hs' with %Heq
  subst Heq
  iexists nds
  isplitl
  · iexact Hs
  isplitl
  · imodintro; iexact HL
  isplitl
  · ipureintro; exact Hn
  · imodintro; iexact HN

/-- The names of a union decision from its children's. -/
theorem decNames_union (N : Nat) (d : ConditionsAwareDecision) (ks : List Dec)
    (nds : List namedConditionsAwareDecision)
    (hn : ∀ nd ∈ nds, nd.conditionalAuthorizerName'.length ≤ N) :
    d.union'.inner' ↦*□ nds ∗ decNamesL (GF := GF) N (nds.map (·.d')) ks ⊢
      decNames N d (.union ks) := by
  unfold decNames decNamesL
  iintro ⟨#Hs, #HN⟩
  imodintro
  simp only [decNamesRaw]
  iexists nds
  isplitl
  · iexact Hs
  isplitl
  · ipureintro; exact hn
  · iexact HN

/-- **A well-formed decision of at most `D` depth and `S` nodes whose names are at most `N`
bytes** (`ToDecision`, `PartiallyEvaluateConditionsAwareDecision` and the authorizers return
these). -/
def isWFDecisionBnd (D S N : Nat) (d : ConditionsAwareDecision) : IProp GF :=
  iprop(∃ m : Dec, isDecision d m ∗ ⌜m.WF ∧ m.depth ≤ D ∧ m.size ≤ S⌝ ∗ decNames N d m)

instance isWFDecisionBnd_persistent (D S N : Nat) (d : ConditionsAwareDecision) :
    Persistent (isWFDecisionBnd (GF := GF) D S N d) := by
  unfold isWFDecisionBnd; infer_instance

theorem isWFDecisionBnd_isWFDecisionLe (D S N : Nat) (d : ConditionsAwareDecision) :
    isWFDecisionBnd (GF := GF) D S N d ⊢ isWFDecisionLe D d := by
  unfold isWFDecisionBnd isWFDecisionLe
  iintro ⟨%m, #Hd, %Hm, -⟩
  iexists m
  iframe Hd
  ipureintro; exact ⟨Hm.1, Hm.2.1⟩

theorem isWFDecisionBnd_isWFDecision (D S N : Nat) (d : ConditionsAwareDecision) :
    isWFDecisionBnd (GF := GF) D S N d ⊢ isWFDecision d := by
  unfold isWFDecisionBnd isWFDecision
  iintro ⟨%m, #Hd, %Hm, -⟩
  iexists m
  iframe Hd
  ipureintro; exact Hm.1

theorem isWFDecisionBnd_weaken (D S N D' S' : Nat) (d : ConditionsAwareDecision) :
    isWFDecisionBnd (GF := GF) D S N d ∗ ⌜D ≤ D' ∧ S ≤ S'⌝ ⊢ isWFDecisionBnd D' S' N d := by
  unfold isWFDecisionBnd
  iintro ⟨⟨%m, #Hd, %Hm, #Hn⟩, %h⟩
  iexists m
  iframe Hd Hn
  ipureintro; exact ⟨Hm.1, by omega, by omega⟩

/-- A well-formed leaf. -/
theorem isWFDecisionBnd_leaf (D S N : Nat) (d : ConditionsAwareDecision) (m : Dec) (hm : m.WF)
    (hu : m.isUnion = false) (hS : 1 ≤ S) :
    isDecision (GF := GF) d m ⊢ isWFDecisionBnd D S N d := by
  have h0 : m.depth = 0 := by cases m <;> simp_all [Dec.isUnion, Dec.depth]
  unfold isWFDecisionBnd
  iintro #Hd
  iexists m
  isplitr
  · iexact Hd
  isplitr
  · ipureintro; exact ⟨hm, by omega, by rw [Dec.size_of_depth_zero m h0]; exact hS⟩
  · iapply (decNames_leaf N d m hu)

/-- A well-formed leaf (the bounds as a premise). -/
theorem isWFDecisionBnd_leaf' (D S N : Nat) (d : ConditionsAwareDecision) (m : Dec) :
    isDecision (GF := GF) d m ∗ ⌜m.WF ∧ m.isUnion = false ∧ 1 ≤ S⌝ ⊢ isWFDecisionBnd D S N d := by
  iintro ⟨#Hd, %h⟩
  iapply (isWFDecisionBnd_leaf D S N d m h.1 h.2.1 h.2.2)
  iexact Hd

/-- A leaf (depth zero): one node, no names. -/
theorem isWFDecisionLe_zero_bnd (N : Nat) (d : ConditionsAwareDecision) :
    isWFDecisionLe (GF := GF) 0 d ⊢ isWFDecisionBnd 0 1 N d := by
  unfold isWFDecisionLe isWFDecisionBnd
  iintro ⟨%m, #Hd, %Hm⟩
  have h0 : m.depth = 0 := by omega
  iexists m
  iframe Hd
  isplitr
  · ipureintro; exact ⟨Hm.1, Hm.2, Nat.le_of_eq (Dec.size_of_depth_zero m h0)⟩
  · iapply decNames_leaf N d m (Dec.isUnion_of_depth_zero m h0)

/-- **A well-formed decision that fits `strings.Join`** (`Dec.foldFits`) with names of at most
`N` bytes: what the union authorizer's `EvaluateConditions` passes its authorizers. -/
def isWFDecisionFit (N : Nat) (d : ConditionsAwareDecision) : IProp GF :=
  iprop(∃ m : Dec, isDecision d m ∗ ⌜m.WF ∧ Dec.foldFits N m⌝ ∗ decNames N d m)

instance isWFDecisionFit_persistent (N : Nat) (d : ConditionsAwareDecision) :
    Persistent (isWFDecisionFit (GF := GF) N d) := by
  unfold isWFDecisionFit; infer_instance

theorem isWFDecisionFit_isWFDecision (N : Nat) (d : ConditionsAwareDecision) :
    isWFDecisionFit (GF := GF) N d ⊢ isWFDecision d := by
  unfold isWFDecisionFit isWFDecision
  iintro ⟨%m, #Hd, %Hm, -⟩
  iexists m
  iframe Hd
  ipureintro; exact Hm.1

/-- `ConditionsAwareAuthorize(ctx, attrs)` of the authorizer `ai` returns a well-formed
decision, at most `authzDepthMax` deep, of at most `authzSizeMax` nodes, with names of at most
`authzNameMax` bytes (the union authorizer adds it to a builder, `ownBuilder`, whose `ToDecision`
joins its leaves' paths and reasons: fmt stage 1). -/
def caaOk (ai : GoInterfaceOk) (ctx attrs : GoInterface) : IProp GF :=
  iprop({{ (True : IProp GF) }}
    (App (App (Val #(methods ai.ty go!"ConditionsAwareAuthorize" ai.v)) (Val #ctx)) (Val #attrs))
    {{ (d : ConditionsAwareDecision), RET #d;
      isWFDecisionBnd (GF := GF) authzDepthMax authzSizeMax authzNameMax d }})

instance caaOk_persistent (ai : GoInterfaceOk) (ctx attrs : GoInterface) :
    Persistent (caaOk (GF := GF) ai ctx attrs) := by
  unfold caaOk; infer_instance

/-- `EvaluateConditions(ctx, d, data)` of the authorizer `ai` on a well-formed decision (that fits
`strings.Join` with names of at most `authzNameMax` bytes, `isWFDecisionFit`: the union
authorizer's are) returns some decision word, reason and error. -/
def ecOk (ai : GoInterfaceOk) (ctx : GoInterface) (d : ConditionsAwareDecision)
    (data : GoInterface) : IProp GF :=
  iprop({{ isWFDecisionFit (GF := GF) authzNameMax d }}
    (App (App (App (Val #(methods ai.ty go!"EvaluateConditions" ai.v)) (Val #ctx)) (Val #d))
      (Val #data))
    {{ (dec : w64) (r : GoString) (e : GoInterface), RET (PairV (PairV #dec #r) #e); True }})

instance ecOk_persistent (ai : GoInterfaceOk) (ctx : GoInterface) (d : ConditionsAwareDecision)
    (data : GoInterface) : Persistent (ecOk (GF := GF) ai ctx d data) := by
  unfold ecOk; infer_instance

/-- **An authorizer** (an `Authorizer` interface value, untrusted): not `nil`; its
`ConditionsAwareAuthorize` returns a well-formed decision; its `EvaluateConditions`, called on a
well-formed decision, returns some decision word, reason and error (the leaves may lie). For any
context, attributes and data. (`Authorize` is not called through the interface on the driver's
path, so it is not asked for.) -/
def isAuthorizer (a : GoInterface) : IProp GF :=
  iprop(∃ ai : GoInterfaceOk, ⌜a = .ok ai⌝ ∗
    (∀ (ctx attrs : GoInterface), caaOk ai ctx attrs) ∗
    (∀ (ctx : GoInterface) (d : ConditionsAwareDecision) (data : GoInterface), ecOk ai ctx d data))

instance isAuthorizer_persistent (a : GoInterface) : Persistent (isAuthorizer (GF := GF) a) := by
  unfold isAuthorizer; infer_instance

/-! ## Iterators and the library's own callbacks -/

/-- A call `y(x)` of a yield function from `P`: returns `true` in `Q`, `false` in `D`. -/
def yield1Ok {V : Type} (y : GoFunc) (x : V) (P Q D : IProp GF) : IProp GF :=
  iprop({{ P }} (App (Val #y) (Val #x)) {{ (b : Bool), RET #b; if b then Q else D }})

/-- A call `y(k, v)` of a two-value yield function from `P`: returns `true` in `Q`, `false` in
`D`. -/
def yield2Ok {K V : Type} (y : GoFunc) (k : K) (v : V)
    (P Q D : IProp GF) : IProp GF :=
  iprop({{ P }} (App (App (Val #y) (Val #k)) (Val #v)) {{ (b : Bool), RET #b; if b then Q else D }})

/-- A call `f(y)` of an iterator from `P` returns (nothing) in `Q`. -/
def iterRunOk (f y : GoFunc) (P Q : IProp GF) : IProp GF :=
  iprop({{ P }} (App (Val #f) (Val #y)) {{ RET #(); Q }})

/-- **An iterator over `xs`** (`iter.Seq[V]`, a `func(yield func(V) bool)`): for any yield function
`y` and states `I i` (before element `i`) and `D` (stopped), if `y` on element `i` goes from `I i`
to `I (i+1)` returning `true` or to `D` returning `false`, then the iterator goes from `I 0` to
`I xs.length` (it calls `y` on each element in order) or to `D` (it stops at the first `false`). -/
def seqOk {V : Type} (f : GoFunc) (xs : List V) : IProp GF :=
  iprop(□ ∀ (y : GoFunc) (I : Nat → IProp GF) (D : IProp GF),
    (□ ∀ (i : Nat) (x : V), ⌜xs[i]? = some x⌝ -∗ yield1Ok y x (I i) (I (i + 1)) D) -∗
      iterRunOk f y (I 0) iprop(I xs.length ∨ D))

instance seqOk_persistent {V : Type} (f : GoFunc) (xs : List V) :
    Persistent (seqOk (GF := GF) f xs) := by
  unfold seqOk; infer_instance

/-- **An iterator over the pairs `xs`** (`iter.Seq2[K, V]`), as `seqOk`. -/
def seq2Ok {K V : Type} (f : GoFunc) (xs : List (K × V)) : IProp GF :=
  iprop(□ ∀ (y : GoFunc) (I : Nat → IProp GF) (D : IProp GF),
    (□ ∀ (i : Nat) (k : K) (v : V), ⌜xs[i]? = some (k, v)⌝ -∗
        yield2Ok y k v (I i) (I (i + 1)) D) -∗
      iterRunOk f y (I 0) iprop(I xs.length ∨ D))

instance seq2Ok_persistent {K V : Type} (f : GoFunc)
    (xs : List (K × V)) : Persistent (seq2Ok (GF := GF) f xs) := by
  unfold seq2Ok; infer_instance

/-- A call `ev(cond)` of `partiallyEvaluateConditionsMapInternal`'s `evalCond` closure on a
condition returns some evaluation result. -/
def evalCondCallOk (ev : GoFunc) (cond : GoInterface) : IProp GF :=
  iprop({{ isCondition (GF := GF) cond }} (App (Val #ev) (Val #cond))
    {{ (r : ConditionEvaluationResult), RET #r; resOk r }})

/-- **A condition evaluator** (`func(cond Condition) ConditionEvaluationResult`, the closure
`partiallyEvaluateConditionsMapInternal` builds): callable on any condition. -/
def evalCondOk (ev : GoFunc) : IProp GF :=
  iprop(∀ (cond : GoInterface), evalCondCallOk ev cond)

instance evalCondOk_persistent (ev : GoFunc) : Persistent (evalCondOk (GF := GF) ev) := by
  unfold evalCondOk evalCondCallOk; infer_instance

/-- A call `f(ctx, a)` of an authorization function returns some decision word, reason and error. -/
def authzCallOk (f : GoFunc) (ctx a : GoInterface) : IProp GF :=
  iprop({{ (True : IProp GF) }} (App (App (Val #f) (Val #ctx)) (Val #a))
    {{ (dec : w64) (r : GoString) (e : GoInterface), RET (PairV (PairV #dec #r) #e);
        utilerrors.errTreeOrNil e }})

/-- **An authorization function** (an `AuthorizerFunc`'s function, untrusted): callable, returning
anything. -/
def authzFnOk (f : GoFunc) : IProp GF :=
  iprop(∀ (ctx a : GoInterface), authzCallOk f ctx a)

instance authzFnOk_persistent (f : GoFunc) : Persistent (authzFnOk (GF := GF) f) := by
  unfold authzFnOk authzCallOk; infer_instance

/-! ## Laws of `isDecision` -/

/-- A union decision's children slice and its children. -/
theorem isDecision_union (d : ConditionsAwareDecision) (ks : List Dec) :
    isDecision (GF := GF) d (.union ks) ⊢
      ∃ nds : List namedConditionsAwareDecision, d.union'.inner' ↦*□ nds ∗
        isDecisionL (nds.map (·.d')) ks := by
  unfold isDecision isDecisionL
  simp only [isDecisionRaw]
  iintro #⟨-, -, ⟨%nds, #Hs, #HL⟩, -⟩
  iexists nds
  isplitl
  · iexact Hs
  · imodintro
    iexact HL

/-- A union decision's memoized fields agree with its children. -/
theorem isDecision_union_subOk (d : ConditionsAwareDecision) (ks : List Dec) :
    isDecision (GF := GF) d (.union ks) ⊢ subOk d.union' DFrac.discard ks := by
  unfold isDecision
  simp only [isDecisionRaw]
  iintro #⟨-, #H, -, -⟩
  iexact H

/-- A conditions map decision's conditions map. -/
theorem isDecision_cmap (d : ConditionsAwareDecision) (dn no al : List GoInterface) :
    isDecision (GF := GF) d (.cmap dn no al) ⊢ isConditionsMap d.conditionsMap' dn no al := by
  unfold isDecision
  simp only [isDecisionRaw]
  iintro #⟨-, H, -⟩
  iexact H

theorem isDecisionRawL_lookup : ∀ (ds : List ConditionsAwareDecision) (ks : List Dec) (i : Nat)
    (d : ConditionsAwareDecision), ds[i]? = some d →
    iprop(□ isDecisionRawL ds ks) ⊢ (∃ m : Dec, ⌜ks[i]? = some m⌝ ∗ □ isDecisionRaw d m : IProp GF)
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, _, _ => by
    simp only [isDecisionRawL]
    iintro #H
    iexfalso
    iexact H
  | d' :: ds, k :: ks, 0, d, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [isDecisionRawL]
    iintro #⟨#H1, -⟩
    iexists k
    isplitr
    · ipureintro; rfl
    · iexact H1
  | d' :: ds, k :: ks, i + 1, d, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [isDecisionRawL]
    iintro #⟨-, #H2⟩
    icases isDecisionRawL_lookup ds ks i d h $$ H2 with ⟨%m, %hm, #Hm⟩
    iexists m
    isplitr
    · ipureintro; simpa using hm
    · iexact Hm

/-- The `i`-th child of a union, with its model. -/
theorem isDecisionL_lookup (ds : List ConditionsAwareDecision) (ks : List Dec) (i : Nat)
    (d : ConditionsAwareDecision) (h : ds[i]? = some d) :
    isDecisionL (GF := GF) ds ks ⊢ ∃ m : Dec, ⌜ks[i]? = some m⌝ ∗ isDecision d m := by
  unfold isDecisionL isDecision
  iintro #H
  iapply isDecisionRawL_lookup ds ks i d h
  iexact H

/-! ## The union builder -/

/-- **The union builder** (`*ConditionsAwareDecisionUnion` at `p`, owned) holding the children
`ks` (in order): its children's slice (owned, as `Add` appends to it) holds decisions described by
`ks`; its errors' slice is owned; its memoized fields agree with `ks` (the set is `nil` until the
first child, then owned). The children are `WF` and less than `2 ^ 63 - 1` deep (`Add` takes
only such decisions): `ToDecision`'s `collectReasonsAndErrors` starts each child's path of names
at length one. The children's names, and the names in them, are at most `N` bytes (`decNames`). -/
def ownBuilder (p : Loc) (ks : List Dec) (N : Nat) : IProp GF :=
  iprop(∃ (u : ConditionsAwareDecisionUnion) (nds : List namedConditionsAwareDecision)
      (es : List GoInterface),
    ⌜(Dec.WFL ks ∧ Dec.depthL ks + 1 < 2 ^ 63) ∧
      ∀ nd ∈ nds, nd.conditionalAuthorizerName'.length ≤ N⌝ ∗ p ↦ u ∗
    u.inner' ↦* nds ∗ ownSliceCap namedConditionsAwareDecision u.inner' (DFrac.own 1) ∗
    isDecisionL (nds.map (·.d')) ks ∗
    u.errs' ↦* es ∗ ownSliceCap GoInterface u.errs' (DFrac.own 1) ∗
    ([∗list] e ∈ es, utilerrors.errTree e) ∗
    subOk u (DFrac.own 1) ks ∗ decNamesL N (nds.map (·.d')) ks)

/-- The zero builder (`var u ConditionsAwareDecisionUnion`) has no children. -/
theorem ownBuilder_zero (p : Loc) (N : Nat) :
    p ↦ (zero_val ConditionsAwareDecisionUnion) ⊢ ownBuilder (GF := GF) p [] N := by
  unfold ownBuilder isDecisionL
  iintro Hp
  iexists (zero_val ConditionsAwareDecisionUnion), [], []
  isplitr
  · ipureintro; exact ⟨⟨trivial, by simp [Dec.depthL]⟩, by simp⟩
  iframe Hp
  isplitr
  · iapply ownSlice_nil
  isplitr
  · iapply ownSliceCap_nil
  isplitr
  · imodintro; simp only [List.map_nil, isDecisionRawL]; itrivial
  isplitr
  · iapply ownSlice_nil
  isplitr
  · iapply ownSliceCap_nil
  isplitr
  · iapply BigSepL.bigSepL_nil.2; itrivial
  isplitr
  · unfold subOk
    isplitr
    · ipureintro; rfl
    ileft
    ipureintro
    exact ⟨rfl, rfl⟩
  simp only [List.map_nil]
  iapply decNamesL_nil

end defs

end authorizer
end EtcdGrove
end Perennial
