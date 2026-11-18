/-
Lean-first (no Rocq counterpart).

# The bridge to Kubernetes' checker, B2: linearizability transfers (k8s 7g step 4)

`notes/k8s-7g-scope.md` §2.3, B2. On a failure-free history, the driver's model (`pM (kSpec h0)`) keeps a
single configuration with nothing pending: a call that answered takes its step (`PStep.ok`), a watch is an
observation of the configuration (`PStep.obs`), and no write is left pending, so no late effect (`PReach`
from an empty pending list is the identity). Along it, the maintainers' `Step` (`realS`) accepts each unary
operation's real answer on the configuration's abstraction (B1: `rstepL_write`, `rstepL_get`,
`rstepL_list`). So the unary operations, with the store's answers, are linearized for `realS` by the driver's
linearization, renumbered (`isLinearization_filter`).

- `ROp`: a recorded operation (input, plain output, the store's answer as the checker's `Response`);
  `kM h0`, the driver's model on them (`ansOf`: an `EOther` output is a failed call);
- `realS init`: `correctness.Model`'s `Step` as a porcupine model; `unaryOf`, the unary operations;
- `CfgOk h`: what B1 needs of a configuration (`StOk`, `itemOk`, `rmWf`, a positive revision, the history's
  revisions); `OpOk v`: of an operation (no failed call, `RawRel`, the request facts);
- `kM_step`: the single configuration's step;
- **`realS_isLinearization`** (B2).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealBridge
public import Proof.github_com.anishathalye.porcupine.Filter

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open k8s_etcd3 k8sDeep github_com.anishathalye.porcupine.Theory
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input Output item)

section go
variable [GooseExts]

/-- **A recorded operation**: the input, the driver's plain output, and the store's answer (`Output.Raw`,
as the checker's `Response`). -/
abbrev ROp := Input × Output × RResp

/-- **The driver's model on recorded operations** (`ansOf`: an `EOther` output is a failed call). -/
abbrev kM (h0 : HSt) : SeqModel (linkv.PSet HSt Input) ROp :=
  linkv.pM (kSpec h0) fun v => some (v.1, ansOf v.2.1)

/-- **The maintainers' `Model` as porcupine's model** (`toPorcupineModel`'s `Step`), from `init`. -/
def realS (init : RM) : SeqModel RM (Input × RResp) :=
  ⟨init, fun m v => if (rstepL v.1 m v.2).1 then some (rstepL v.1 m v.2).2.1 else none⟩

/-- **The unary operations**, as the checker's (a watch, kind 5, is not one). -/
def unaryOf (v : ROp) : Option (Input × RResp) :=
  if v.1.Kind' = W64 5 then none else some (v.1, v.2.2)

/-- **What B1 needs of a configuration**: its store sorted, unannotated (`StOk`), with objects
`encodeItems` is injective on, well formed (`rmWf`), at a positive revision, and its history's store at
each revision up to the current one at that revision. -/
def CfgOk (h : HSt) : Prop :=
  StOk h.st ∧ (∀ it ∈ h.st.items, itemOk it.obj') ∧ rmWf (absR h.st) ∧ 0 < uint.nat h.st.rv ∧
    ∀ q : w64, 0 < uint.nat q → uint.nat q ≤ uint.nat h.st.rv → (histAtL h.hist q).rv = q

/-- **What B1 needs of an operation**: the call did not fail (`failureFree`), and a unary one's answer is
what its output encodes (`RawRel`), with the request facts: a list's match is one the driver draws, its
options ones `ListReadConsistency` accepts and its key one `PrepareKey` accepts; any other's key one
`PrepareKey` accepts. -/
def OpOk (v : ROp) : Prop :=
  v.2.1.Err' ≠ W64 4 ∧
  (v.1.Kind' ≠ W64 5 → RawRel v.1 v.2.1 v.2.2 ∧
    (v.1.Kind' = W64 4 → (v.1.Match' = W64 0 ∨ v.1.Match' = W64 1 ∨ v.1.Match' = W64 2) ∧
      (listConsL v.1).isSome ∧ (k8s.prepareKeyM [] v.1.ListKey' v.1.Recursive').isSome) ∧
    (v.1.Kind' ≠ W64 4 → keyOkL (storeKeyL v.1.Key') = true))

/-! ## A single configuration -/

theorem preach_nil' {St I O : Type} [DecidableEq I] {P : linkv.PendSpec St I O}
    {c0 c : linkv.PCfg St I} (hr : linkv.PReach P c0 c) : c0.pend = [] → c = c0 := by
  induction hr with
  | refl => intro _; rfl
  | @step c c₁ c₂ hs _ ih =>
    intro hp
    cases hs with
    | apply i hm => rw [hp] at hm; cases hm
    | perm p hpp =>
      have hp' : p = [] := by rw [hp] at hpp; exact List.Perm.eq_nil hpp
      subst hp'
      rw [ih rfl]
      cases c; simp only at hp; subst hp; rfl

/-- From an empty pending list, no late effect. -/
theorem preach_nil {St I O : Type} [DecidableEq I] {P : linkv.PendSpec St I O} {s : St}
    {c : linkv.PCfg St I} (hr : linkv.PReach P ⟨s, []⟩ c) : c = ⟨s, []⟩ :=
  preach_nil' hr rfl

/-- **The driver's model on a single configuration** `h` with nothing pending: a call that answered
leaves the single configuration `kstepL` reaches, and answered its output; a watch was allowed
(`watchOkL`) and leaves `h`. -/
theorem kM_step (h0 h : HSt) (S : linkv.PSet HSt Input) (hS : ∀ c, S c ↔ c = ⟨h, []⟩) (x : Input)
    (y : Output) (r : RResp) (hne : y.Err' ≠ W64 4) (T : linkv.PSet HSt Input)
    (hT : (kM h0).step S (x, y, r) = some T) :
    (x.Kind' = W64 5 → watchOkL x y h = true ∧ ∀ c, T c ↔ c = ⟨h, []⟩) ∧
    (x.Kind' ≠ W64 5 → y = (kstepL x h).2 ∧ ∀ c, T c ↔ c = ⟨(kstepL x h).1, []⟩) := by
  have hans : ansOf y = .ok y := by unfold ansOf; rw [if_neg hne]
  rw [linkv.pM_step _ _ S (x, y, r) x (ansOf y) rfl, hans] at hT
  have hTe := linkv.pSeq_step_some hT
  have hex : ∃ c, T c := by
    simp only [linkv.pSeq] at hT
    split at hT
    · rename_i hc; obtain ⟨c, hc⟩ := hc; exact ⟨c, by rw [hTe]; exact hc⟩
    · cases hT
  -- every configuration of `T`
  have hall : ∀ c', T c' → (x.Kind' = W64 5 ∧ watchOkL x y h = true ∧ c' = ⟨h, []⟩) ∨
      (x.Kind' ≠ W64 5 ∧ y = (kstepL x h).2 ∧ c' = ⟨(kstepL x h).1, []⟩) := by
    intro c' hc'
    rw [hTe] at hc'
    obtain ⟨c₀, c, c₁, h0', hr0, hst, hr1⟩ := hc'
    rw [hS] at h0'; subst h0'
    have := preach_nil hr0; subst this
    cases hst with
    | ok ho =>
      right
      have hk : x.Kind' ≠ W64 5 := by simpa using ho
      exact ⟨hk, rfl, preach_nil hr1⟩
    | obs o hob hok =>
      left
      have hk : x.Kind' = W64 5 := by simpa using hob
      exact ⟨hk, hok, preach_nil hr1⟩
  obtain ⟨c, hc⟩ := hex
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · rcases hall c hc with ⟨-, hw, rfl⟩ | ⟨hk', -, -⟩
    · refine ⟨hw, fun c' => ⟨fun h' => ?_, fun e => e ▸ hc⟩⟩
      rcases hall c' h' with ⟨-, -, e⟩ | ⟨hk', -, -⟩
      · exact e
      · exact absurd hk hk'
    · exact absurd hk hk'
  · rcases hall c hc with ⟨hk', -, -⟩ | ⟨-, hy, rfl⟩
    · exact absurd hk' hk
    · refine ⟨hy, fun c' => ⟨fun h' => ?_, fun e => e ▸ hc⟩⟩
      rcases hall c' h' with ⟨hk', -, -⟩ | ⟨-, -, e⟩
      · exact absurd hk' hk
      · exact e

/-- A get's step leaves the configuration. -/
theorem kstepL_get (x : Input) (h : HSt)
    (hg : ¬ (x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2)) (h4 : x.Kind' ≠ W64 4) :
    kstepL x h = (h, mgetL x h.st) := by
  simp only [not_or] at hg
  unfold kstepL mstepL
  rw [if_neg h4, if_neg hg.1, if_neg hg.2.1, if_neg hg.2.2]
  unfold advanceL
  simp

/-- **B1 on the driver's model step**: on a configuration B1 applies to, the maintainers' `Step` accepts a
unary operation's real answer and moves to the abstraction of `kstepL`'s configuration. -/
theorem rstepL_kstepL (x : Input) (y : Output) (r : RResp) (h : HSt) (hk5 : x.Kind' ≠ W64 5)
    (hop : OpOk (x, y, r)) (hcfg : CfgOk h) (hy : y = (kstepL x h).2) :
    (rstepL x (absR h.st) r).1 = true ∧ (rstepL x (absR h.st) r).2.1 = absR (kstepL x h).1.st := by
  obtain ⟨-, hop⟩ := hop
  obtain ⟨hrel, hlist, hkey⟩ := hop hk5
  obtain ⟨hst, hio, hwf, hpos, hhist⟩ := hcfg
  simp only at hrel hlist hkey
  by_cases h4 : x.Kind' = W64 4
  · obtain ⟨hm, hc, hp⟩ := hlist h4
    have hks : kstepL x h = (h, mlistL x h) := by unfold kstepL; rw [if_pos h4]
    rw [hks] at hy ⊢
    subst hy
    exact rstepL_list x h r h4 hm hc hp hst hio hpos hhist hrel
  · by_cases hw : x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2
    · have hks : kstepL x h = (advanceL h (mstepL x h.st).1, (mstepL x h.st).2) := by
        unfold kstepL; rw [if_neg h4]
      rw [hks] at hy ⊢
      subst hy
      rw [advanceL_items]
      exact rstepL_write x h.st r hw (hkey h4) hst hrel
    · rw [kstepL_get x h hw h4] at hy ⊢
      subst hy
      exact rstepL_get x h.st r hw h4 (hkey h4) hst hwf hpos hrel

/-! ## B2 -/

/-- **B2: the driver's linearization is the maintainers'.** On a recorded history every operation of which
answered (no `EOther` output) with its real answer encoded by its output (`OpOk`), linearized by `π` for
the driver's model from the seeded configuration `h0`, the unary operations with the store's answers are
linearized for `realS` from `h0`'s abstraction (`initialModel`) by `π`'s unary indices, renumbered.
Premises on the configurations: `h0`'s are B1's (`CfgOk`), and every unary step of the history keeps
them. -/
theorem realS_isLinearization (h0 : HSt) (H : List (Op ROp)) (π : List Nat)
    (hπ : IsLinearization (kM h0) H π) (hops : ∀ o ∈ H, OpOk o.val) (hcfg0 : CfgOk h0)
    (hpres : ∀ o ∈ H, ∀ h, CfgOk h → o.val.1.Kind' ≠ W64 5 → CfgOk (kstepL o.val.1 h).1) :
    IsLinearization (realS (absR h0.st)) (fmapH unaryOf H) (π.filterMap (fidx unaryOf H)) := by
  refine isLinearization_filter (kM h0) (realS (absR h0.st)) unaryOf
    (fun S m => ∃ h, (∀ c, S c ↔ c = ⟨h, []⟩) ∧ m = absR h.st ∧ CfgOk h) H π
    ⟨h0, fun c => Iff.rfl, rfl, hcfg0⟩ ?_ ?_ hπ
  · rintro o ho S m T ⟨h, hS, rfl, hc⟩ hT hf
    have hk5 : o.val.1.Kind' = W64 5 := by
      unfold unaryOf at hf; by_cases e : o.val.1.Kind' = W64 5
      · exact e
      · rw [if_neg e] at hf; cases hf
    obtain ⟨-, hT'⟩ := (kM_step h0 h S hS o.val.1 o.val.2.1 o.val.2.2 (hops o ho).1 T hT).1 hk5
    exact ⟨h, hT', rfl, hc⟩
  · rintro o ho S m T b ⟨h, hS, rfl, hc⟩ hT hf
    have hk5 : o.val.1.Kind' ≠ W64 5 := by
      intro e; unfold unaryOf at hf; rw [if_pos e] at hf; cases hf
    have hb : b = (o.val.1, o.val.2.2) := by
      unfold unaryOf at hf; rw [if_neg hk5] at hf; exact (Option.some.inj hf).symm
    subst hb
    obtain ⟨hy, hT'⟩ := (kM_step h0 h S hS o.val.1 o.val.2.1 o.val.2.2 (hops o ho).1 T hT).2 hk5
    obtain ⟨hok, hmv⟩ := rstepL_kstepL o.val.1 o.val.2.1 o.val.2.2 h hk5 (hops o ho) hc hy
    refine ⟨absR (kstepL o.val.1 h).1.st, ?_, (kstepL o.val.1 h).1, hT', rfl, hpres o ho h hc hk5⟩
    show (if (rstepL o.val.1 (absR h.st) o.val.2.2).1 then
      some (rstepL o.val.1 (absR h.st) o.val.2.2).2.1 else none) = _
    rw [if_pos hok, hmv]

/-- **B2, linearizable**: the unary history with the store's answers is linearizable for `realS` (so the
real porcupine run, with no timeout, answers `Ok`). -/
theorem realS_linearizable (h0 : HSt) (H : List (Op ROp)) (π : List Nat)
    (hπ : IsLinearization (kM h0) H π) (hops : ∀ o ∈ H, OpOk o.val) (hcfg0 : CfgOk h0)
    (hpres : ∀ o ∈ H, ∀ h, CfgOk h → o.val.1.Kind' ≠ W64 5 → CfgOk (kstepL o.val.1 h).1) :
    Linearizable (realS (absR h0.st)) (fmapH unaryOf H) :=
  linearizable_of_isLinearization (realS_isLinearization h0 H π hπ hops hcfg0 hpres)

end go

end k8s_correctness
end EtcdGrove
end Perennial
