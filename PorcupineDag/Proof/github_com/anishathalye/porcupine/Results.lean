/- Lean-first (no Rocq counterpart).

# Porcupine PR #46: the results (2026-11-02)

The public entry points' specs (`CheckOperations`, `CheckOperationsTimeout`,
`CheckOperationsVerbose`) decide `LinearizableCO` at the client order, under `HistOk` and
`ClientsOk` (`notes/porcupine-dag-plan.md`, FROZEN). Their corollaries, for each `X`:

- `X.spec_seq : X.spec → X.specSeq`: under sequential clients (`ClientsSeq`, with `HistOk` and
  `ClientIdsOk`; `MonoReturns` follows: `ret_i < call_j ≤ ret_j`), v1.3.1's post, with
  `Linearizable` (`linCO_iff_lin`);
- `X.spec_sound : X.spec → X.specSound`: under `HistOk` and `ClientsOk` alone, `true`/`Ok` implies
  `Linearizable` (`linearizable_of_co`).

The caller's slice is given back in both, as in the specs.

`#print axioms` of the linked results (`Link.lean`) and of the corollaries at them is their trust
base.
-/
module

public import PorcupineDag.Spec.github_com.anishathalye.porcupine.CheckOperations
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.CheckOperationsTimeout
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.CheckOperationsVerbose

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine
  github_com.anishathalye.porcupine.Theory

section results
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- Sequential clients' returns do not decrease along their listed order. -/
theorem monoReturns_of_seq {ops : List Operation} (hok : HistOk ops) (hseq : ClientsSeq ops) :
    MonoReturns ops := by
  intro i j oi oj hij hi hj hc
  have h1 := hseq i j oi oj hij hi hj hc
  have h2 := hok.2 oj (List.mem_of_getElem? hj)
  omega

/-- `CheckOperations` under sequential clients: v1.3.1's spec. -/
abbrev CheckOperations.specSeq : Prop :=
  ∀ (σ : Type) (S : ModelSpec GF σ) (m : Model) (sl : GoSlice) (ops : List Operation)
    (dq : DFrac),
  HistOk ops → ClientIdsOk ops → ClientsSeq ops →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ context.isClosedchanInit ∗
      isModel S m ∗ sl ↦*{dq} ops ∗ opsIoOk S ops }}
    (App (App (Val (@! github_com.anishathalye.porcupine.CheckOperations))
      (Val #m)) (Val #sl))
  {{ (b : Bool), RET #b; ⌜b = true ↔ Linearizable S.M (histOf ops)⌝ ∗ sl ↦*{dq} ops }}

/-- `CheckOperations`, sound for plain linearizability. -/
abbrev CheckOperations.specSound : Prop :=
  ∀ (σ : Type) (S : ModelSpec GF σ) (m : Model) (sl : GoSlice) (ops : List Operation)
    (dq : DFrac),
  HistOk ops → ClientsOk ops →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ context.isClosedchanInit ∗
      isModel S m ∗ sl ↦*{dq} ops ∗ opsIoOk S ops }}
    (App (App (Val (@! github_com.anishathalye.porcupine.CheckOperations))
      (Val #m)) (Val #sl))
  {{ (b : Bool), RET #b; ⌜b = true → Linearizable S.M (histOf ops)⌝ ∗ sl ↦*{dq} ops }}

/-- `CheckOperationsTimeout` under sequential clients: v1.3.1's spec. -/
abbrev CheckOperationsTimeout.specSeq : Prop :=
  ∀ (σ : Type) (S : ModelSpec GF σ) (m : Model) (sl : GoSlice) (ops : List Operation)
    (dq : DFrac) (dur : w64),
  HistOk ops → ClientIdsOk ops → ClientsSeq ops →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ context.isClosedchanInit ∗
      isModel S m ∗ sl ↦*{dq} ops ∗ opsIoOk S ops }}
    (App (App (App (Val (@! github_com.anishathalye.porcupine.CheckOperationsTimeout))
      (Val #m)) (Val #sl)) (Val #dur))
  {{ (r : GoString), RET #r;
      ⌜(r = go!"Ok" ∧ Linearizable S.M (histOf ops)) ∨
        (r = go!"Illegal" ∧ ¬ Linearizable S.M (histOf ops)) ∨
        (r = go!"Unknown" ∧ 0 < sint.Z dur)⌝ ∗ sl ↦*{dq} ops }}

/-- `CheckOperationsTimeout`, sound for plain linearizability. -/
abbrev CheckOperationsTimeout.specSound : Prop :=
  ∀ (σ : Type) (S : ModelSpec GF σ) (m : Model) (sl : GoSlice) (ops : List Operation)
    (dq : DFrac) (dur : w64),
  HistOk ops → ClientsOk ops →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ context.isClosedchanInit ∗
      isModel S m ∗ sl ↦*{dq} ops ∗ opsIoOk S ops }}
    (App (App (App (Val (@! github_com.anishathalye.porcupine.CheckOperationsTimeout))
      (Val #m)) (Val #sl)) (Val #dur))
  {{ (r : GoString), RET #r;
      ⌜(r = go!"Ok" → Linearizable S.M (histOf ops)) ∧
        (r = go!"Ok" ∨ r = go!"Illegal" ∨ (r = go!"Unknown" ∧ 0 < sint.Z dur))⌝ ∗ sl ↦*{dq} ops }}

/-- `CheckOperationsVerbose` under sequential clients: v1.3.1's spec. -/
abbrev CheckOperationsVerbose.specSeq : Prop :=
  ∀ (σ : Type) (S : ModelSpec GF σ) (m : Model) (sl : GoSlice) (ops : List Operation)
    (dq : DFrac) (dur : w64),
  HistOk ops → ClientIdsOk ops → ClientsSeq ops →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ context.isClosedchanInit ∗
      isModel S m ∗ sl ↦*{dq} ops ∗ opsIoOk S ops }}
    (App (App (App (Val (@! github_com.anishathalye.porcupine.CheckOperationsVerbose))
      (Val #m)) (Val #sl)) (Val #dur))
  {{ (r : GoString) (info : LinearizationInfo), RET (PairV #r #info);
      ⌜(r = go!"Ok" ∧ Linearizable S.M (histOf ops)) ∨
        (r = go!"Illegal" ∧ ¬ Linearizable S.M (histOf ops)) ∨
        (r = go!"Unknown" ∧ 0 < sint.Z dur)⌝ ∗ sl ↦*{dq} ops }}

/-- `CheckOperationsVerbose`, sound for plain linearizability. -/
abbrev CheckOperationsVerbose.specSound : Prop :=
  ∀ (σ : Type) (S : ModelSpec GF σ) (m : Model) (sl : GoSlice) (ops : List Operation)
    (dq : DFrac) (dur : w64),
  HistOk ops → ClientsOk ops →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ context.isClosedchanInit ∗
      isModel S m ∗ sl ↦*{dq} ops ∗ opsIoOk S ops }}
    (App (App (App (Val (@! github_com.anishathalye.porcupine.CheckOperationsVerbose))
      (Val #m)) (Val #sl)) (Val #dur))
  {{ (r : GoString) (info : LinearizationInfo), RET (PairV #r #info);
      ⌜(r = go!"Ok" → Linearizable S.M (histOf ops)) ∧
        (r = go!"Ok" ∨ r = go!"Illegal" ∨ (r = go!"Unknown" ∧ 0 < sint.Z dur))⌝ ∗ sl ↦*{dq} ops }}

/-- The three outcomes, at `LinearizableCO` under sequential clients: at `Linearizable`. -/
theorem outcome_seq {σ : Type} {M : SeqModel σ OpV} {ops : List Operation} {r : GoString}
    {dur : w64} (hseq : ClientsSeq ops)
    (hr : (r = go!"Ok" ∧ LinearizableCO M (histOf ops) (clientOrder ops)) ∨
      (r = go!"Illegal" ∧ ¬ LinearizableCO M (histOf ops) (clientOrder ops)) ∨
      (r = go!"Unknown" ∧ 0 < sint.Z dur)) :
    (r = go!"Ok" ∧ Linearizable M (histOf ops)) ∨
      (r = go!"Illegal" ∧ ¬ Linearizable M (histOf ops)) ∨
      (r = go!"Unknown" ∧ 0 < sint.Z dur) := by
  rw [linCO_iff_lin hseq] at hr
  exact hr

/-- The three outcomes, at `LinearizableCO`: `Ok` implies `Linearizable`. -/
theorem outcome_sound {σ : Type} {M : SeqModel σ OpV} {ops : List Operation} {r : GoString}
    {dur : w64}
    (hr : (r = go!"Ok" ∧ LinearizableCO M (histOf ops) (clientOrder ops)) ∨
      (r = go!"Illegal" ∧ ¬ LinearizableCO M (histOf ops) (clientOrder ops)) ∨
      (r = go!"Unknown" ∧ 0 < sint.Z dur)) :
    (r = go!"Ok" → Linearizable M (histOf ops)) ∧
      (r = go!"Ok" ∨ r = go!"Illegal" ∨ (r = go!"Unknown" ∧ 0 < sint.Z dur)) := by
  rcases hr with ⟨rfl, h⟩ | ⟨rfl, -⟩ | ⟨rfl, h⟩
  · exact ⟨fun _ => linearizable_of_co h, Or.inl rfl⟩
  · exact ⟨fun h => absurd h (by decide), Or.inr (Or.inl rfl)⟩
  · exact ⟨fun h => absurd h (by decide), Or.inr (Or.inr ⟨rfl, h⟩)⟩

theorem CheckOperations.spec_seq (h : CheckOperations.spec (GF := GF) (hG := hG)) :
    CheckOperations.specSeq (GF := GF) (hG := hG) := by
  intro σ S m sl ops dq Hok Hids Hseq
  wp_start_folded as Hpre
  wp_apply (h σ S m sl ops dq Hok ⟨Hids, monoReturns_of_seq Hok Hseq⟩) $$ [$Hpre]
    as %b ⟨%Hb, Hsl⟩
  iapply HΦ
  iframe Hsl
  ipureintro
  rw [← linCO_iff_lin Hseq]
  exact Hb

theorem CheckOperations.spec_sound (h : CheckOperations.spec (GF := GF) (hG := hG)) :
    CheckOperations.specSound (GF := GF) (hG := hG) := by
  intro σ S m sl ops dq Hok Hcl
  wp_start_folded as Hpre
  wp_apply (h σ S m sl ops dq Hok Hcl) $$ [$Hpre] as %b ⟨%Hb, Hsl⟩
  iapply HΦ
  iframe Hsl
  ipureintro
  exact fun hb => linearizable_of_co (Hb.1 hb)

theorem CheckOperationsTimeout.spec_seq (h : CheckOperationsTimeout.spec (GF := GF) (hG := hG)) :
    CheckOperationsTimeout.specSeq (GF := GF) (hG := hG) := by
  intro σ S m sl ops dq dur Hok Hids Hseq
  wp_start_folded as Hpre
  wp_apply (h σ S m sl ops dq dur Hok ⟨Hids, monoReturns_of_seq Hok Hseq⟩) $$ [$Hpre]
    as %r ⟨%Hr, Hsl⟩
  iapply HΦ
  iframe Hsl
  ipureintro
  exact outcome_seq Hseq Hr

theorem CheckOperationsTimeout.spec_sound
    (h : CheckOperationsTimeout.spec (GF := GF) (hG := hG)) :
    CheckOperationsTimeout.specSound (GF := GF) (hG := hG) := by
  intro σ S m sl ops dq dur Hok Hcl
  wp_start_folded as Hpre
  wp_apply (h σ S m sl ops dq dur Hok Hcl) $$ [$Hpre] as %r ⟨%Hr, Hsl⟩
  iapply HΦ
  iframe Hsl
  ipureintro
  exact outcome_sound Hr

theorem CheckOperationsVerbose.spec_seq (h : CheckOperationsVerbose.spec (GF := GF) (hG := hG)) :
    CheckOperationsVerbose.specSeq (GF := GF) (hG := hG) := by
  intro σ S m sl ops dq dur Hok Hids Hseq
  wp_start_folded as Hpre
  wp_apply (h σ S m sl ops dq dur Hok ⟨Hids, monoReturns_of_seq Hok Hseq⟩) $$ [$Hpre]
    as %r %info ⟨%Hr, Hsl⟩
  iapply HΦ
  iframe Hsl
  ipureintro
  exact outcome_seq Hseq Hr

theorem CheckOperationsVerbose.spec_sound
    (h : CheckOperationsVerbose.spec (GF := GF) (hG := hG)) :
    CheckOperationsVerbose.specSound (GF := GF) (hG := hG) := by
  intro σ S m sl ops dq dur Hok Hcl
  wp_start_folded as Hpre
  wp_apply (h σ S m sl ops dq dur Hok Hcl) $$ [$Hpre] as %r %info ⟨%Hr, Hsl⟩
  iapply HΦ
  iframe Hsl
  ipureintro
  exact outcome_sound Hr

end results

end porcupine
end EtcdGrove
end Perennial
