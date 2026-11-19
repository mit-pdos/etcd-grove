/-
`RawMessage`'s methods in the lab's `encoding/json` model (`json.go`): `m.MarshalJSON()` returns
`m` itself, or a fresh `"null"` when `m` is nil (never an error); `mp.UnmarshalJSON(data)` copies
`data` into `*mp` (reusing its storage), a syntax error (non-nil) when `mp` is nil.
-/
module

public import Harness.Proof.encoding.json.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace encoding.json

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [encoding.json.Assumptions]

set_option goose.wp.extras true

/-- `m.MarshalJSON()`: `(m, nil)`, or a fresh `"null"` when `m` is nil. -/
abbrev RawMessage.MarshalJSON.spec : Prop :=
  ∀ (m : GoSlice),
  {{ (True : IProp GF) }}
    (App (Val (m @!! RawMessage.ty @!! go!"MarshalJSON")) (Val #()))
  {{ (s : GoSlice), RET (PairV #s #(interface.nil : GoInterface));
      ⌜m ≠ slice.nil ∧ s = m⌝ ∨ (⌜m = slice.nil⌝ ∗ s ↦* (go!"null" : List w8)) }}

theorem RawMessage.MarshalJSON.wp_proof : RawMessage.MarshalJSON.spec (GF := GF) (hG := hG) := by
  intro m
  wp_start
  wp_auto
  wp_if_destruct
  · wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
    iapply HΦ
    iright
    iframe Hsl
  · iapply HΦ
    ileft
    ipureintro; exact ⟨Hif, rfl⟩

/-- `mp.UnmarshalJSON(data)`, `mp` non-nil: `*mp` becomes a slice holding a copy of `data`
(with its capacity), and the error is nil. -/
abbrev RawMessage.UnmarshalJSON.spec : Prop :=
  ∀ (mp : Loc) (m : GoSlice) (old : List w8) (data : GoSlice) (dq : DFrac) (bs : List w8),
  {{ (mp ↦ m ∗ m ↦* old ∗ ownSliceCap w8 m (DFrac.own 1) ∗ data ↦*{dq} bs : IProp GF) }}
    (App (Val (mp @!! go.GoType.PointerType RawMessage.ty @!! go!"UnmarshalJSON")) (Val #data))
  {{ RET #(interface.nil : GoInterface); ∃ m' : GoSlice,
      mp ↦ m' ∗ m' ↦* bs ∗ ownSliceCap w8 m' (DFrac.own 1) ∗ data ↦*{dq} bs }}

/-- `mp.UnmarshalJSON(data)` with `mp` nil: a (non-nil) syntax error. -/
abbrev RawMessage.UnmarshalJSON_nil.spec : Prop :=
  ∀ (data : GoSlice),
  {{ (True : IProp GF) }}
    (App (Val (null @!! go.GoType.PointerType RawMessage.ty @!! go!"UnmarshalJSON")) (Val #data))
  {{ (err : GoInterface), RET #err; ⌜err ≠ interface.nil⌝ }}

theorem RawMessage.UnmarshalJSON.wp_proof : RawMessage.UnmarshalJSON.spec (GF := GF) (hG := hG) := by
  intro mp m old data dq bs
  wp_start as ⟨Hmp, Hm, Hcap, Hd⟩
  ihave %Hnn := typedPointsto_not_null $$ Hmp
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hm
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  rw [ite_eq_left ⟨by decide, by decide, by word⟩]
  ihave ⟨-, Hm0, Hcap0⟩ := ownSlice_slice_with_cap (W64 0) (W64 0) m old ⟨by decide, by decide, Hwf.1⟩ $$ [Hm Hcap]
  · iframe
  wp_auto
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hm0 $Hcap0 $Hd] as %m' ⟨Hm', Hcap', Hd⟩
  iapply HΦ
  iexists m'
  iframe

theorem RawMessage.UnmarshalJSON_nil.wp_proof :
    RawMessage.UnmarshalJSON_nil.spec (GF := GF) (hG := hG) := by
  intro data
  wp_start
  wp_auto
  wp_alloc e as He
  wp_auto
  iapply HΦ
  ipureintro
  simp [interface.mkOk]

end spec

end encoding.json

end Perennial
