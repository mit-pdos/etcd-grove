/-
**`Int64.Load` with the fraction chosen inside the update** (for `inBounds.spec`, whose caller's
accessor picks the fraction when it opens its invariant). Perennial's `Int64.Load.spec` and
`LoadInt64.spec` take the fraction before the update; their proofs open the update before the
load, so the same proofs give this form. Re-proved here from the same steps (`LoadInt64`'s
`wp_load_bytes_typed`, `Int64.Load`'s struct field); the general form is proposed for Perennial
(`notes/perennial-changes.md`). Lean-first.
-/
module

public import Perennial.Spec.sync.atomic.Int64__Load
public import Perennial.Spec.sync.atomic.LoadInt64

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.atomic.Assumptions]

/-- `LoadInt64`, the fraction chosen inside the update. -/
theorem wp_LoadInt64_ex (addr : Loc) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ (dq : DFrac) (v : w64), addr ↦{dq} v ∗ (addr ↦{dq} v ={∅,⊤}=∗ Φ #v)) -∗
      WP (App (Val (@! sync.atomic.LoadInt64)) (Val #addr)) {{ Φ }} := by
  wp_start as _
  imod HΦ with ⟨%dq, %v, >Haddr, HΦ⟩
  wp_apply_core wp_load_bytes_typed _ _ addr dq v $$ Haddr
  iintro Haddr
  iapply HΦ $$ Haddr

/-- `Int64.Load`, the fraction chosen inside the update. -/
theorem wp_Int64_Load_ex (u : Loc) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ (dq : DFrac) (v : w64), sync.atomic.ownInt64 u dq v ∗
        (sync.atomic.ownInt64 u dq v ={∅,⊤}=∗ Φ #v)) -∗
      WP (App (Val (u @!! go.GoType.PointerType sync.atomic.Int64.ty @!! go!"Load")) (Val #())) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_LoadInt64_ex $$ [] [HΦ «$res0»]
  · iPkgInit
  imod HΦ with ⟨%dq, %v, Hown, HΦ⟩
  imodintro; inext
  simp only [sync.atomic.ownInt64_unseal, sync.atomic.ownInt64Def]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists dq, v
  iframe v
  iintro Hv
  imod HΦ $$ [- «$res0»] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  imodintro
  wp_auto
  iexact HΦ

end proof

end mvccfull
end EtcdGrove
end Perennial
