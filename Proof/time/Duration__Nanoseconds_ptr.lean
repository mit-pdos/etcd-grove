/-
The proof of `(*time.Duration).Nanoseconds()`: goose's pointer-method wrapper (`ptr_unfold'Nanoseconds`
in the method set of `*Duration`: load `*l`, call the value method), over Perennial's proof of the
value method `Duration.Nanoseconds` (`int64(d)`). Lean-first.
-/
module

public import Spec.time.Duration__Nanoseconds_ptr
public import Perennial.Spec.time.Duration__Nanoseconds
import Perennial.Proof.time.Duration__Nanoseconds

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.time.Assumptions]

theorem time.Duration.Nanoseconds_ptr.wp_proof :
    time.Duration.Nanoseconds_ptr.spec (GF := GF) (hG := hG) := by
  intro l dq d
  -- Perennial has `NotInterface` instances for the type constructors only, none for the
  -- predeclared named types (`go.int64 := go.Named "int64" []`, not reducible): the method
  -- resolution step of the value method needs it (`notes/perennial-changes.md`).
  haveI : go.NotInterface go.int64 := ⟨by simp [go.int64]⟩
  wp_start as Hl
  wp_auto
  wp_apply _root_.Perennial.time.Duration.Nanoseconds.wp_proof
  iapply HΦ $$ Hl

end proof

end EtcdGrove
end Perennial
