/-
`time.Duration.String`: the trust boundary (Perennial translates `time` without
`Duration.String`). Lean-first (no Rocq counterpart); `fmt.Printf`'s `%v` of a `Duration`
calls it (`fmt.argsOk`, `Spec/fmt/Errorf.lean`).
-/
module

public import Spec.fmt.Errorf
public import Perennial.Proof.time

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.time.Assumptions]

/-- `d.String()`: some string (the duration in Go's `72h3m0.5s` form); it needs nothing and
returns. -/
abbrev time.Duration.String.spec : Prop :=
  ∀ (d : _root_.Perennial.time.Duration),
  {{ (True : IProp GF) }}
    (App (Val (d @!! _root_.Perennial.time.Duration.ty @!! go!"String")) (Val #()))
  {{ (s : GoString), RET #s; True }}

/-- A `Duration` argument is `fmt.argOk`: its `String()` has `fmt.stringMethodSpec`. -/
theorem time.Duration.String.argOk (H : time.Duration.String.spec (GF := GF) (hG := hG))
    (d : _root_.Perennial.time.Duration) :
    ⊢ fmt.argOk (GF := GF) (interface.mkOk _root_.Perennial.time.Duration.ty #d) := by
  simp only [fmt.argOk, interface.mkOk]
  iintro
  iright; iright
  unfold fmt.stringMethodSpec
  imodintro
  iintro %Φ HΦ
  iapply H d $$ [] [HΦ]
  · itrivial
  inext
  iintro %s -
  iapply HΦ

end spec

end EtcdGrove
end Perennial
