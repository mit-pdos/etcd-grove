/-
`(*time.Time).Add(d)` (Go's standard library), called through a pointer (`lr.Add(revokeBackoff)`
on a range variable, in `client/v3/leasing`'s `clearOldRevokes`). Perennial models `Time.Add` on a
value (`time.Time.wp_Add`, an axiom) and gives the pointer receiver no semantics
(`time.Time.TypeAssumptions` has no `ptr_Add_unfold`): the trust boundary (an axiom,
`Proof/time/Time__Add.lean`). Lean-first (no Rocq counterpart).
-/
module

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

/-- `l.Add(d)` for a `*time.Time` `l`: some time (a clock value, as `time.Time.wp_Add`), leaving
`*l` unchanged. -/
abbrev time.Time.Add.spec : Prop :=
  ∀ (l : Loc) (t : _root_.Perennial.time.Time) (d : _root_.Perennial.time.Duration),
  {{ (l ↦ t : IProp GF) }}
    (App (Val (l @!! go.GoType.PointerType _root_.Perennial.time.Time.ty @!! go!"Add")) (Val #d))
  {{ (t' : _root_.Perennial.time.Time), RET #t'; l ↦ t }}

end spec

end EtcdGrove
end Perennial
