/-
The proof of `(*types.ID).String`: goose's pointer-method wrapper (in the method set of `*ID`:
load `*p`, call the value method), over `types.ID.String`'s spec (until 2026-11-19 a
trust-boundary axiom). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String

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
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.types.Assumptions]

theorem types.ID.String_ptr.wp_proof
    (wp_String : types.ID.String.spec (GF := GF) (hG := hG)) :
    types.ID.String_ptr.spec (GF := GF) (hG := hG) := by
  intro p dq id
  -- the method resolution step needs the underlying type's `NotInterface`, which Perennial
  -- does not state for the predeclared `uint64` (as `Duration__Nanoseconds_ptr.lean`)
  haveI : go.NotInterface go.uint64 := ⟨by unfold go.uint64; trivial⟩
  wp_start as Hp
  wp_auto
  wp_apply wp_String as %s %hs
  iapply HΦ
  iframe Hp
  ipureintro; exact hs

end proof

end EtcdGrove
end Perennial
