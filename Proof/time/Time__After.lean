/-
The proof of `(*time.Time).After(u)`: goose's pointer-method wrapper (in the method set of `*Time`:
load `*p`, call the value method), over Perennial's linked proof of the value method `Time.After`.
-/
module

public import Spec.time.Time__After
public import Perennial.Spec.time.Time__After
import Perennial.Proof.time.Link

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

theorem time.Time.After.wp_proof : time.Time.After.spec (GF := GF) (hG := hG) := by
  intro p t u dq
  wp_start as Hp
  wp_auto
  wp_apply _root_.Perennial.time.Time.wp_After
  iapply HΦ $$ Hp

end proof

end EtcdGrove
end Perennial
