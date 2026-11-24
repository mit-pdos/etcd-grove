/-
The proved requirement snippets of `examples/specreq/reflect` (reflect S0), restated at top level over
Perennial's model of `reflect`, with the trust base of each printed in the build log (`#print
axioms`): `isNil` (true exactly of a nil interface and of an interface holding a nil pointer),
`typedNilString` (`("<nil>", true)` of a nil pointer, `("", false)` of a non-nil one and of an
`int`), `MustPanicIsNilZeroValue` (raises Go's `&reflect.ValueError{"reflect.Value.IsNil", 0}`) and
`MustPanicIsNilStruct` (raises `&reflect.ValueError{"reflect.Value.IsNil", 25}`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.specreq.reflect.isNil
public import Proof.github_com.mit_pdos.etcd_grove.examples.specreq.reflect.typedNilString
public import Proof.github_com.mit_pdos.etcd_grove.examples.specreq.reflect.MustPanicIsNilZeroValue
public import Proof.github_com.mit_pdos.etcd_grove.examples.specreq.reflect.MustPanicIsNilStruct

@[expose] public section

-- `#print axioms` prints the axioms by their full names (shortening them is slow).
set_option pp.fullNames true

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace specreq_reflect

open Iris Iris.BI

section results
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.specreq.reflect.Assumptions]

theorem wp_isNil : isNil.spec (GF := GF) (hG := hG) := isNil.wp_proof
theorem wp_typedNilString : typedNilString.spec (GF := GF) (hG := hG) := typedNilString.wp_proof
theorem wp_typedNilString_int : typedNilString.spec_int (GF := GF) (hG := hG) :=
  typedNilString.wp_proof_int
theorem wp_MustPanicIsNilZeroValue : MustPanicIsNilZeroValue.spec (GF := GF) (hG := hG) :=
  MustPanicIsNilZeroValue.wp_proof
theorem wp_MustPanicIsNilStruct : MustPanicIsNilStruct.spec (GF := GF) (hG := hG) :=
  MustPanicIsNilStruct.wp_proof

end results

#print axioms wp_isNil
#print axioms wp_typedNilString
#print axioms wp_typedNilString_int
#print axioms wp_MustPanicIsNilZeroValue
#print axioms wp_MustPanicIsNilStruct

end specreq_reflect
end EtcdGrove
end Perennial
