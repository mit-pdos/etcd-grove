/-
`errors.Is` (`Spec/errors/Is.lean`): Perennial's `errors.wp_Is` (the same statement), which rests on the axiom
`errors.wp_reflectliteComparable` (the model of `reflectlite.TypeOf(target).Comparable()`).
-/
module

public import Spec.errors.Is

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3 go_etcd_io.etcd.pkg.v3 go_uber_org

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.errors.Assumptions]

open Iris.ProofMode in
theorem errors.Is.wp_proof : errors.Is.spec (GF := GF) (hG := hG) := by
  intro S M err target htarget htyped
  iintro %Φ ⟨#Hinit, #Htree, %HS⟩ HΦ
  iapply _root_.Perennial.errors.wp_Is S M err target htarget htyped $$ [] HΦ
  iframe #; ipureintro; exact HS

end proof

end EtcdGrove
end Perennial
