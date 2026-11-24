/-
`MustPanicIsNilStruct` (see its spec): proved over Perennial's model of `reflect` (reflect S0).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.specreq.reflect.MustPanicIsNilStruct
public import Perennial.Proof.reflect.Link
public import Perennial.Proof.reflect.Results

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace specreq_reflect

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.specreq.reflect

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.specreq.reflect.Assumptions]

theorem MustPanicIsNilStruct.wp_proof :
    MustPanicIsNilStruct.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  have hd : _root_.Perennial.reflect.directIfaceN 2 RangeResponse2.ty = some false :=
    _root_.Perennial.reflect.directIfaceN_struct_last
      (f := go.field_decl.Field go!"Count" go.int64 go!"") (u := go.int64) (k := 6) 0 (by simp [RangeResponse2.fields]) (by simp [RangeResponse2.fields])
      (show underlying go.int64 = go.int64 from go.is_underlying)
      (by simp [go.kindOf, go.int64, go.bool, go.int, go.int8, go.int16, go.int32]) (by omega) (by omega) rfl
  wp_apply (_root_.Perennial.reflect.wp_ValueOf_struct_indirect _ 2
    (by simp [_root_.Perennial.reflect.rtype.ty, RangeResponse2.ty]) hd) as %q Hq
  wp_pures
  wp_apply (_root_.Perennial.reflect.Value.wp_IsNil_struct_value _ q)
  iintro %l Hl
  wp_pures
  iapply HΦ
  iexists l
  iframe
  ipureintro
  rfl

end proof

end specreq_reflect
end EtcdGrove
end Perennial
