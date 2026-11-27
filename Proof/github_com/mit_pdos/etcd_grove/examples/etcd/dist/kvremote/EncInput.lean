/-
The proof of `EncInput` (`Spec/.../dist/kvremote/EncInput.lean`): the fields' appends, in order.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.EncInput
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Enc__Int
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Enc__Str
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.encCmp
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.encTOp

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote

open github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc
open github_com.mit_pdos.etcd_grove.examples.lib.txnwork

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Assumptions]
variable [enc_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Assumptions]

theorem EncInput.wp_proof (wp_Int : Enc.Int.spec (GF := GF) (hG := hG)) (wp_Str : Enc.Str.spec (GF := GF) (hG := hG)) (wp_encCmp : encCmp.spec (GF := GF) (hG := hG)) (wp_encTOp : encTOp.spec (GF := GF) (hG := hG)) :
    EncInput.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  ihave #Penc : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc $$ []
  · iPkgInit
  try wp_auto
  ihave He : ownEnc «$r0_ptr» [] $$ [«$r0»]
  · unfold ownEnc
    iexists slice.nil
    iframe
    isplitl []
    · iapply ownSlice_nil
    · iapply ownSliceCap_nil
  wp_apply wp_Int _ _ x.Kind' $$ [He] as He
  · iframe
  try wp_auto
  wp_apply wp_Str _ _ x.Key' $$ [He] as He
  · iframe
  try wp_auto
  wp_apply wp_Str _ _ x.Val' $$ [He] as He
  · iframe
  try wp_auto
  wp_apply wp_Int _ _ x.NCmps' $$ [He] as He
  · iframe
  try wp_auto
  wp_apply wp_encCmp _ _ x.Cmp0' $$ [He] as He
  · iframe
  try wp_auto
  wp_apply wp_Int _ _ x.NThen' $$ [He] as He
  · iframe
  try wp_auto
  wp_apply wp_encTOp _ _ x.Then0' $$ [He] as He
  · iframe
  try wp_auto
  wp_apply wp_encTOp _ _ x.Then1' $$ [He] as He
  · iframe
  try wp_auto
  wp_apply wp_encTOp _ _ x.Then2' $$ [He] as He
  · iframe
  try wp_auto
  wp_apply wp_Int _ _ x.NElse' $$ [He] as He
  · iframe
  try wp_auto
  wp_apply wp_encTOp _ _ x.Else0' $$ [He] as He
  · iframe
  try wp_auto
  unfold ownEnc
  icases He with ⟨%s, He, Hs, -⟩
  try wp_auto
  iapply HΦ
  simp only [inputBytes, List.append_assoc, List.nil_append]
  iexact Hs

end proof

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
end Perennial
