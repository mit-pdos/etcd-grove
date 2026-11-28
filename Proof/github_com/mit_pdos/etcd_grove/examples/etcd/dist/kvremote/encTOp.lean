/-
The proof of `encTOp` (`Spec/.../dist/kvremote/encTOp.lean`): the fields' appends, in order.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.encTOp
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Enc__Int
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Enc__Str

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

theorem encTOp.wp_proof (wp_Int : Enc.Int.spec (GF := GF) (hG := hG)) (wp_Str : Enc.Str.spec (GF := GF) (hG := hG)) :
    encTOp.spec (GF := GF) (hG := hG) := by
  intro e bs x
  wp_start as He
  ihave #Penc : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_Int _ _ x.Kind' $$ [He] as He
  · iframe
  try wp_auto
  wp_apply wp_Str _ _ x.Key' $$ [He] as He
  · iframe
  try wp_auto
  wp_apply wp_Str _ _ x.Val' $$ [He] as He
  · iframe
  try wp_auto
  iapply HΦ
  simp only [tOpBytes, List.append_assoc]
  iexact He

end proof

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
end Perennial
