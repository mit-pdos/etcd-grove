/-
The proof of `encKV` (`Spec/.../dist/kvremote/encKV.lean`): the fields' appends, in order.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.encKV
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Enc__Str
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.encVR

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote

open github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc
open github_com.mit_pdos.etcd_grove.examples.etcd.txnlin

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Assumptions]
variable [enc_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Assumptions]

theorem encKV.wp_proof (wp_Str : Enc.Str.spec (GF := GF) (hG := hG)) (wp_encVR : encVR.spec (GF := GF) (hG := hG)) :
    encKV.spec (GF := GF) (hG := hG) := by
  intro e bs x
  wp_start as He
  ihave #Penc : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_Str _ _ x.Key' $$ [He] as He
  · iframe
  try wp_auto
  wp_apply wp_encVR _ _ x.R' $$ [He] as He
  · iframe
  try wp_auto
  iapply HΦ
  simp only [kvBytes, List.append_assoc]
  iexact He

end proof

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
end Perennial
