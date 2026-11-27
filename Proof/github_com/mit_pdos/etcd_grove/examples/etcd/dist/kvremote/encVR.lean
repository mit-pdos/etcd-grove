/-
The proof of `encVR` (`Spec/.../dist/kvremote/encVR.lean`): the fields' appends, in order.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.encVR
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Enc__Str
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Enc__I64

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

theorem encVR.wp_proof (wp_Str : Enc.Str.spec (GF := GF) (hG := hG)) (wp_I64 : Enc.I64.spec (GF := GF) (hG := hG)) :
    encVR.spec (GF := GF) (hG := hG) := by
  intro e bs x
  wp_start as He
  ihave #Penc : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_Str _ _ x.Val' $$ [He] as He
  · iframe
  try wp_auto
  wp_apply wp_I64 _ _ x.Mod' $$ [He] as He
  · iframe
  try wp_auto
  wp_apply wp_I64 _ _ x.Ver' $$ [He] as He
  · iframe
  try wp_auto
  iapply HΦ
  simp only [vrBytes, List.append_assoc]
  iexact He

end proof

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
end Perennial
