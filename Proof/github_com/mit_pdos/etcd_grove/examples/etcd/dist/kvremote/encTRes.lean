/-
The proof of `encTRes` (`Spec/.../dist/kvremote/encTRes.lean`): the fields' appends, in order.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.encTRes
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Enc__Int
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Enc__Bool
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.encVR
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Enc__I64

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

theorem encTRes.wp_proof (wp_Int : Enc.Int.spec (GF := GF) (hG := hG)) (wp_Bool : Enc.Bool.spec (GF := GF) (hG := hG)) (wp_encVR : encVR.spec (GF := GF) (hG := hG)) (wp_I64 : Enc.I64.spec (GF := GF) (hG := hG)) :
    encTRes.spec (GF := GF) (hG := hG) := by
  intro e bs x
  wp_start as He
  ihave #Penc : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_Int _ _ x.Kind' $$ [He] as He
  · iframe
  try wp_auto
  wp_apply wp_Bool _ _ x.Found' $$ [He] as He
  · iframe
  try wp_auto
  wp_apply wp_encVR _ _ x.R' $$ [He] as He
  · iframe
  try wp_auto
  wp_apply wp_I64 _ _ x.N' $$ [He] as He
  · iframe
  try wp_auto
  iapply HΦ
  simp only [tResBytes, List.append_assoc]
  iexact He

end proof

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
end Perennial
