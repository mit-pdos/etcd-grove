/-
The proof of `EncOutput` (`Spec/.../dist/kvremote/EncOutput.lean`): the fields' appends, in order.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.EncOutput
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Enc__Bool
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Enc__I64
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.encVR
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Enc__Int
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.encTRes
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.encKV

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

theorem EncOutput.wp_proof (wp_Bool : Enc.Bool.spec (GF := GF) (hG := hG)) (wp_I64 : Enc.I64.spec (GF := GF) (hG := hG)) (wp_encVR : encVR.spec (GF := GF) (hG := hG)) (wp_Int : Enc.Int.spec (GF := GF) (hG := hG)) (wp_encTRes : encTRes.spec (GF := GF) (hG := hG)) (wp_encKV : encKV.spec (GF := GF) (hG := hG)) :
    EncOutput.spec (GF := GF) (hG := hG) := by
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
  wp_apply wp_Bool _ _ x.Err' $$ [He] as He
  · iframe
  try wp_auto
  wp_apply wp_I64 _ _ x.Rev' $$ [He] as He
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
  wp_apply wp_Bool _ _ x.Ok' $$ [He] as He
  · iframe
  try wp_auto
  wp_apply wp_Int _ _ x.NRes' $$ [He] as He
  · iframe
  try wp_auto
  wp_apply wp_encTRes _ _ x.Res0' $$ [He] as He
  · iframe
  try wp_auto
  wp_apply wp_encTRes _ _ x.Res1' $$ [He] as He
  · iframe
  try wp_auto
  wp_apply wp_encTRes _ _ x.Res2' $$ [He] as He
  · iframe
  try wp_auto
  wp_apply wp_Int _ _ x.NKVs' $$ [He] as He
  · iframe
  try wp_auto
  wp_apply wp_encKV _ _ x.KV0' $$ [He] as He
  · iframe
  try wp_auto
  wp_apply wp_encKV _ _ x.KV1' $$ [He] as He
  · iframe
  try wp_auto
  wp_apply wp_encKV _ _ x.KV2' $$ [He] as He
  · iframe
  try wp_auto
  unfold ownEnc
  icases He with ⟨%s, He, Hs, -⟩
  try wp_auto
  iapply HΦ
  simp only [outputBytes, List.append_assoc, List.nil_append]
  iexact Hs

end proof

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
end Perennial
