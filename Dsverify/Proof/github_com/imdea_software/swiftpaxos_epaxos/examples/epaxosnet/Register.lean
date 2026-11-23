/-
`register(ip, port, maddr)`'s proof (the lab's `wp_register`, `Proof/examples/epaxosnet/Server.lean`):
dial the master with `rpc.DialHTTP` (`RpcHttpHyp`), call `Master.Register` (`registerCall.spec`)
until the reply is ready, then trade node `k`'s token for the replica id's token and start
resources at the registration exchange (`regX_claim`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.ServerDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open github_com.imdea_software.swiftpaxos_epaxos.netrpcw

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

open github_com.imdea_software.swiftpaxos_epaxos

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [examples.epaxosnet.Assumptions] [master.Assumptions] [epaxos.Assumptions]
variable [log.Assumptions] [net.http.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

set_option goose.wp.extras true in
theorem register.wp_proof [RpcHttpAddr GF] [RpcHttpHyp GF]
    (wp_Call : registerCall.spec (GF := GF) (hG := hG))
    (wp_Close : net.rpc.Client.Close.spec (GF := GF) (hG := hG)) :
    register.spec (GF := GF) (hG := hG) := by
  intro γ W k hk hSS
  wp_start as ⟨#Hready, #Hce, #Hde, %Hrb, #Hra, Hnt, #Hrx⟩
  unfold dialEnv; icases Hde with ⟨#Hhe, #Hcon⟩
  ihave #Hrpc : isPkgInit (PROP := IProp GF) pkg_id.net.rpc $$ []
  · unfold rpcReady; icases Hready with ⟨H, -⟩; iexact H
  wp_auto
  ipersist «$r0»
  wp_for
  wp_apply (RpcHttpHyp.DialHTTP_spec go!"tcp" net.tcpNet_tcp W masterAddr) $$ [$Hce $Hhe $Hcon $Hra]
    as %mc %err Hd
  · ipureintro; exact Hrb
  icases Hd with (⟨%He, #Hcl⟩ | ⟨%He, -⟩)
  rotate_left
  · rcases err with ei | _
    · wp_auto
      wp_apply time.wp_Sleep
      wp_for_post
      iframe
    · exact absurd rfl He
  subst He
  wp_auto
  wp_for
  have hz : (zero_val replica.defs.RegisterReply) =
      replica.defs.RegisterReply.mk (W64 0) slice.nil false false := by
    simp [zero_val, ZeroVal.zeroValDef]
  rw [hz]
  wp_apply (lc := 1) (wp_Call γ W k mc «$r0_ptr» reply_ptr hk hSS) $$ [$Hready $Hcl $reply]
    as %e Hc
  · iexact «$r0»
  icases Hc with (⟨%He, %id, %sl, %nl, %r, %il, Hrep, Hsl, #Hok⟩ | ⟨%He, -⟩)
  rotate_left
  · rcases e with ei | _
    · wp_auto
      wp_for_post
      wp_apply (wp_Close mc W masterAddr) $$ [$Hcl] as %e2 -
      wp_apply time.wp_Sleep
      wp_for_post
      iframe
    · exact absurd rfl He
  subst He
  wp_auto
  cases r
  · wp_auto
    wp_apply time.wp_Sleep
    wp_for_post
    iframe
  unfold regReplyOk
  simp only [ite_true]
  icases Hok with ⟨#Hlf, %Hat⟩
  wp_auto
  ihave Hcl2 := (regX_claim γ (repStart γ) ⊤ k (uint.nat id) nl CoPset.subseteq_top hk Hat) $$
    Hrx Hnt Hlf Hlc1
  iapply fupd_wp
  imod Hcl2 with ⟨Hid, Hrs⟩
  imodintro
  wp_apply (wp_Close mc W masterAddr) $$ [$Hcl] as %e2 -
  wp_for_post
  wp_for_post
  iapply HΦ
  iexists nl
  iframe Hlf Hid Hrs Hsl
  ipureintro; exact Hat

end proof

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

end Perennial
