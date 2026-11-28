/-
`hraftnet.Orch`'s proof (the hraft kit's orchestrator machine): `chooseN0()` (the size and two
receipts), the draw (`kit_draw`: the drawn protocol's packages for the servers, under the draw's
invariant), `configure`, `Register()`, the admin on a goroutine of its own (what it knows,
`adminCtx`), then `remoteCheck(chooseOps())`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.Orch
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.chooseN0
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.configure
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.Register
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.admin
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.chooseOps
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.remoteCheck

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.hashicorp.raft.examples.hraftnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [π : NetProtoGS] [rsem : github_com.hashicorp.raft.Assumptions]
variable [ρ : RemoteGS] [hRB : ReceiptBoundLe GF (2 ^ 62)]

set_option goose.wp.extras true

theorem Orch.wp_proof (wp_chooseN0 : chooseN0.spec (GF := GF))
    (wp_configure : configure.spec (GF := GF))
    (wp_Register : Register.spec (GF := GF))
    (wp_admin : admin.spec (GF := GF))
    (wp_chooseOps : chooseOps.spec (GF := GF))
    (wp_remoteCheck : remoteCheck.spec (GF := GF)) :
    Orch.spec (GF := GF) := by
  intro K γp
  have hrb := hRB.receiptBound_le
  unfold orchShare
  wp_start as ⟨#Hmu, Hcu, #Hcp, #Hra, %Hss, #Hdi, Htok, Hpre, #Hrem, #Hmap, #Hpend, Hlib, Hbud⟩
  (try wp_auto)
  wp_apply (lc := 1) wp_chooseN0 as %r ⟨%n, ⟨%hr, %hn⟩, Hrc⟩
  subst hr
  iapply fupd_wp
  imod kit_draw K n hn Hss.2 $$ [Hlc1 Htok Hpre Hrc] with ⟨#Hc, #Hsv⟩
  · iframe Hlc1 Hdi Htok Hpre Hrc
  imodintro
  wp_apply (wp_configure K.γc n hn) $$ []
  · iframe #
  wp_apply wp_Register $$ [Hcu] as #Hcod
  · iframe #; iexact Hcu
  ihave #Hac : adminCtx K $$ []
  · unfold adminCtx
    isplitr; · ipureintro; exact Hss
    isplitr; · iexact Hra
    iexists n
    iframe Hc Hsv
    ipureintro; exact hn
  wp_apply wp_fork $$ []
  · wp_apply (wp_admin K) $$ [] as %hF
    · iframe #; ipureintro; omega
    exact hF.elim
  (try wp_auto)
  wp_apply wp_chooseOps as %ops %Hops
  wp_apply (wp_remoteCheck K.g.st γp ops Hops.1 Hops.2 (by omega)) $$ [Hlib Hbud]
  · iframe #; iframe Hlib Hbud
  iapply HΦ
  itrivial

end proof

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
