/-
kit.go's `serve(id, addrs)` on server node `id = i + 1` (the lab's `Serve.lean`, redone for the kit
over remote and `RpcHttpHyp`, as dsv-epaxos's `ServerProof`/`ServeReplica`): wait for the
configuration (`awaitConf` in a goroutine, the first valid one over the channel), register the
codec, then run the master (node 1), or (replica node `k + 2`, `k < N`) register with the master,
build the replica (`swift.New`) and serve its rpc methods over HTTP, or idle.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ServeDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.KitDeps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ServersSpecs
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.master.New
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.master.Master__Run
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.New
public import Perennial.Proof.time

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section laws
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [SwiftNetPkgState netDistGF]

theorem dialP_fullX (γ : SwiftNames netDistGF) (cid : Nat) (bs : List w8)
    (hl : bs.length = confLen) :
    conf.dialP γ cid bs ⊢ ∃ c cs, conf.is γ c ∗ iprop(True) ∗
      ⌜bs = c.encodeC cs ∧ c.valid ∧ c.changesOk cs ∧ cs = []⌝ := by
  iintro H
  ihave ⟨%c, %cs, #Hc, %Hp⟩ := conf.dialP_full γ cid bs hl $$ H
  iexists c, cs
  iframe Hc
  isplitr
  · itrivial
  ipureintro; exact Hp

theorem srvAckQ_ok (γ : SwiftNames netDistGF) (i : Nat) (cid : Nat) :
    (if i = 0 then iprop(True) else sp.predReg γ.sp (sp.PNode.rep (i - 1))) ⊢
      srvAckQ γ i cid [confAck] := by
  unfold srvAckQ
  by_cases h : i = 0
  · simp only [h, ↓reduceIte]; unfold conf.ackQ; iintro -; ipureintro; exact List.prefix_refl _
  · simp only [h, ↓reduceIte]
    unfold conf.ackQP
    iintro #H
    isplitl []
    · ipureintro; exact List.prefix_refl _
    iright; iexact H

end laws

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [examples.swiftnet.Assumptions]
variable [net.Assumptions] [net.rpc.Assumptions] [net.FieldAssumptions] [log.Assumptions]
  [net.http.Assumptions] [io.Assumptions] [client.Assumptions]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF]

set_option goose.wp.extras true

local notation "swiftnetPkg" => pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet

/-- What the configuration's future carries to server node `i + 1`: nothing for the master,
replica node `i - 1`'s claimed ghost otherwise. -/
def srvR (γ : SwiftNames netDistGF) (i : Nat) : IProp netDistGF :=
  if i = 0 then iprop(True) else client.nodeGhostOk γ.sp (sp.PNode.rep (i - 1))

/-- `awaitConf` at server node `i + 1`'s configuration port. -/
theorem wp_awaitConf_srv (wp_awaitConf : awaitConf.spec (hG := hG))
    (wp_claim : client.claimGhost.spec) (γ : SwiftNames netDistGF) (i : Nat)
    (a : GoString) (ch : Loc) (γf : FutureNames) :
    {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg ∗
        addrProto (Gg := hG.goose_globalGS) a (conf.dialP γ) (srvAckQ γ i) ∗
        (if i = 0 then iprop(True)
         else sp.inv γ.sp γ.conf γ.mem γ.lin ∗ sp.predTok γ.sp (sp.PNode.rep (i - 1)) ∗
           client.ghostFresh) ∗
        isFuture examples.swiftnet.msg γf ch ∗
        Fulfill γf (confMsg γ (fun _ cs => cs = []) (srvR γ i)) }}
      (App (App (Val (@! examples.swiftnet.awaitConf)) (Val #a)) (Val #ch))
    {{ RET #(); False }} := by
  iintro %Φ ⟨#Hpkg, #Hcp, Hpt, #Hfut, Hful⟩ HΦ
  iapply (wp_awaitConf γ a ch γf (conf.dialP γ) (srvAckQ γ i) (fun _ cs => cs = [])
    iprop(if i = 0 then iprop(True)
     else iprop(sp.inv γ.sp γ.conf γ.mem γ.lin ∗ sp.predTok γ.sp (sp.PNode.rep (i - 1)) ∗
       client.ghostFresh))
    iprop(if i = 0 then iprop(True) else sp.predReg γ.sp (sp.PNode.rep (i - 1)))
    (srvR γ i) iprop(True)
    (conf.dialP_closed γ) (dialP_fullX γ) (srvAckQ_ok γ i) ?_) $$ [Hpt Hful] HΦ
  · iintro #Hk Hpre -
    unfold srvR
    by_cases h0 : i = 0
    · simp only [h0, ↓reduceIte]
      iintro !>
      isplitl []
      · iintro !>; itrivial
      itrivial
    · simp only [h0, ↓reduceIte]
      icases Hpre with ⟨#Hinv, Htok, Hfresh⟩
      ihave #Hcl : isPkgInit (PROP := IProp netDistGF)
          pkg_id.github_com.imdea_software.swiftpaxos.client $$ []
      · iPkgInit
      imod wp_claim γ.sp γ.conf γ.mem γ.lin (sp.PNode.rep (i - 1)) $$ Hcl Hinv Hfresh Htok
        with ⟨#Hreg, Hok⟩
      imodintro
      iframe Hok
      iexact Hreg
  · iframe Hpkg Hcp Hfut Hful Hpt

end proof

end Perennial.github_com.imdea_software.swiftpaxos
