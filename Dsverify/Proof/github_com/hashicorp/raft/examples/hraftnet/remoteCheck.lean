/-
`hraftnet.remoteCheck`'s proof (vr's `Orch.wp_proof`'s check): remote's `Check(Model(), ClientAddrs(),
Codec(), Gen, ops, attempt())` against the register's porcupine model `regS` of the far side's store
`regR g` (`regS_pendDec`, `regR_encOut_inj`), with the masks `pendN_kit`, `lintestN_kit` and the call
budgets `orchBud`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.remoteCheck
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.ClientAddrs
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.attempt

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
variable [ρ : RemoteGS]

set_option goose.wp.extras true

theorem remoteCheck.wp_proof
    (wp_Check : github_com.mit_pdos.etcd_grove.examples.lib.remote.Check.spec (GF := GF) (hG := hG)
      (St := service.Reg) (I := HIn) (O := HOut))
    (wp_Model : Model.spec (GF := GF) (hG := hG))
    (wp_ClientAddrs : ClientAddrs.spec (GF := GF))
    (wp_Codec : Codec.spec (GF := GF) (hG := hG))
    (wp_Gen : Gen.spec (GF := GF) (hG := hG))
    (wp_attempt : attempt.spec (GF := GF)) :
    remoteCheck.spec (GF := GF) := by
  intro g γp ops hops1 hops2 hrb
  wp_start as ⟨#Hra, #Hmap, #Hpend, Hlib, Hbud⟩
  ihave #Hcc : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  ihave #Hrp : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_Model as %m #Hm
  wp_apply wp_ClientAddrs as %addrs ⟨%L, Haddrs, %HL⟩
  subst HL
  iapply fupd_wp
  imod ownSlice_persist _ _ _ $$ Haddrs with #Haddrs
  imodintro
  wp_apply (wp_Codec g) as %cd #Hcd
  wp_apply wp_attempt as %d -
  ihave %Hal := ownSlice_len _ _ _ $$ Haddrs
  have hlen' : sint.Z addrs.len = 5 := by
    have := Hal.1; simp only [clientAddrs, List.length_cons, List.length_nil] at this; word
  have hops : sint.Z ops = uint.Z ops := by word
  wp_apply wp_Check (regR g) regS γp m addrs clientAddrs cd _ ops d pendN_kit lintestN_kit
    (regS_pendDec g) (regR_encOut_inj g) (fun st => by unfold regR; infer_instance) hrb
    (by rw [hlen']; decide) (by rw [hops]; omega) (by rw [hlen', hops]; omega) orchBud
    (by unfold orchBud; simp only [readTries]; have : sint.nat ops = uint.nat ops := by word
        rw [this]; word)
    $$ [Hlib Hbud]
  · iframe #
    iframe Hlib Hbud
    iapply (show isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet ⊢
        EtcdGrove.lintest.genSpec (GF := GF) (functions github_com.hashicorp.raft.examples.hraftnet.Gen [])
          (fun x => iprop(∃ i, ⌜x = (regR (GF := GF) (Gg := hG.goose_globalGS) g).iv i⌝)) from wp_Gen)
    iexact Hpkg
  iapply HΦ
  itrivial

end proof

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
