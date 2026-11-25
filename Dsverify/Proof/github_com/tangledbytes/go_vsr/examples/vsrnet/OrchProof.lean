/-
The vr kit's orchestrator (`kit.go`'s `Orch`, notes/dsv-vr.md): `Configure(CfgAddrs(), choose())`
(the orchestrator fixes the number of replicas of its chosen configuration with its size token,
`conf_size`, before it sends it), then `remote.Check(Model(), ClientAddrs(), Codec(), Gen, Ops,
attempt())` against the far side's store `kvR γ.gn` and the map's porcupine model `kvS`. Ported
from dsverify-lab `examples/vr/proof/VsrProof/Top/Orch.lean` (its `RunRemote`, recorder and
porcupine axiom replaced by remote's `Check`, as paxos's kit `Orch.wp_proof`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.ConfDefs
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.KitProofDefs
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.Check
public import Net.Spec.net.Dial
public import Net.Spec.net.Listen
public import Net.Spec.net.Listener__Accept
public import Net.Spec.net.Conn__Write
public import Net.Spec.net.Conn__Close
public import Net.Spec.net.Conn__RemoteAddr
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.OrchProofDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open VsrModel VsrGhost

namespace github_com.tangledbytes.go_vsr.examples.vsrnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## Masks, the model's decoder -/

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.tangledbytes.go_vsr.examples.vsrnet.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet

set_option goose.wp.extras true

theorem Orch.wp_proof
    (wp_Check : github_com.mit_pdos.etcd_grove.examples.lib.remote.Check.spec (GF := GF) (hG := hG)
      (St := VsrModel.Store) (I := KIn) (O := KOut))
    (wp_CfgAddrs : CfgAddrs.spec (GF := GF) (hG := hG))
    (wp_Configure : Configure.spec (GF := GF) (hG := hG))
    (wp_Model : Model.spec (GF := GF) (hG := hG))
    (wp_Codec : Codec.spec (GF := GF) (hG := hG))
    (wp_Gen : Gen.spec (GF := GF) (hG := hG)) :
    Orch.spec (GF := GF) (hG := hG) := by
  intro γ γp hrb
  rw [pendCtx_kvS, pendLib_kvS]
  wp_start as ⟨#Hsys, Hsize, #Hcp, #Hra, #Hmap, #Hpend, Hlib, Hbud⟩
  ihave #Hcc : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  ihave #Hrp : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote $$ []
  · iPkgInit
  -- the configuration
  wp_apply wp_CfgAddrs as %cfgs Hcfgs
  wp_apply wp_choose as %n %h %r %Hc
  iapply fupd_wp
  imod conf_size γ Hc $$ Hsys Hsize with #Hf
  imodintro
  wp_apply (wp_Configure γ cfgs (DFrac.own 1) n h r Hc)
    $$ [Hcfgs] as -
  · iframe; iframe #
  -- the check
  wp_apply wp_Model as %m #Hm
  wp_apply wp_ClientAddrs as %addrs Haddrs
  iapply fupd_wp
  imod ownSlice_persist _ _ _ $$ Haddrs with #Haddrs
  imodintro
  wp_apply (wp_Codec γ.gn) as %cd #Hcd
  wp_apply wp_attempt as %d -
  ihave %Hal := ownSlice_len _ _ _ $$ Haddrs
  have hlen' : sint.Z addrs.len = 6 := by
    have := Hal.1; simp only [clientAddrs, List.length_cons, List.length_nil] at this; word
  wp_apply wp_Check (kvR γ.gn) kvS γp m addrs clientAddrs cd _ (W64 8) d pendN_vsr lintestN_vsr
    (kvS_pendDec γ.gn) (kvR_encOut_inj γ.gn) (fun st => kvR_timeless γ.gn st) hrb
    (by rw [hlen']; decide) (by decide) (by rw [hlen']; decide) 24 (by decide) $$ [Hlib Hbud]
  · iframe #
    iframe Hlib Hbud
    iapply (show ⊢ EtcdGrove.lintest.genSpec (GF := GF)
        (functions github_com.tangledbytes.go_vsr.examples.vsrnet.Gen [])
        (fun x => iprop(∃ i, ⌜x = (kvR (Gg := hG.goose_globalGS) γ.gn).iv i⌝)) from wp_Gen)
  iapply HΦ
  itrivial

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
