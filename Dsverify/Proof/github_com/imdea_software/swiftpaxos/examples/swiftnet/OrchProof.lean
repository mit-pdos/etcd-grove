/-
The orchestrator (`kit.go`'s `Orch()` = `orch(Addrs(), ClientAddrs())`): `New` (the configuration
protocol, `New.spec`), a wait, then remote's `Check` of the client machines' operations against
porcupine's model `swS` of the store `swRK γk` (`ModelLemmas.lean`'s `swS_pendDec`,
`swR_encOut_inj`), as dsv-epaxos's `Orch.wp_proof`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientNodeDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.KitDeps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ModelLemmas
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.Check
public import Perennial.Proof.time

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv
open github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.imdea_software.swiftpaxos.examples.swiftnet
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp netShaExts_has netShaExts_hasSha256

namespace cnode

theorem lintestN_spN : (↑EtcdGrove.lintest.lintestN : CoPset) ⊆ (⊤ \ ↑sp.spN) \ ↑linkN := by
  unfold EtcdGrove.lintest.lintestN sp.spN linkN
  solve_ndisj

theorem pendN_spN : (↑pendN : CoPset) ⊆ (⊤ \ ↑sp.spN) \ ↑linkN := by
  unfold pendN remoteN sp.spN linkN
  solve_ndisj

theorem pendN_sw : (↑pendN : CoPset) ⊆ ⊤ \ swEop := by
  rw [swEop_diff]; exact pendN_spN

theorem lintestN_sw : (↑EtcdGrove.lintest.lintestN : CoPset) ⊆ ⊤ \ (swEop ∪ ↑pendN) := by
  intro p hp
  rw [LawfulSet.mem_diff, LawfulSet.mem_union, not_or]
  refine ⟨CoPset.mem_full, ?_, ?_⟩
  · intro h
    have h1 : p ∈ (⊤ \ swEop : CoPset) := by rw [swEop_diff]; exact lintestN_spN p hp
    rw [LawfulSet.mem_diff] at h1
    exact h1.2 h
  · intro h
    have h1 := nclose_subseteq (nroot.@"remote") "pend" p h
    exact ndot_ne_disjoint nroot (show "lintest" ≠ "remote" by decide) p ⟨hp, h1⟩

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [net.Assumptions] [net.rpc.Assumptions] [net.FieldAssumptions] [log.Assumptions]
  [net.http.Assumptions] [client.Assumptions] [examples.swiftnet.Assumptions]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF]
variable [ρ : RemoteGS]

set_option goose.wp.extras true

theorem Orch.wp_proof
    (wp_New : ∀ γ, New.spec (hG := hG) γ)
    (wp_Addrs : AddrsC.spec) (wp_ClientAddrs : ClientAddrs.spec)
    (wp_Model : Model.spec (GF := netDistGF) (hG := hG))
    (wp_Codec : Codec.spec (GF := netDistGF) (hG := hG))
    (wp_Gen : Gen.spec (GF := netDistGF) (hG := hG))
    (wp_Check : github_com.mit_pdos.etcd_grove.examples.lib.remote.Check.spec (GF := netDistGF)
      (hG := hG) (St := St) (I := KIn) (O := BStr)) :
    Orch.spec (hG := hG) := by
  intro γ γk γp hrb
  rw [pendCtx_swS, pendLib_swS]
  wp_start as ⟨Hw, #Hcom, #Hra, #Hmap, #Hpend, Hlib, Hbud⟩
  ihave #Hcc : context.isClosedchanInit (GF := netDistGF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  try wp_auto
  wp_apply wp_Addrs as %asl Hasl
  wp_apply wp_ClientAddrs as %addrs Haddrs
  iapply fupd_wp
  imod ownSlice_persist _ _ _ $$ Hasl with #Hasl
  imod ownSlice_persist _ _ _ $$ Haddrs with #Haddrs
  imodintro
  wp_func_call
  wp_call
  try wp_auto
  wp_apply wp_New γ asl $$ [$Hw] as -
  · iframe #
  wp_apply time.wp_Sleep
  wp_apply wp_Model as %m #Hm
  wp_apply (wp_Codec (sysK γk) swEop) as %cd #Hcd
  wp_apply wp_callTime as %d -
  ihave %Hal := ownSlice_len _ _ _ $$ Haddrs
  have hlen' : sint.Z addrs.len = 6 := by
    have := Hal.1; simp only [clientAddrs, List.length_cons, List.length_nil] at this; word
  wp_apply wp_Check (swRK γk) swS γp m addrs clientAddrs cd _ _ d pendN_sw lintestN_sw
    (swS_pendDec _ _) (swR_encOut_inj _ _) (fun st => sysK_timeless γk st) hrb
    (by rw [hlen']; decide) (by decide) (by rw [hlen']; decide) 24 (by decide) $$ [Hlib Hbud]
  · iframe #
    iframe Hlib Hbud
    iapply (show ⊢ EtcdGrove.lintest.genSpec (GF := netDistGF)
        (functions github_com.imdea_software.swiftpaxos.examples.swiftnet.Gen [])
        (fun x => iprop(∃ i, ⌜x = (swRK (G := hG.goose_globalGS) γk).iv i⌝)) from wp_Gen)
  iapply HΦ
  itrivial

end proof

end cnode

end Perennial.github_com.imdea_software.swiftpaxos
