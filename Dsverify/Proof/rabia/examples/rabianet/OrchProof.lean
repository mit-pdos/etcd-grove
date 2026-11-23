/-
The kit's orchestrator (`kit.go`'s `Orch`, as paxos's `Orch`): `New` (choose, record and send the
configuration, from `orchCore`), `time.Sleep`, then `remote.Check` of six clients' `K = 8`
operations against the key-value map with pending puts (`kvS`, `Model()`), over `kvR γ`
(`Codec()`), with the generator `gens()`. `Model()`'s, `Codec()`'s, `gens()`'s and remote's
`Check`'s specs are hypotheses here (linked in `Linked.lean`).
-/
module

public import Dsverify.Proof.rabia.examples.rabianet.KitSpecs
public import Dsverify.Proof.rabia.examples.rabianet.ModelLemmas
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.Check
public import Perennial.Proof.time

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.rabia.examples.rabianet

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode model Net rabia
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory
open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.examples.rabianet.Assumptions]
variable [math.rand.Hyps GF]
variable [_root_.Perennial.io.Assumptions] [net.Assumptions] [net.FieldAssumptions] [go.BasicIntoValInj]
variable [ρ : RemoteGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

set_option goose.wp.extras true

/-- `Orch()` (`Orch.spec`). -/
theorem Orch.wp_proof (wp_Model : Model.spec (GF := GF) (hG := hG))
    (wp_Codec : Codec.spec (GF := GF) (hG := hG))
    (wp_gens : gens.spec (GF := GF) (hG := hG))
    (wp_Check : github_com.mit_pdos.etcd_grove.examples.lib.remote.Check.spec (GF := GF) (hG := hG)
      (St := KSt) (I := KIn) (O := KOut))
    (wp_New : New.spec (GF := GF)) (wp_ClientAddrs : ClientAddrs.spec (GF := GF))
    (wp_attempt : attempt.spec (GF := GF)) :
    Orch.spec (GF := GF) (hG := hG) := by
  intro γ γp hrb
  rw [pendCtx_kvS, pendLib_kvS]
  wp_start as ⟨Hcore, #Hra, #Hmap, #Hpend, Hlib⟩
  ihave #Hcc : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  unfold orchCore
  icases Hcore with ⟨#Hsh, HK⟩
  wp_apply wp_New γ $$ [$Hpkg $Hsh $HK] as -
  try wp_auto
  wp_apply time.wp_Sleep
  try wp_auto
  wp_apply wp_Model as %m #Hm
  wp_apply wp_ClientAddrs as %addrs ⟨%L, Haddrs, %HL⟩
  subst HL
  iapply fupd_wp
  imod ownSlice_persist _ _ _ $$ Haddrs with #Haddrs
  imodintro
  wp_apply (wp_Codec γ) as %cd #Hcd
  wp_apply wp_gens as %g #Hg
  try wp_auto
  wp_apply wp_attempt as %d -
  ihave %Hal := ownSlice_len _ _ _ $$ Haddrs
  have hlen' : sint.Z addrs.len = 6 := by
    have := Hal.1
    rw [List.length_map, List.length_range] at this
    have h2 := Hal.2
    unfold nC at this
    word
  try wp_auto
  wp_apply wp_Check (kvR γ) kvS γp m addrs _ cd g _ d pendN_rabia lintestN_rabia
    (kvS_pendDec γ) (kvR_encOut_inj γ) (fun st => kvR_timeless γ st) hrb (by rw [hlen']; decide)
    (by decide) (by rw [hlen']; decide) $$ [Hlib]
  · iframe #
    iframe Hlib
    simp only [kvR]
    iexact Hg
  iapply HΦ
  itrivial

end proof

end Perennial.rabia.examples.rabianet
