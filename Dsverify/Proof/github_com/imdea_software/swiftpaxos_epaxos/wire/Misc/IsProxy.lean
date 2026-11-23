module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Misc

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.imdea_software.swiftpaxos_epaxos.kvs

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [replica.Assumptions]

theorem config.ProxyInfo.IsProxy.spec_holds : config.ProxyInfo.IsProxy.spec (GF := GF) := by
  intro p als addr
  wp_start as #Hp
  iStructNamed Hp
  wp_auto
  unfold map.lookup2
  wp_auto
  wp_end

end heap
end Perennial.github_com.imdea_software.swiftpaxos_epaxos
