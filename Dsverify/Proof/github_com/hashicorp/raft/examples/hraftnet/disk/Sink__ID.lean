/-
(hraft_robust R3) The proof of `disk.(*Sink).ID` (`snap.go`), as `examples/snapstore`'s.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Sink__ID

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]
variable [dur_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]

open github_com.hashicorp.raft proto github_com.hashicorp.raft.examples.hraftnet.disk EtcdGrove

set_option goose.wp.extras true

theorem github_com.hashicorp.raft.examples.hraftnet.disk.Sink.ID.wp_proof :
    github_com.hashicorp.raft.examples.hraftnet.disk.Sink.ID.spec (GF := GF) (hG := hG) :=
  fun k s g Qc Wf id ver idx term cfgIdx cfg => by
  wp_start as #Hcore
  iunfold sinkCore at Hcore
  icases Hcore with ⟨#Hst, #Hsn, #Hver, #Hid, #Hidx, #Hterm, #Hpeers, #Hcfg, #HcfgIdx, %Hmnn⟩
  wp_auto
  wp_end

end proof

end Perennial
