/-
Port of election_proof/proof_raft__sendAppend.v.

raft v3.7 (stage R4): compiles as ported (imports only).
-/
module

public import Spec.go_etcd_io.raft.v3.raft__sendAppend
public import Spec.go_etcd_io.raft.v3.raft__maybeSendAppend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raft.sendAppend.wp_proof
    (wp_raft_maybeSendAppend : raft.maybeSendAppend.spec (GF := GF) (hG := hG)) :
    raft.sendAppend.spec (GF := GF) (hG := hG) := by
  intro c r id s to G Hto Hcfg Hlead Htz
  wp_start as Hpre
  iNamed Hpre
  wp_auto
  wp_apply wp_raft_maybeSendAppend c r id s to true G Hto Hcfg Hlead Htz
    $$ [$Hphys $Hgate $HG $Hnosnap]
    as %b %ms %pvs ⟨Hphys, %Hms, %Hmm, HG⟩
  iapply HΦ
  iframe Hphys HG
  ipureintro
  exact ⟨Hms, Hmm⟩

end proof

end EtcdGrove
end Perennial
