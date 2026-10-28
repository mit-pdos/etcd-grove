/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.node__Ready
import all Proof.go_etcd_io.raft.v3.InvNodeChan
public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.InvApplyConf
public import Proof.go_etcd_io.raft.v3.InvBoot
public import Spec.go_etcd_io.raft.v3.RawNode__ProposeConfChange
public import Spec.go_etcd_io.raft.v3.NewRawNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem node.Ready.wp_proof : node.Ready.spec (GF := GF) (hG := hG) := by
  intro γ id n
  wp_start as Hnode
  iunfold isNodeChan at Hnode
  icases Hnode with ⟨%nv, %r, %lok, #Hnode⟩
  iNamed Hnode
  ihave #Hn' := Hn
  iStructNamed Hn'
  wp_auto
  iapply HΦ
  unfold isReadyChanRaw
  iexact Hreadyc

end proof

end EtcdGrove
end Perennial
