/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.node__Ready
import all Proof.go_etcd_io.raft.v3.InvNode
import all Proof.go_etcd_io.raft.v3.InvNodeChan
import Proof.go_etcd_io.raft.v3.InvApi
import Proof.go_etcd_io.raft.v3.InvApiView

@[expose] public section

noncomputable section


namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3


/-! ## The spec, from the raw triple -/

namespace ApiImpl

section wrap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `node.Ready.spec` from the raw triple (`node`'s names hidden behind the API's). -/
private theorem node.wp_Ready_impl :
    EtcdGrove.node.Ready.spec (GF := GF) (hG := hG) := by
  unfold EtcdGrove.node.Ready.spec EtcdGrove.Cluster EtcdGrove.isNode EtcdGrove.isReadyChan
  intro γ N id n
  wp_start as Hnode
  iunfold isNode at Hnode
  icases Hnode with ⟨%γn, -, #Hnode, -⟩
  iunfold EtcdGrove.isNodeChan at Hnode
  icases Hnode with ⟨%nv, %r, %lok, #Hnode⟩
  iNamed Hnode
  ihave #Hn' := Hn
  iStructNamed Hn'
  wp_auto
  iapply HΦ
  unfold isReadyChan
  iexists nv
  iframe Hn
  ipureintro; rfl

end wrap

end ApiImpl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem node.Ready.wp_proof :
    node.Ready.spec (GF := GF) (hG := hG) :=
  ApiImpl.node.wp_Ready_impl

end proof

end EtcdGrove
end Perennial
