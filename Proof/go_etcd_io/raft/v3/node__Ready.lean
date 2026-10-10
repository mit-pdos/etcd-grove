/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.node__Ready

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

theorem node.Ready.wp_proof : node.Ready.spec (GF := GF) (hG := hG) := by
  intro γ id n
  wp_start as Hnode
  iunfold isNode at Hnode
  icases Hnode with ⟨%nv, %r, %lok, #Hnode⟩
  iNamed Hnode
  ihave #Hn' := Hn
  iStructNamed Hn'
  wp_auto
  iapply HΦ
  unfold isReadyChan
  iexact Hreadyc

end proof

end EtcdGrove
end Perennial
