-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/traceReplicate.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart). `traceReplicate` in raft's build without `with_tla`
(`state_trace_nop.go`): an empty function, against the spec both builds share. The gate gives its
`Q` with nothing logged (`TraceNopLemmas.lean`: the traced mode is empty in this build). The
`with_tla` build's proof is `RaftTla/`'s module of this name. -/
module

public import KvNet.Spec.go_etcd_io.raft.v3.traceReplicate
public import KvNet.Proof.go_etcd_io.raft.v3.TraceNopLemmas

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

theorem traceReplicate.wp_proof : traceReplicate.spec (GF := GF) (hG := hG) := by
  intro c r id s es dq ents tl Q
  wp_start as ⟨Hes, #Htl, Hown, Hfire⟩
  ihave HQ := traceFireN_nop $$ Hfire
  iapply HΦ
  iframe Hes Hown HQ

end proof

end EtcdGrove
end Perennial
