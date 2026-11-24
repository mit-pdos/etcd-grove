-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/traceChangeConfEvent.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart). `traceChangeConfEvent` in raft's build without `with_tla`
(`state_trace_nop.go`): an empty function, against the spec both builds share (the conf change is
only read). The `with_tla` build's proof is `RaftTla/`'s module of this name. -/
module

public import KvNet.Spec.go_etcd_io.raft.v3.traceChangeConfEvent

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

theorem traceChangeConfEvent.wp_proof : traceChangeConfEvent.spec (GF := GF) (hG := hG) := by
  intro c dq o r tl
  wp_start as ⟨Hc, #Htl, %Hok⟩
  iapply HΦ
  iexact Hc

end proof

end EtcdGrove
end Perennial
