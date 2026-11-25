-- The copy for the part `KvRaft/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/traceInitState.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart). `traceInitState` in raft's build without `with_tla`
(`state_trace_nop.go`): an empty function, against the spec both builds share. The gate gives its
`Q` with nothing logged (`TraceNopLemmas.lean`: the traced mode is empty in this build). The
`with_tla` build's proof is `RaftTla/`'s module of this name. -/
module

public import KvRaft.Spec.go_etcd_io.raft.v3.traceInitState
public import KvRaft.Proof.go_etcd_io.raft.v3.TraceNopLemmas

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

theorem traceInitState.wp_proof : traceInitState.spec (GF := GF) (hG := hG) := by
  intro r tl tr E Q R
  wp_start as ⟨#Htl, Hown, Hfire⟩
  ihave HQ := traceFire_nop $$ Hfire
  iapply HΦ
  iframe HQ
  iapply trOwn_wand tr _ R
  iframe Hown
  iintro ⟨%c, %id, %s, %P, HP, -, -, HR⟩
  iapply HR $$ HP

end proof

end EtcdGrove
end Perennial
