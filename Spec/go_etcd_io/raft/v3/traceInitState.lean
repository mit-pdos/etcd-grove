/-
Port of election_proof/spec_traceInitState.v (feb5c73d4).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `newRaft`'s tracing hook. A no-op in the translated build (`state_trace_nop.go`);
it owns nothing. -/
abbrev traceInitState.spec : Prop :=
  ∀ (r : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val #(functions traceInitState [])) (Val #r))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
