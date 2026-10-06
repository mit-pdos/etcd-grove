/- Port of election_proof/spec_traceCommit.v (feb5c73d4). -/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `traceCommit(r)`: a tracing hook, and a **no-op** -- Goose translates it to
`λ: <>, exception_do (do: #())` (`traceCommit.impl`,
`Perennial/Code/go_etcd_io/raft/v3.lean`). Same shape as the other trace hooks
(`Spec/traceBecomeLeader.lean`): it owns nothing. `maybeCommit` calls it through a
`defer`. -/
abbrev traceCommit.spec : Prop :=
  ∀ (r : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val #(functions traceCommit [])) (Val #r))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
