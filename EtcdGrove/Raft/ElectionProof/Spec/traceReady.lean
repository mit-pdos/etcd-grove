/-
Port of `election_proof/spec_traceReady.v` (857d09190).
-/
import EtcdGrove.Raft.ElectionProof.InvReadylog

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

/-- `traceReady(r)`: a no-op in the build that is translated (`state_trace_nop.go`), so
it owns nothing (notes/decisions.md, "The trace hooks"). -/
abbrev traceReady.spec : Prop :=
  ∀ (r : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val #(functions traceReady [])) (Val #r))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
