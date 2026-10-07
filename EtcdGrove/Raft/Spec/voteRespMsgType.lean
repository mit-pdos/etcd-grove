/- Port of election_proof/spec_voteRespMsgType.v (feb5c73d4). -/
import EtcdGrove.Raft.Defs

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

/-- `voteRespMsgType` maps a vote request to its response type: `MsgVote` to
`MsgVoteResp`, and (since 2026-10-04) `MsgPreVote` to `MsgPreVoteResp`. Any other type
panics. Stated as a relation between `t` and the result `r`, so that a caller names the
result it expects. -/
abbrev voteRespMsgType.spec : Prop :=
  ∀ (t r : w32),
  (t = MsgVote ∧ r = MsgVoteResp) ∨ (t = MsgPreVote ∧ r = MsgPreVoteResp) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val #(functions voteRespMsgType [])) (Val #t))
  {{ RET #r; True }}

end spec

end EtcdGrove
end Perennial
