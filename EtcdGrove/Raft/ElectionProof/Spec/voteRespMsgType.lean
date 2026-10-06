/-
Port of `election_proof/spec_voteRespMsgType.v`.
-/
import EtcdGrove.Raft.ElectionProof.Defs

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

/-- `voteRespMsgType(MsgVote)` is `MsgVoteResp`. -/
abbrev voteRespMsgType.spec : Prop :=
  ∀ (t : w32),
  t = MsgVote →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val #(functions voteRespMsgType [])) (Val #t))
  {{ RET #MsgVoteResp; True }}

end spec

end EtcdGrove
end Perennial
