/-
`(*electionServer).Resign(ctx, req)` (`server/etcdserver/api/v3election/election.go`; the auth
plan's A3c, 2026-10-24). Lean-first (no Rocq counterpart); see `v3election/Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3election.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3election

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency concurrency
  _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v3election

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v3election.Assumptions]

/-- **`Resign(ctx, req)`**: for a request without a leader, no response and
`ErrMissingLeaderKey`; otherwise a session over the leader's lease (`session`) and a resignation
of the leader `key` at `rev` (`ResumeElection` on the leader's name, `Election.Resign`): its write
is the delete of the request's leader key. It returns the response `{Header}` of the resignation
(`notLeaderAt`: the key no longer the leader's), or no response and an error. The leader's name
is non-empty (`ResumeElection`'s spec requires a non-empty prefix; Go does not).

The request's leader's name and key are at most the server's receive limit long
(`v3rpc.grpcRecvBytesOk`, the receive-size fact: grpc's server decoded the request under etcd's
limit `v3rpc.etcdMaxRecvMsgSize maxReq`, `maxReq` the configuration's `MaxRequestBytes`, which
meets `v3rpc.etcdMaxRequestBytesOk`; 2026-10-30, `notes/decisions.md`, "The receive-size
fact"). -/
abbrev electionServer.Resign.spec : Prop :=
  ∀ (es c req lk : Loc) (name key : GoString) (rev lease : w64)
    (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (maxReq : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3election ∗
      isElectionServer es c ∗ electionClientOk c ∗
      ⌜v3rpc.etcdMaxRequestBytesOk maxReq⌝ ∗
      structFieldRef v3electionpb.ResignRequest go!"Leader" req ↦□ lk ∗
      (⌜lk = null⌝ ∨ leaderKeyAt lk name key rev lease ∗ ⌜name ≠ []⌝ ∗
        ⌜v3rpc.grpcRecvBytesOk (v3rpc.etcdMaxRecvMsgSize maxReq) name ∧
          v3rpc.grpcRecvBytesOk (v3rpc.etcdMaxRecvMsgSize maxReq) key⌝) ∗
      context.isContext ctx cs ∗ context.isCancelCtxCtx ctx cs }}
    (App (App (Val (es @!! go.GoType.PointerType electionServer.ty @!! go!"Resign"))
      (Val #(GoInterface.ok ctx))) (Val #req))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜lk = null ∧ resp = null⌝ ∗ globalAddr ErrMissingLeaderKey ↦□ err ∗
        ⌜err ≠ GoInterface.nil⌝) ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ (hdr : Loc) (v : v3electionpb.ResignResponse),
        resp ↦ v ∗ ⌜v.Header' = hdr⌝ ∗
        (⌜¬ name <+: key⌝ ∨ ∃ R : w64, hdrRevAt hdr R ∗ etcdReached R ∗ notLeaderAt name key rev R)) ∨
      ⌜resp = null ∧ err ≠ GoInterface.nil⌝ }}

end spec

end v3election
end EtcdGrove
end Perennial
