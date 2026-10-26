/-
`(*electionServer).Proclaim(ctx, req)` (`server/etcdserver/api/v3election/election.go`; the auth
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

/-- **`Proclaim(ctx, req)`**: for a request without a leader, no response and
`ErrMissingLeaderKey`; otherwise a session over the leader's lease (`session`) and a
proclamation of the request's value as the leader `key` at `rev` (`ResumeElection` on the
leader's name, `Election.Proclaim`): its write is to the request's leader key. It returns the
response `{Header}` of the proclamation (`proclaimedAt`, at the session's lease: the leader's), or
no response and an error. The leader's name is non-empty (`ResumeElection`'s spec requires a
non-empty prefix; Go does not). -/
abbrev electionServer.Proclaim.spec : Prop :=
  ∀ (es c req lk : Loc) (vsl : GoSlice) (name key val : GoString) (rev lease : w64)
    (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3election ∗
      isElectionServer es c ∗ electionClientOk c ∗
      structFieldRef v3electionpb.ProclaimRequest go!"Leader" req ↦□ lk ∗
      (⌜lk = null⌝ ∨ leaderKeyAt lk name key rev lease ∗ ⌜name ≠ []⌝) ∗
      structFieldRef v3electionpb.ProclaimRequest go!"Value" req ↦□ vsl ∗ vsl ↦*□ val ∗
      context.isContext ctx cs ∗ context.isCancelCtxCtx ctx cs }}
    (App (App (Val (es @!! go.GoType.PointerType electionServer.ty @!! go!"Proclaim"))
      (Val #(GoInterface.ok ctx))) (Val #req))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜lk = null ∧ resp = null⌝ ∗ globalAddr ErrMissingLeaderKey ↦□ err ∗
        ⌜err ≠ GoInterface.nil⌝) ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ (hdr : Loc) (v : v3electionpb.ProclaimResponse),
        resp ↦ v ∗ ⌜v.Header' = hdr⌝ ∗
        (⌜¬ name <+: key⌝ ∨ ∃ (r id : w64), hdrRevAt hdr r ∗ etcdReached r ∗
          proclaimedAt name key rev val id r ∗ ⌜id ≠ W64 0 ∧ (lease ≠ W64 0 → id = lease)⌝)) ∨
      ⌜resp = null ∧ err ≠ GoInterface.nil⌝ }}

end spec

end v3election
end EtcdGrove
end Perennial
