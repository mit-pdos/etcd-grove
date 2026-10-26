/-
`(*electionServer).Campaign(ctx, req)` (`server/etcdserver/api/v3election/election.go`; the auth
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

/-- **`Campaign(ctx, req)`**: a session over the request's lease (`session`) and a campaign of the
election on the request's name with its value (`NewElection`, `Election.Campaign`): its keys are
under `name/`. It returns the response `{Header, Leader: {Name, Key, Rev, Lease}}` of the
campaign's key (`keyValAt`, under `name/`) and its outcome (`leaderAt`: the leader, or
`campaignLost`: its key gone before it won), or no response and an error. -/
abbrev electionServer.Campaign.spec : Prop :=
  ∀ (es c req : Loc) (nsl vsl : GoSlice) (name val : GoString) (lease : w64) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3election ∗
      isElectionServer es c ∗ electionClientOk c ∗
      structFieldRef v3electionpb.CampaignRequest go!"Name" req ↦□ nsl ∗ nsl ↦*□ name ∗
      structFieldRef v3electionpb.CampaignRequest go!"Lease" req ↦□ lease ∗
      structFieldRef v3electionpb.CampaignRequest go!"Value" req ↦□ vsl ∗ vsl ↦*□ val ∗
      context.isContext ctx cs ∗ context.isCancelCtxCtx ctx cs }}
    (App (App (Val (es @!! go.GoType.PointerType electionServer.ty @!! go!"Campaign"))
      (Val #(GoInterface.ok ctx))) (Val #req))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (key : GoString) (rev r rv R id : w64) (hdr lk : Loc)
          (ksl : GoSlice) (v : v3electionpb.CampaignResponse) (lv : v3electionpb.LeaderKey),
        resp ↦ v ∗ lk ↦ lv ∗ ksl ↦* key ∗
        ⌜v.Header' = hdr ∧ v.Leader' = lk ∧ lv.Name' = nsl ∧ lv.Key' = ksl ∧ lv.Rev' = rev ∧
          lv.Lease' = id ∧ id ≠ W64 0 ∧ (lease ≠ W64 0 → id = lease)⌝ ∗
        hdrRevAt hdr r ∗ etcdReached R ∗ keyValAt (name ++ go!"/") key rev val rv ∗
        (leaderAt (name ++ go!"/") key rev R ∨ campaignLost (name ++ go!"/") key rev R) ∗
        ⌜(name ++ go!"/") <+: key⌝) ∨
      ⌜resp = null ∧ err ≠ GoInterface.nil⌝ }}

end spec

end v3election
end EtcdGrove
end Perennial
