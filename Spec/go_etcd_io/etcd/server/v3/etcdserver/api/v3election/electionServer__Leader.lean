/-
`(*electionServer).Leader(ctx, req)` (`server/etcdserver/api/v3election/election.go`; the auth
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

/-- **`Leader(ctx, req)`**: a session of the server's client (`session(ctx, -1)`) and the lookup of
the leader of the election on the request's name (`NewElection`, `Election.Leader`): its read is
of the keys under `name/`. It returns the response `{Header, Kv}` of the leader's key-value
(`leaderKvAt`: the oldest key under `name/` at the header's revision), or no response and an
error. -/
abbrev electionServer.Leader.spec : Prop :=
  ∀ (es c req : Loc) (nsl : GoSlice) (name : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3election ∗
      isElectionServer es c ∗ electionClientOk c ∗
      structFieldRef v3electionpb.LeaderRequest go!"Name" req ↦□ nsl ∗ nsl ↦*□ name ∗
      context.isContext ctx cs ∗ context.isCancelCtxCtx ctx cs }}
    (App (App (Val (es @!! go.GoType.PointerType electionServer.ty @!! go!"Leader"))
      (Val #(GoInterface.ok ctx))) (Val #req))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (hdr kp : Loc) (R : w64) (kv : EtcdKv)
          (v : v3electionpb.LeaderResponse),
        resp ↦ v ∗ ⌜v.Header' = hdr ∧ v.Kv' = kp⌝ ∗ hdrRevAt hdr R ∗ etcdReached R ∗
        kvValAt kp kv ∗ leaderKvAt (name ++ go!"/") kv R) ∨
      ⌜resp = null ∧ err ≠ GoInterface.nil⌝ }}

end spec

end v3election
end EtcdGrove
end Perennial
