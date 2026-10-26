/-
`s.processInternalRaftRequestOnce(ctx, r)` (`v3_server.go`): propose the request through raft
and wait for the apply thread's result. Lean-first (no Rocq counterpart); see `InvProposer.lean`,
`InvRequest.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The handoff.** `s.processInternalRaftRequestOnce(ctx, r)`, any goroutine, at a context, for
a request `r` holding `rq` but for its header (which it sets: the fresh id `Next` returns, the
auth info's user name and revision), with no `ID` (the server's requests have none; `Apply` takes
the header's), one id credit, a reader slot of `s.leadTimeMu` and (2026-10-14, unit A2) the auth store's reader
resource `E.RD` (`AuthInfoFromCtx`):
* success (`err = nil`): `res` is the apply thread's result of applying `rq'`, the request the
  proposed data decode to (`irrWireOf`: `rq` with its header, up to the model's `[0]` range ends):
  `resultIs E rq' res` (the apply package's `applyStep` and `applyResultIs` at the KV state the
  entry met, and mvcc's certificate of the log after; 2026-10-14, unit C2a: `resultIsW E ρ.rd`, with
  the witness that the log after is applied through an index of the committed log, `appliedWit`);
  and (2026-10-14, unit T1) the result `Qr` of the proposal's update at a committed log (`reqPropOk
  ρ.kv rq Qr`: the request has no KV write, `Qr` trivial; or, since 2026-10-15 (unit T2), it is a
  plain write, a put, a delete or a transaction, with its client's update over the whole state,
  `Qr L` the client's `□ Q` at the state of `L`'s model): `□ Qr L` of the committed log `L` before
  the entry the result is of, whose model is the log `lb` the entry met (unit W-M3: the result's
  `y.log`, so the update's state is the write's);
* failure: no result, an error the gRPC layer can take (`applyErrIs`: in an error tree, a safe map
  key, with a message; 2026-10-12, unit 3a), and the proposal, if made, deposited (`srvMaybeDeposited`: it may
  still be applied: the request limit, the auth store's error, the marshal's error, the size
  limit come before the proposal; `Propose`'s error, the context's (`parseProposeCtxErr`) and the
  server's stop (`ErrStopped`) after it). -/
abbrev EtcdServer.processInternalRaftRequestOnce.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (p : Loc) (rq : apply.IRRModel)
    (Qr : List EntryModel → IProp GF) (F : mvcc.Log),
  rq.id = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ idCred ρ.ids 1 ∗ context.isContext ctx cd ∗
      irrNoHdrIs p rq ∗ reqPropOk ρ.kv rq Qr ∗
      (∃ h0 : Loc, structFieldRef etcdserverpb.InternalRaftRequest go!"Header" p ↦ h0) ∗
      mvcc.idxCert E.γ.idx F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"processInternalRaftRequestOnce"))
      (Val #(GoInterface.ok ctx))) (Val #p))
  {{ (res : Loc) (err : GoInterface), RET (PairV #res #err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel),
          ⌜irrWireOf (apply.withHeader rq hm) rq'⌝ ∗ apply.resTrace res ∗
          ∃ lb : mvcc.Log, resultIsW E ρ.rd rq' F res lb ∗
            ∃ L : List EntryModel, srvRLogLb ρ.raft L ∗ ⌜kvModel ρ.kv L = lb⌝ ∗ □ Qr L) ∨
       (⌜res = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗ srvMaybeDeposited ρ rq)) }}

end spec

end EtcdGrove
end Perennial
