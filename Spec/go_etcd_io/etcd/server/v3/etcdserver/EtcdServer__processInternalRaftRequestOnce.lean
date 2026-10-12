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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The handoff.** `s.processInternalRaftRequestOnce(ctx, r)`, any goroutine, at a context, for
a request `r` holding `rq` but for its header (which it sets: the fresh id `Next` returns, the
auth info's user name and revision), with no `ID` (the server's requests have none; `Apply` takes
the header's), one id credit and a reader slot of `s.leadTimeMu`:
* success (`err = nil`): `res` is the apply thread's result of applying `rq'`, the request the
  proposed data decode to (`irrWireOf`: `rq` with its header, up to the model's `[0]` range ends):
  `resultIs E rq' res` (the apply package's `applyStep` and `applyResultIs` at the KV state the
  entry met, and mvcc's certificate of the log after);
* failure: no result, an error, and the proposal, if made, deposited (`srvMaybeDeposited`: it may
  still be applied: the request limit, the auth store's error, the marshal's error, the size
  limit come before the proposal; `Propose`'s error, the context's (`parseProposeCtxErr`) and the
  server's stop (`ErrStopped`) after it). -/
abbrev EtcdServer.processInternalRaftRequestOnce.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (p : Loc) (rq : apply.IRRModel),
  rq.id = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ srvLeadTimeReader s ∗ idCred ρ.ids 1 ∗ context.isContext ctx cd ∗
      irrNoHdrIs p rq ∗
      (∃ h0 : Loc, structFieldRef etcdserverpb.InternalRaftRequest go!"Header" p ↦ h0) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"processInternalRaftRequestOnce"))
      (Val #(GoInterface.ok ctx))) (Val #p))
  {{ (res : Loc) (err : GoInterface), RET (PairV #res #err); srvLeadTimeReader s ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel),
          ⌜irrWireOf (apply.withHeader rq hm) rq'⌝ ∗ resultIs E rq' res) ∨
       (⌜res = null ∧ err ≠ GoInterface.nil⌝ ∗ srvMaybeDeposited ρ rq)) }}

end spec

end EtcdGrove
end Perennial
