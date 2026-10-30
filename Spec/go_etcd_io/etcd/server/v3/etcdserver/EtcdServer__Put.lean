/-
`s.Put(ctx, r)` (`v3_server.go`): a put through raft and the apply thread. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReqOn

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

/-- **`s.Put(ctx, r)`**, any goroutine, **in the environment's auth mode** (`E.authOn`; the
auth-mode merge's step 5, 2026-10-29), at a context, for a put request `r` holding `op`, with one id
credit and a reader slot of `s.leadTimeMu`, the put's permission (`putPermitM`: off, the lease `0`
and the client's update fired at most once, `kvOpAu1`; on, also the key not empty, and the update
told its grant at the client's lower bound of the requested log, `writeGrantG`, under the binding of
the header to the context): success, the apply package's answer to the put (`putOutcomeIs`, no
error: applied, `putModel`'s, at the log `x.log` the entry met) of the request with the header the
server set (`hm`), dispatched at `x` to `x'` (`applyStep`), the response header's id fields owned
(`appliedHdr`), with mvcc's certificate of the log after, the token of the revision it appended
(`revMinted`), the log after applied through an index of the committed log (`appliedWit`), and `Q`
of the state the update fired at; with auth on, the header bound to the context (`hdrBoundM`) and
the grant at the committed log `L` before the entry (`grantedAt`), the auth state after it
published (`pubAfterM`). Failure: no response and an error the gRPC layer can take
(`applyErrIs`): the apply's (`appliedErr`, at a header bound to the context with auth on), or the
proposal's (made or not; if made, deposited: it may still be applied). The two modes' former specs
are instances (`ModeSpecs.lean`, `Put.spec_off`, `Put.spec_on`). -/
abbrev EtcdServer.Put.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (r : Loc) (op : OpFull)
    (Q : KVState → IProp GF) (F : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM E.authOn s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ idCred ρ.ids 1 ∗ context.isContext ctx cd ∗
      txn.putRequestIs r op ∗ putPermitM E.authOn ρ.raft ρ.kv (hdrBoundM true s E (GoInterface.ok ctx)) op Q ∗ mvcc.idxCert E.γ.idx F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Put"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (hm : apply.HeaderModel) (x x' : apply.ApplyKV)
          (o : apply.Outcome) (skip : Bool),
          ⌜apply.applyStep (apply.withHeader (irrPut op) hm) true x x' (.dispatched o skip) ∧
            (∃ log', o = .applied log' false) ∧ F <+: x.log⌝ ∗
          apply.putOutcomeIs x.log op resp GoInterface.nil o ∗
          apply.appliedHdr x.log (structFieldRef etcdserverpb.PutResponse go!"Header" resp) ∗
          mvcc.idxCert E.γ.idx x'.log ∗ revMinted E x.log x'.log ∗ appliedWit ρ.rd x'.log ∗
          mvcc.certOk E.γ x'.log ∗ Q (kvStateOf x.log) ∗
          hdrBoundM E.authOn s E (GoInterface.ok ctx) hm ∗
          □ (⌜E.authOn = true⌝ → ∃ L, ⌜grantedAt ρ.kv srvAuthSt0 (apply.withHeader (irrPut op) hm) L⌝ ∗
            pubAfterM true E ρ (apply.withHeader (irrPut op) hm) L)) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
         ((∃ hm : apply.HeaderModel, appliedErr E (apply.withHeader (irrPut op) hm) F err ∗
            hdrBoundM E.authOn s E (GoInterface.ok ctx) hm) ∨
          srvMaybeDeposited ρ (irrPut op)))) }}

end spec

end EtcdGrove
end Perennial
