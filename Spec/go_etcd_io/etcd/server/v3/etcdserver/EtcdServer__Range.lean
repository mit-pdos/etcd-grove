/-
`s.Range(ctx, r)` (`v3_server.go`): a linearizable (unless `Serializable`) read of the KV, through `doSerialize`.
Lean-first (no Rocq counterpart); the request path's unit 3b (2026-10-12).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthClass
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadOn

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

/-- **`s.Range(ctx, r)`**, any goroutine, at a context, for a range request `r` holding `o` with
a valid sort target, with a read call's resources (`srvRdCall`: the store's reader slots, the
logger's, the committed index `c` the caller knew of): success, the txn package's answer at a
certified log of at least two revisions, after the read index unless serializable, the header's
id fields owned (`rangeReadOk`); failure, no response and an error the gRPC layer can take (the
read loop's, the auth store's, mvcc's `ErrFutureRev`, or the context's: `fmt.Errorf`'s in
Perennial's model, `applyErrIs` by the server's package facts). 2026-10-14 (unit T1): with a read
deposit `kvDep γr.kv Q` (a client's `Get` update, or nothing), a linearizable success read the KV
model of a committed raft log `L` at which the deposit gave `□ Q L` (`rangeReadOk`). 2026-10-23
(auth plan A1): a success passed the auth store's `IsRangePermitted` for some auth info (the
context's token's, or the empty one): with auth on, that info's read permission class of the
request's range (`apply.rangeClass`). -/
abbrev EtcdServer.Range.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (o : OpFull)
    (ot : Option Loc) (te : Bool) (Q : List EntryModel → IProp GF) (F : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ isServerRead s E γr ∗ srvRdCall s E γr c ∗ context.isContext ctx cd ∗
      traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗ txn.rangeRequestIs r o ∗ ⌜txn.validSortTarget o⌝ ∗
      kvDep γr.kv Q ∗ mvcc.idxCert E.γ.idx F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvRdCall s E γr c ∗
      ((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ (∃ info, apply.rangeClass E.authMode info o) ∗
          rangeReadOk E γr c F o resp Q) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err)) }}

/-- **`spec` with auth on** (the auth plan's E3s, 2026-10-27; `notes/decisions.md`, "E3s of the
auth plan"): in the mode `on γa`, over the request and read views with auth on (`isServerReqM
true`, `isServerReadM true`), the read deposit at the mode-`on` model's state (`kvDep γr.kv Q
(kvStM true γr.kv)`), and a lower bound `n` of the auth store's published index the reader holds
(`auth.authPubLbM`), with the server's range check at it (`srvAuthLb`). Success: the auth store's
`IsRangePermitted` passed for some auth info at states no older than some `m ≥ n`
(`apply.rangeClassFrom`: a state recorded at an index at least `m` permits the read of the
request's range) and, for a linearizable read, no older than the auth state the committed log
through the read index left (`authFloorAt`, E3u: the applied index's invariant has that state
published, and `Range` checks after waiting for the read index, so the reader needs no bound of its
own beyond `n`, which `auth.authPubLb γa 0` always gives), and the read
as `spec`'s, a linearizable one at the mode-`on` model of a committed raft log `L` at which the
deposit gave `□ Q L` (`rangeReadOkM true`). -/
abbrev EtcdServer.Range.specOn : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (o : OpFull)
    (ot : Option Loc) (te : Bool) (Q : List EntryModel → IProp GF) (F : mvcc.Log) (n : Nat)
    (γa : auth.AuthNames),
  E.authMode = .on γa →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM true s E ρ ∗ isServerReadM true s E γr ∗ srvAuthLb s E ∗
      auth.authPubLbM E.authMode n ∗ srvRdCall s E γr c ∗ context.isContext ctx cd ∗
      traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗ txn.rangeRequestIs r o ∗ ⌜txn.validSortTarget o⌝ ∗
      kvDep γr.kv Q (kvStM true γr.kv) ∗ mvcc.idxCert E.γ.idx F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvRdCall s E γr c ∗
      ((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗
          (∃ (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (m : Nat), ⌜n ≤ m⌝ ∗ apply.rangeClassFrom E.authMode m info o ∗
            (if o.base.serializable then iprop(True) else authFloorAt E.authMode γr c m)) ∗
          rangeReadOkM true E γr c F o resp Q) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err)) }}

end spec

end EtcdGrove
end Perennial
