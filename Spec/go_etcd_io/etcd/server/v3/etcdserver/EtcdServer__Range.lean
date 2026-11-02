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

/-- **`s.Range(ctx, r)`**, any goroutine, **in the environment's auth mode** (`E.authOn`, at a mode
other than `.any`; the auth-mode merge's step 5, 2026-10-29), at a context, for a range request `r`
holding `o` with a valid sort target, with a read call's resources (`srvRdCall`: the store's reader
slots, the logger's, the committed index `c` the caller knew of), the server's range check at a
lower bound `n` of the auth store's published index the reader holds (`srvAuthLb`,
`auth.authPubLbM`: nothing with auth off), and a read deposit `kvDep γr.kv Q` at the mode's model
(`kvStM E.authOn`: a client's `Get` update, or nothing). Success: the auth store's
`IsRangePermitted` passed for some auth info at states no older than some `m ≥ n`
(`apply.rangeClassFrom`: with auth off, a pass), the info the caller's (`infoBoundM`: with auth on,
the empty user or one bound to the context's token) and, for a linearizable read with auth on, no
older than the auth state the committed log through the read index left (`authFloorAt`); and the
txn package's answer at a certified log of at least two revisions, after the read index unless
serializable, the header's id fields owned, a linearizable one at the mode's model of a committed
raft log `L` at which the deposit gave `□ Q L` (`rangeReadOkM`). Failure: no response and an error
the gRPC layer can take (`applyErrIs`: the read loop's, the auth store's, mvcc's `ErrFutureRev`, or
the context's). The two modes' former specs are instances (`ModeSpecs.lean`, `Range.spec_off`,
`Range.spec_on`). -/
abbrev EtcdServer.Range.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (o : OpFull)
    (ot : Option Loc) (te : Bool) (Q : List EntryModel → IProp GF) (F : mvcc.Log) (n : Nat),
  E.authMode ≠ .any →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ srvAuthLb s E ∗
      auth.authPubLbM E.authMode n ∗ srvRdCall s E γr c ∗ context.isContext ctx cd ∗
      traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗ txn.rangeRequestIs r o ∗ ⌜txn.validSortTarget o⌝ ∗
      kvDep γr.kv Q (kvStM E.authOn γr.kv) ∗ mvcc.idxCert E.γ.idx F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvRdCall s E γr c ∗
      ((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗
          (∃ (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (m : Nat), ⌜n ≤ m⌝ ∗ apply.rangeClassFrom E.authMode m info o ∗
            infoBoundM E.authOn s E (GoInterface.ok ctx) info ∗
            (if o.base.serializable then iprop(True) else authFloorAt E.authMode γr c m)) ∗
          rangeReadOkM E.authOn E γr c F o resp Q) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err)) }}

end spec

end EtcdGrove
end Perennial
