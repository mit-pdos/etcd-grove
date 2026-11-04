/-
`s.Txn(ctx, r)` (`v3_server.go`): a read-only transaction read locally (as `Range`), a writing one through raft (as `Put`).
Lean-first (no Rocq counterpart); the request path's unit 3b (2026-10-12).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReqOn
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

/-- **`Txn(ctx, r)`, in the server's auth mode** (the auth component's stage 4; it replaces
`spec`, `specOn` and `specOnR`). `t` is the transaction `r` describes.

*Read-only* (`txnReadonly t`): the read path. A linearizable read waits for the read index, then
`doSerialize` runs the auth check (`CheckTxnAuth`) and the txn package's read. The caller also
gives the auth store's lower bounds (`srvAuthLb`, and `authPubLbM E.authMode n`, which is `True`
with auth off). A success gives:
- the answer read at a log `F` extends (`txnReadOkM`, at the mode's model);
- the auth state the check met, at least `n`;
- the user's verdicts there (`txnClassFrom`, which at `.off` is every check passed);
- the user bound to the context (`infoBoundM`, `True` off);
- unless serializable, that state is at the read index's floor (`authFloorAt`).

An error leaves `resp` unconstrained, as Go returns it.

*Writing*: the proposal path. The caller's permit (`txnPermitM`) gives the update its step and,
with auth on, the transaction's shape checked against the permission cache and the update's
grant. A success is applied by the apply thread (`txnAppliedOk`). An error is `applyErrIs` with
what was applied or deposited (`txnErrOkM`).

**The gated grant.** With auth on, a success also names the grant: the wire transaction `tw`,
the header `hm` the server stamped, whose user is bound to the context (`hdrBoundM`), the
committed log `L` before the entry at which the request was granted (`grantedAt`), and the
publications after it (`pubAfterM`). Off, the row is `□ (⌜false = true⌝ → …)`, which is `True`. It
is behind `□` because it is persistent and a caller opens it more than once; `srvKVAnsM`'s rows
need no `□` (`KVAns.ok` is not persistent).

**Scope restriction (read-only only).** `⌜E.authMode ≠ .any⌝` is required of a read-only
transaction: its check is not covered in the mode `.any`, where the server has no fixed auth
state. It is `specOnR`'s (its `γa`) and `Range.spec`'s restriction (step 5, `notes/decisions.md`,
"The request path in the environment's mode", the user's B). A writing transaction is covered in every mode, as by today's
`spec` and `specOn`.

**Departure.** The writing case takes all of `srvRdCall`. The writing path needs only its logger's
field and reader slot (`EnsureTrace` reads `s.Logger()`, `v3_server.go:341`) and the auth store's
reader resource `E.RD` (`raftRequest`, `Spec/…/EtcdServer__raftRequest.lean:49`). The rest of
`srvRdCall` (`storeReader`, `committedAtLeast`, `srvReadReader`) is the read path's. Today's `spec`
does the same, and every writing caller holds `srvRdCall`, so this is no regression. The footprint
is wider than the code's.

`Range.spec` states its restriction as a Lean premise `E.authMode ≠ .any →`
(`Spec/.../EtcdServer__Range.lean:51`). `Txn.spec` states it in the precondition, guarded by
`txnReadonly t` as the other read-only premises are. `Range.spec` converts when it next
changes. -/
abbrev EtcdServer.Txn.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (t : TxnModel)
    (Q : KVState → IProp GF) (Qr : List EntryModel → IProp GF) (ot : Option Loc) (te : Bool)
    (F : mvcc.Log) (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗
      srvLeadTimeReader s ∗ idCred ρ.ids 1 ∗
      srvRdCall s E γr c ∗ context.isContext ctx cd ∗ traceutil.ctxTraceIs ctx ot ∗
      traceutil.ownTraceOpt ot te ∗ txn.txnRequestIs r t ∗
      ⌜txn.txnReadonly t = true → txn.txnGetsOk t ∧ E.authMode ≠ .any⌝ ∗
      ⌜txn.txnReadonly t = false → apply.txnDepthOk t⌝ ∗ mvcc.idxCert E.γ.idx F ∗
      (if txn.txnReadonly t then
         iprop(srvAuthLb s E ∗ auth.authPubLbM E.authMode n ∗ kvDep γr.kv Qr (kvStM E.authOn γr.kv))
       else txnPermitM E.authOn ρ.raft ρ.kv (hdrBoundM E.authOn s E (GoInterface.ok ctx)) t Q) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Txn"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      srvLeadTimeReader s ∗ srvRdCall s E γr c ∗
      if txn.txnReadonly t then
        iprop(idCred ρ.ids 1 ∗
          ((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗
              (∃ (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (m : Nat), ⌜n ≤ m⌝ ∗
                txnClassFrom E.authMode m info t ∗ infoBoundM E.authOn s E (GoInterface.ok ctx) info ∗
                (if txn.txnSerializable t then iprop(True) else authFloorAt E.authMode γr c m)) ∗
              txnReadOkM E.authOn E γr c F t Qr resp) ∨
           (⌜err ≠ GoInterface.nil⌝ ∗ applyErrIs err)))
      else
        iprop((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ txnAppliedOk E ρ.rd F t Q resp ∗
            □ (⌜E.authOn = true⌝ → ∃ (tw : txn.TxnModelW) (hm : apply.HeaderModel) (L : List EntryModel),
              ⌜tw.toModel = t ∧ grantedAt ρ.kv srvAuthSt0 (apply.withHeader (irrTxn tw) hm) L⌝ ∗
              hdrBoundM E.authOn s E (GoInterface.ok ctx) hm ∗
              pubAfterM E.authOn E ρ (apply.withHeader (irrTxn tw) hm) L)) ∨
          (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
            txnErrOkM E.authOn s E ρ (GoInterface.ok ctx) F t err)) }}

end spec

end EtcdGrove
end Perennial
