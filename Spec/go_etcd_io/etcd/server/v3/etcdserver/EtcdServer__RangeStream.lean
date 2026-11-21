/-
`s.RangeStream(r, rs)` (`v3_server.go`): a linearizable (unless `Serializable`) streamed read of the KV,
through `doSerialize`, its pages sent on `rs` by `rangeStream` (names only, a trust-boundary spec).
Lean-first (no Rocq counterpart); auth-mediation M3 (2026-11-21), row 2 of `etc/auth-table.txt`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RangeStreamDefs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthClass
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthCheckTxnLb
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReqOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadWhy
public import Proof.context.LibKeys

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

/-- **The streamed range `o` passed the permission check** on the server `s` (persistent): the auth
store's `IsRangePermitted` of `o`'s `[key, end)` passed for some auth info at states no older than
some `m ≥ n` (`apply.rangeClassFrom`: with auth off, a pass), the info the caller's (`infoBoundM`:
with auth on, the empty user or one bound to the context's token `tok`), the store published through
`m` (`auth.authPubLbM`). What `Range`'s success states of its check. -/
def rangeStreamPassed (s : Loc) (E : apply.AEnv GF) (n : Nat) (tok : Option GoString) (o : OpFull) :
    IProp GF :=
  iprop(∃ (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (m : Nat), ⌜n ≤ m⌝ ∗
    apply.rangeClassFrom E.authMode m info o ∗ infoBoundM E.authOn s E tok info ∗
    auth.authPubLbM E.authMode m)

instance rangeStreamPassed_persistent (s : Loc) (E : apply.AEnv GF) (n : Nat)
    (tok : Option GoString) (o : OpFull) : Persistent (rangeStreamPassed (GF := GF) s E n tok o) := by
  unfold rangeStreamPassed; infer_instance

/-- **`s.RangeStream(r, rs)`**, any goroutine, **in the environment's auth mode** (`E.authOn`, at a
mode other than `.any`), for a range request `r` of the get `o` with a valid sort target, its three
rewritten fields owned (`rangeRequestOwn`), on the stream `rs` whose `Context()` returns the context
`ctx` (`rangeStreamCtx`) and whose `Send` is a contract (`rangeSendOk rs Ψ Ξ`), with a read call's
resources (`srvRdCall`) and the server's range check at a lower bound `n` of the auth store's
published index (`srvAuthLb`, `auth.authPubLbM`), as `Range`'s.

**Every chunk it sends passed the check** (auth-mediation M3): `Send`'s precondition `Ψ resp` is
given, through the caller's `□ (∀ resp, rangeChunkIs o resp -∗ rangeStreamPassed s E n tok o -∗ Ψ
resp)`, for a chunk of `o`'s range (`rangeChunkIs`) and the passed check of `o`'s `[key, end)`
(`rangeStreamPassed`, what `Range`'s success states). The check is made once, before the first page
(`doSerialize`'s `chk`); a revocation during the stream is seen only by `doSerialize`'s revision
re-check after the last page, which then returns `ErrAuthOldRevision` after the chunks were sent
(`nonissues/etcd-rangestream-auth-revoked-midstream.md`).

It returns `nil`, an error the gRPC layer can take (`applyErrIs`) with why, if the auth checks refused
it (`rangeWhyOut`, as `Range`'s: the request side's reasons, the read check's refusal, `doSerialize`'s
revision re-check, or the read index's or the read's own error), or an error a `Send` returned
(`Ξ resp err`). -/
abbrev EtcdServer.RangeStream.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (tok : Option GoString) (r : Loc) (o : OpFull) (rs : GoInterface)
    (Ψ : Loc → IProp GF) (Ξ : Loc → GoInterface → IProp GF)
    (ot : Option Loc) (te : Bool) (n : Nat),
  E.authMode ≠ .any →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ srvAuthLb s E ∗
      auth.authPubLbM E.authMode n ∗ srvRdCall s E γr c ∗
      rangeStreamCtx rs ctx ∗ context.isContext ctx cd ∗ context.libCtxOk ctx ∗
      □ (⌜E.authOn = true⌝ → auth.ctxToken (GoInterface.ok ctx) tok) ∗
      traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗
      rangeRequestOwn r o ∗ ⌜txn.validSortTarget o⌝ ∗
      rangeSendOk rs Ψ Ξ ∗
      □ (∀ resp : Loc, rangeChunkIs o resp -∗ rangeStreamPassed s E n tok o -∗ Ψ resp) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"RangeStream")) (Val #r))
      (Val #rs))
  {{ (err : GoInterface), RET #err; srvRdCall s E γr c ∗ rangeRequestBack r ∗
      (⌜err = GoInterface.nil⌝ ∨
       (⌜err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗ rangeWhyOut s E.authMode n tok o err) ∨
       ∃ resp : Loc, Ξ resp err) }}

end spec

end EtcdGrove
end Perennial
