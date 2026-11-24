/-
`s.rangeStream(ctx, r, rs)` (`v3_server.go`): the pages of a streamed range, sent on `rs`. Names
only: a trust-boundary spec (auth-mediation M3, option (B), the user's choice 2026-11-21; the later
replacement, (A), a proof over a restated `txn.Range.spec`: `notes/specs-only/ledger.md`,
2026-11-21). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RangeStreamDefs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadOn
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

/-- **`s.rangeStream(ctx, r, rs)`** (names only; the trust boundary of the streamed range), any
goroutine, at a context (`mvcc.txnCtx`, with the trace `t` it carries), with the request side's and
the read side's server facts (`isServerReqM`, `isServerReadM`: the store, the logger, the
configuration's `MaxRequestBytes`), the store's reader token and the logger's reader slot (which it
gives back), for the range request `r` of the get `o` with a valid sort target, its three rewritten
fields owned (`rangeRequestOwn`: the three fields given back, `rangeRequestBack`, not the new key's
contents), and the stream `rs` whose `Send` is a
contract (`rangeSendOk rs Ψ Ξ`).

**It sends only through `rs`, each chunk under the check it is given**: every chunk it sends is a
`rangeChunkIs o` (key-values of `o`'s range, a header `nil` or fresh), and the caller's `□ (∀ resp,
rangeChunkIs o resp -∗ Ψ resp)` (where the caller puts what its permission check established) turns
it into `Send`'s precondition. It returns `nil`, an error of the store's reads (`applyErrIs`, `rangeReadErr`: `txn.Range`'s or
`txn.Count`'s, mvcc's `ErrFutureRev` or `ErrCompacted`, or `rangeKeys`' wrapped context error), or the
error a `Send` returned (`Ξ resp err` of the chunk `resp` it was sending).

Why it is true of Go (`v3_server.go:199-275`, the fork's `goose-lean` branch): its only calls on
`rs` are `rs.Send(&pb.RangeStreamResponse{RangeResponse: out})`, after which it returns that call's
error if not `nil`. `out` is a fresh `&pb.RangeResponse{Kvs: resp.Kvs}` (or, count-only, with no
key-values), its `Header` set only on the last chunk, to a fresh `&pb.ResponseHeader{Revision: ..}`.
`resp` is `txn.Range(ctx, s.Logger(), s.KV(), r, false)` of the request as rewritten: the first
page at `o`'s key, each later page at `nextKey = append(bytes.Clone(lastKey), 0)`, the smallest key after the
previous page's last, with `o`'s range end and every other field unchanged (only `Key`, `Limit` and
`Revision` are written), so each page's keys are in `o`'s range; mvcc reads a `nil` range end as the
key alone, an empty or `"\x00"` one as every key from the key on, any other as `[key, end)`, as
`auth.inRange` does on the model's range end (`txn.rangeEndOf`). The append writes into a fresh
copy of the last key (the fork's cherry-pick of upstream's etcd-io/etcd@9acc0ebe37), never into the
chunk's key-values or mvcc's index. Its errors are those of `txn.Range` and `txn.Count` (the same as `Range`'s,
`rangeResult_errIs`) and of `Send`. It takes no lock but the logger's reader slot and the store's
read transaction, both given back. `More` is set only when the page had `Limit ≥ 1` keys (`Limit` is
at least `1` on each page: `adjustChunkLimit`'s floor and `totalLimit - count > 0` while not done),
so `resp.Kvs[len(resp.Kvs)-1]` is in bounds. Evidence: the Go tests `examples/authmedrangestream/`
(each chunk's keys in the range, through the real server; the review's errors and aliasing).
(errors-is-deadline, 2026-11-23) Since then the post's `applyErrIs` also says that the error tree's
errors of type `context.deadlineExceededError` hold `deadlineExceededError{}` (`deTyped`). Go's
typing makes this true of every Go error: `deadlineExceededError` is a field-less struct type, whose
only value is `deadlineExceededError{}`. The model does not type interface values, and `togRPCError`
compares the error with `context.DeadlineExceeded`, so the fact is stated. It was accepted by the
coordinator under the user's approval of the same typing class (2026-11-23), and review was
requested on #31. -/
abbrev EtcdServer.rangeStream.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (t : Loc) (te : Bool) (r : Loc) (o : OpFull)
    (rs : GoInterface) (Ψ : Loc → IProp GF) (Ξ : Loc → GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗
      mvcc.api.mvccReaders E.γ 1 ∗ srvLgReader s ∗ mvcc.txnCtx ctx cd ∗
      traceutil.ctxTraceIs ctx (some t) ∗ traceutil.ownTrace t te ∗
      rangeRequestOwn r o ∗ ⌜txn.validSortTarget o⌝ ∗
      rangeSendOk rs Ψ Ξ ∗ □ (∀ resp : Loc, rangeChunkIs o resp -∗ Ψ resp) }}
    (App (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"rangeStream"))
      (Val #(GoInterface.ok ctx))) (Val #r)) (Val #rs))
  {{ (err : GoInterface), RET #err; mvcc.api.mvccReaders E.γ 1 ∗ srvLgReader s ∗
      (∃ te' : Bool, traceutil.ownTrace t te') ∗ rangeRequestBack r ∗
      (⌜err = GoInterface.nil⌝ ∨ (⌜err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗ rangeReadErr err) ∨
        ∃ resp : Loc, Ξ resp err) }}

end spec

end EtcdGrove
end Perennial
