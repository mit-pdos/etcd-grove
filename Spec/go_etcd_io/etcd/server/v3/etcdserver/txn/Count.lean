/-
## `Count(ctx, lg, kv, key, rangeEnd, revision)` (`range.go`)

**Users.** `EtcdServer.rangeStream` (`v3_server.go:255`: the remaining count after the last page,
at the stream's pinned revision). Snippet: `examples/specreq/txn/read.go` (`ReqRangeStreamPages`).

**Proof sketch.** A count-only `RangeRequest` (`countReq`, fresh, owned: `rangeReqOwn` by W0's
unfold law, its range end the caller's slice) and `Range.spec` at it with `withTotalCount` false
(a count-only range counts every key: `rangeOut`'s first case; mvcc's `CountRevisions` checks no
context, so no context error: 3e's count-only `Range`). `resp.Count` read from the reply.

**Changes.** The old spec (`specs-ref`'s `Count.lean`, over the log) restated as `Range`.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Txn

open Iris Iris.BI EtcdModel EtcdWire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- **`Count(ctx, lg, kv, key, rangeEnd, rev)`**: the number of present keys of `[key, rangeEnd)` at
revision `rev` (`0`: the current) of the state `h` the caller's update fires at, or mvcc's revision
error. An empty `rangeEnd` must be `nil` (the one key), as off the wire. -/
def Count.spec : Prop :=
  ∀ (ctx : GoInterface) (lg : Loc) (kv : GoInterface) (γ : MvccName) (key rend : GoSlice)
    (k e : GoString) (rev : w64) (Q : KVHist → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ Context.ctxOk ctx ∗ Zap.isLogger lg ∗ mvccKV kv γ ∗ threadTok ∗
      key ↦*□ k ∗ rend ↦*□ e ∗ ⌜e = [] → rend = slice.nil⌝ ∗
      AU <{ ∃∃ (h : KVHist), mvccState γ h }> @ ⊤ \ ↑mvccN, ∅
        <{ mvccState γ h, COMM Q h }> }}
    (App (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.Count)) (Val #ctx)) (Val #lg)) (Val #kv)) (Val #key)) (Val #rend)) (Val #rev))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err); threadTok ∗ ∃ h : KVHist, Q h ∗
      ((∃ er : EtcdErr, ⌜(countReq k e (sint.Z rev)).revErr h = some er ∧ n = W64 0⌝ ∗ errIs err er) ∨
       (⌜(countReq k e (sint.Z rev)).revErr h = none ∧ err = GoInterface.nil⌝ ∗ ∃ all : List KV,
          ⌜(h.storeAt ((countReq k e (sint.Z rev)).readRev h)).rangeKVs
              { key := k, rangeEnd := e } all ∧ n = W64 all.length⌝)) }}

end spec
end Txn
end EtcdGrove
end Perennial
