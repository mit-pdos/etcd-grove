/-
## `Count(ctx, lg, kv, key, rangeEnd, revision)` (`range.go`)

**Users.** `EtcdServer.rangeStream` (`v3_server.go:255`: the remaining count after the last page,
at the stream's pinned revision). Snippet: `examples/specreq/txn/read.go` (`ReqRangeStreamPages`).

**Proof sketch.** A count-only `RangeRequest` (`countReq`, fresh, owned: `rangeReqOwn` by W0's
unfold law at the end's reading `endOf rend e`, F1's mapping) and `Range.spec` at it with
`withTotalCount` false (a count-only range counts every key; mvcc's `CountRevisions` checks no
context: `Range.spec`'s context-error case asks `rm.countOnly = false`, so it is excluded).
`resp.Count` read from the reply.

**Changes.** The old spec (`specs-ref`'s `Count.lean`, over the log) restated as `Range`. Round 1:
the `nil`-end premise dropped (the end read as mvcc reads the slice, `endOf`: F1); 3e's API (F4).

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Api

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

/-- **`Count(ctx, lg, kv, key, rangeEnd, rev)`**: the number of present keys of the range of `key`
and the slice `rangeEnd` (as mvcc reads it: `endOf`) at revision `rev` (`0`: the current) of the
state `σ` the caller's update fires at, or mvcc's revision error. -/
def Count.spec : Prop :=
  ∀ (ctx : GoInterface) (o : Option Loc) (lg : Loc) (kv : GoInterface) (γ : Mvcc.MvccName)
    (key rend : GoSlice) (k e : GoString) (rev : w64) (Q : Mvcc.MvccState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ Context.ctxOk ctx ∗ TraceUtil.ctxTraceIs ctx o ∗ ctxTraceOwn o ∗ Zap.isLogger lg ∗
      Mvcc.isMvcc kv γ ∗ Mvcc.mvccReaders γ 1 ∗ key ↦*□ k ∗ rend ↦*□ e ∗
      AU <{ ∃∃ (σ : Mvcc.MvccState), Mvcc.mvccState γ σ }> @ ⊤ \ ↑Mvcc.mvccN, ∅
        <{ Mvcc.mvccState γ σ, COMM Q σ }> }}
    (App (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.Count)) (Val #ctx)) (Val #lg)) (Val #kv)) (Val #key)) (Val #rend)) (Val #rev))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err); Mvcc.mvccReaders γ 1 ∗
      (∃ tr : Loc, traceBack o tr) ∗ ∃ σ : Mvcc.MvccState, Q σ ∗
      ((∃ er : EtcdErr, ⌜(countReq k (endOf rend e) (sint.Z rev)).revErr σ.kv = some er ∧ n = W64 0⌝ ∗
          errIs err er) ∨
       (⌜(countReq k (endOf rend e) (sint.Z rev)).revErr σ.kv = none ∧ err = GoInterface.nil⌝ ∗
          ∃ all : List KV,
          ⌜(σ.kv.storeAt ((countReq k (endOf rend e) (sint.Z rev)).readRev σ.kv)).rangeKVs
              { key := k, rangeEnd := endOf rend e } all ∧ n = W64 all.length⌝)) }}

end spec
end Txn
end EtcdGrove
end Perennial
