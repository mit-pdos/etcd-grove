/-
`concurrency.NewSTM(c, apply, so...)` (`client/v3/concurrency/stm.go`).

Users: etcd's tests (`tests/integration/clientv3/concurrency/example_stm_test.go`: a
transfer between accounts keeping their sum, `NewSTM` with the default level;
`tests/integration/clientv3/experimental/recipes/v3_stm_test.go`-style uses: every level,
`WithPrefetch`, `WithAbortContext`, an aborted closure), etcd's benchmark tool (`tools/benchmark`,
not in the pinned sources). No production caller in the pinned etcd, raft, Kubernetes or
`examples/`. Snippets: `concurrency/stm.go` (`ReqSTMTransfer`, `ReqSTMLevels`, `ReqSTMPrefetch`,
`ReqSTMAbort`).

Proof sketch: `Client.Ctx.spec` (1c); the options (`stmOptAt_call`, a fresh struct, persisted);
with prefetch keys, the wrapping closure's `applyOk` from `apply`'s and `STM.GetTriple`
(`stmAt_methods`: its value dropped, the frame threaded); `mkSTM.spec` (`stmStale`, the read
permission `etcdPeek` from the lent one), `runSTM.spec`.

Changes: from `specs-ref`'s `NewSTM.lean`: the result over the cluster's states (`stmResult`:
`etcdLb` of the commit's states and `stmCommitted`) instead of the old `stmOutcome`; the
closure's contract keeps a caller's frame `F` indexed by the attempt (captured variables), given
back on every outcome; the commit's effect through the lent permission (`stmEff`; its token `P` back
with the committed attempt); a client of any cluster state and any context; the result after the
caller's `σ0`; no thread token (Perennial's fork needs none); no size bounds (the old
`stmKeyMax`/`stmCallMax`: a request too large is a refusal, an error, in W0's model).

Margin: the committed attempt's reads are also each one revision's (`readsSeen`); a failed
attempt's reads promise nothing (`issues/stm-serializable-snapshot.md`); the commit's reply's
contents (the write responses) are only given as owned.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.concurrency.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Concurrency

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- `NewSTM(c, apply, opts...)`: runs `apply` until an attempt commits: `nil`, the committed
attempt (satisfying the closure's `Rel`, the frame `F` at it) applied atomically from a state the
cluster reached to the next (`stmCommitted` at the options' level), and the commit's reply; or
`nil` and an error (the closure's, or a request's), the frame given back. The options' level must
be one of the four, their context (the client's if none) a context. -/
def NewSTM.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (dflt who : Principal) (apply : GoFunc) (F : Attempt → IProp GF)
    (Rel : Attempt → Prop) (sl : GoSlice) (gs : List (STMOpts → STMOpts))
    (T : State → State → Prop) (P : IProp GF) (σ0 : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isClient c γ dflt ∗ stmOptsAt sl gs ∗ ⌜isoValid (applySTMOptsM gs).iso⌝ ∗
      optCtxOk (applySTMOptsM gs).ctx dflt who ∗ applyOk apply γ who F Rel ∗ (∃ b, F b) ∗ etcdLent γ T P ∗ P ∗ etcdLb γ σ0 ∗
      ⌜effIn (stmEff (applySTMOptsM gs).iso Rel) T⌝ }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.NewSTM)) (Val #c)) (Val #apply)) (Val #sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); stmOptsAt sl gs ∗
      stmResult γ (applySTMOptsM gs).iso F Rel P σ0 resp err }}

end spec

end Concurrency
end EtcdGrove
end Perennial
