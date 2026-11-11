/- Lean-first (no Rocq counterpart).

`x.checkStoreRange(m, lo, clo, q, res, err)` (`examples/mvccfull/mvccfull.go`): returns when the
store's own `Range` of `q` (its own read transaction) gave `(res, err)`, with the floors `lo` and
`clo` loaded from `m.revLo`/`m.cmpLo` before the call.

**The triple.** The caller holds what `KV.Range.contract` gives at the reader's update
(`reader_au`): the state `σ` the read was at, what the read learned of it (`readQ`: the monotone
counters' lower bounds at `σ`'s, the history's lower bound covering it, `σ` reachable), the outcome
`rangeOutcomeC res err σ.log σ.rev σ.crev …` (not the context's: `res ≠ null`), the log's well
formedness; and the floors below `σ`'s revision and compaction revision (`lo ≤ σ.rev`,
`clo ≤ σ.crev`). It holds the member's incarnation live (`incLive`: to load `m.revHi`/`m.cmpHi` in
its invariant; `revHi_acc`, `cmpHi_acc`), a reader slot of the history, the run's keys and history,
and the request's key and end (at any fractions). Then every check passes:

- `ErrCompacted`: the revision read is `q.ro.Rev` (a read at the current revision is never below
  the compaction revision, `σ.crev ≤ σ.rev`), positive and below `σ.crev ≤ m.cmpHi`;
- otherwise the result is not `nil`, its revision `σ.rev` is in `[lo, m.revHi]`, and
  `checkRangeAt` at `(σ.rev, clo)` passes: the outcome at `σ.crev`'s live case is the one at
  `clo ≤ σ.crev` (`rangeOutcomeC_lower`), and the snapshot taken has the store's states up to
  `σ.rev` (`hist_match`). Checking at the floor `clo` does not weaken the check: the store did not
  return `ErrCompacted`, so the revision read is not below `σ.crev ≥ clo`.

Everything is given back but the result. Callers: `readOne` (the store's `Range`) and the watch
receiver (`stream.receive`, the watch server's previous key-value read).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Readers

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- See the file header. -/
abbrev runner.checkStoreRange.spec : Prop :=
  ∀ (x : Loc) (ks : List GoString) (h : Loc) (γh : HistNames) (i : Nat) (mp : Loc)
    (m : MemberNames) (ι : IncNames) (kv : GoInterface) (qr : Qp) (lo clo : w64) (q : rangeReq)
    (kk e : GoString) (dk de : DFrac) (res : Loc) (err : GoInterface) (σ : MvccState),
  sint.Z lo ≤ σ.rev → sint.Z clo ≤ σ.crev →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      runnerKeys x ks ∗ runnerH x h ∗ histRd h γh ∗ incLive ks γh i mp m ι kv qr ∗
      q.key' ↦*{dk} kk ∗ q.end' ↦*{de} e ∗ readQ ks γh m σ ∗ ⌜res ≠ null⌝ ∗
      rangeOutcomeC res err σ.log (W64 (σ.rev : Int)) σ.crev (decide (q.end' = slice.nil)) kk e
        q.ro' ∗
      ⌜LogWf' σ.log ∧ ∀ cs ∈ σ.log, cs.length < 2 ^ 63⌝ }}
    (App (App (App (App (App (App (x @!! go.GoType.PointerType runner.ty @!! go!"checkStoreRange")
      (Val #mp)) (Val #lo)) (Val #clo)) (Val #q)) (Val #res)) (Val #err))
  {{ RET #(); histRd h γh ∗ incLive ks γh i mp m ι kv qr ∗ q.key' ↦*{dk} kk ∗ q.end' ↦*{de} e }}

end spec

end mvccfull
end EtcdGrove
end Perennial
