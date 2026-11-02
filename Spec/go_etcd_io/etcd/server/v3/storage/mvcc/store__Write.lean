/-
`store.Write` (kvstore_txn.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.Write(trace)` opens a write transaction at the committed log, for one revision token:
`s.mu` held shared and the batch transaction locked (the writer's resources) until `End`.
`LockInsideApply` runs the store's post-lock hook `f` under the lock (invariant `P`, `hookIs`)
on the caller's `Pre`, by the caller's triple: its `Q` is the caller's. A write token of the
backend (`storeWT`: the real backend's write-back budget, which the transaction's `Unlock` spends;
nothing for mvcc's assumed backend; 2026-10-13, unit 5) is spent too.

**The compaction revision** (2026-10-13, unit 6a): the transaction holds `s.mu` at the
compaction revision `crev` (fixed until `End`), at or above the caller's lower bound `c`, a
revision of the committed log (or `-1`); its reads answer `rangeOutcomeC` at it. The reader's tag
`Z` is carried to `End`. The caller's hook (`hookIs`, with the writer's fragment: the caller's
names are the store's current ones; D22 receiver epochs, S5b) is given back. The readers' statement (`storeReader`, `crev = -1`) is `specR`
(`spec_R`, `ReaderSpecs.lean`). -/
abbrev mvcc.store.Write.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (trace : Loc) (P Pre Q : IProp GF) (f : val) (te : Bool)
    (c : Int) (Z : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.storeReaderC s γ ∗ □ Z ∗ mvcc.crevLb γ.idx c ∗ mvcc.revToken γ ∗
      mvcc.storeWT γ ∗ ⌜trace ≠ null⌝ ∗
      mvcc.hookIs γ P f ∗ Pre ∗ □ ({{ P ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) ∗
      traceutil.ownTrace trace te }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Write")) (Val #trace))
  {{ (mw : Loc), RET #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw);
      (∃ (ilog : mvcc.Log) (crev : Int),
        mvcc.isTxnWrite mw s γ trace ilog [] (W64 0) (W64 0) (W64 0) crev Z ∗ mvcc.crevLb γ.idx crev ∗
        ⌜c ≤ crev⌝) ∗ Q ∗ mvcc.hookIs γ P f }}

/-- **Candidate** (round 8, 2026-11-02, `notes/mvcc-api-candidate.md`; over `Api.lean`, not proved). `s.Write(trace)` opens a write transaction, the store's writer until its `End`: at the
store's state `σ`, which nothing else changes before then (`mvccTxn_write_agree`), no pending
change. Under the batch lock (invariant `P`), the post-lock hook `f` runs on the caller's `Pre`
(`hookRun`: `f`'s triple, or with no hook the caller's update), giving `Q`; `End` takes `P` back.
The caller's thread token is the transaction's until its `End`. On a store with watchers, the transaction's own `End` needs
the watchers notified (`mvccWatchersOk`), which only the watchable store's `End` provides: a
client of a watched store commits through `watchableStore.Write`. -/
abbrev mvcc.store.Write.specC : Prop :=
  ∀ (s : Loc) (γ : mvcc.MvccName) (trace : Loc) (te : Bool) (P Pre Q : IProp GF) (f : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isMvcc s γ ∗ threadTok ∗ ⌜trace ≠ null⌝ ∗ traceutil.ownTrace trace te ∗ mvcc.mvccHook γ P f ∗ Pre ∗ mvcc.hookRun P f Pre Q }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Write")) (Val #trace))
  {{ (mw : Loc), RET #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw);
      (∃ σ : mvcc.MvccState, mvcc.mvccTxn (interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw) γ trace (.write σ [])) ∗ Q }}

end spec

end EtcdGrove
end Perennial
