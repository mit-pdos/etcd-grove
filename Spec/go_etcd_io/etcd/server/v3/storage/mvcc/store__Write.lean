/-
`store.Write` (kvstore_txn.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.WriteCtx
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.TxnSteps

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
(`spec_R`, `ReaderSpecs.lean`). 
The transaction's compaction revision is permitted (`crevPermAt`, C3's store law, 2026-11-02).
The writer's pin (`writerPin`, M2's item 37, 2026-11-02) goes into the transaction, which holds
the writer's half of the bucket's view; `End` gives it back at the new log.

**M4, track B, 2026-11-06** (request 4, `Api/WriteCtx.lean`): the hook by its state (`writeCtxM`:
set, its facts and triple; unset, `LockInsideApply`'s nil arm at the share `dq` of the hook at
`nil`, the caller's view shift from the batch lock's invariant and `Pre`), given back as
`lockBackM`; the names pinned by any share `qf` of the store's current objects (`curAt`: the API's
`mvccBackend` holds an eighth of `q`), given back, in place of the writer's fragment; the frozen
state excluded by the caller's `G` (`□ (slotF γ ∗ G -∗ False)`, given back: the API's backend share,
`slotF_share_excl`), in place of the placeholder `slotF_excl_M1`; and the begin's callback
(`writeCb`), run with the writer's slot at the committed log `ilog` and the transaction's compaction
revision `crev`, its `F ilog crev` returned; the transaction without its trace (`isTxnWriteT` at
`True`), the trace given back.

**Track A, request 3, 2026-11-06**: the revision token and the writer's pin are the caller's only for
a watchable store's sole writer (`wrIn`); a store without watchers' writer finds them after its
checkout, in the writer's state (`wrToks`, every token not spent) and the batch lock's resource
(`wrPin`), so concurrent writers need nothing of each other. The reader under a later (its first step strips
it: a pool's loan, `rdSupply`, is under one) and the backend's write token or its supply (a step's
receipt buys one: the API's `mvccBackend` holds the supply). -/
abbrev mvcc.store.Write.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (trace : Loc) (P Pre Q : IProp GF) (hk : Option val)
    (dq : DFrac) (te : Bool) (c : Int) (Z : IProp GF) (log : mvcc.Log) (qf : Qp)
    (o : mvcc.StoreObjs) (G : IProp GF) (F : mvcc.Log → Int → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ ▷ mvcc.storeReaderC s γ ∗ □ Z ∗ mvcc.crevLb γ.idx c ∗
      (mvcc.storeWT γ ∨ □ (⧗ 1 ={⊤}=∗ mvcc.storeWT γ)) ∗ ⌜trace ≠ null⌝ ∗
      mvcc.writeCtxM γ P hk Pre Q dq ∗ mvcc.curAt γ (DFrac.own qf) o ∗
      G ∗ □ (mvcc.slotF γ ∗ G -∗ False) ∗ mvcc.writeCb γ F ∗ mvcc.wrIn γ log ∗
      traceutil.ownTrace trace te }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Write")) (Val #trace))
  {{ (mw : Loc), RET #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw);
      (∃ (ilog : mvcc.Log) (crev : Int),
        mvcc.isTxnWriteT mw s γ trace ilog [] (W64 0) (W64 0) (W64 0) crev Z false iprop(True) ∗
        mvcc.crevLb γ.idx crev ∗
        mvcc.crevPermAt γ crev ∗
        ⌜c ≤ crev⌝ ∗ F ilog crev) ∗ traceutil.ownTrace trace te ∗ Q ∗ mvcc.lockBackM γ P hk dq ∗
      mvcc.curAt γ (DFrac.own qf) o ∗ G }}

end spec

end EtcdGrove
end Perennial
