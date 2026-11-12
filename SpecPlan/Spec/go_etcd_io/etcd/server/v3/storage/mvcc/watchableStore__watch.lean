/-
`(*watchableStore).watch(key, end, startRev, id, ch, fcs...)` (internal; `watchStream.Watch`'s
callee, under `ws.mu`): a watcher record added to the synced group (a start revision `0` or past
the current one: `minRev` the next revision, or the start) or the unsynced one, under `s.mu` and
`revMu`'s read side (the reader token); the cancel closure.

**Proof sketch.** Under `s.mu` (`wsMu`) and `revMu.RLock` (3e's: the current revision `R`, nothing
pending; the caller's read update fired at the state `σ` read, `σ.rev = R`): the record (`wRecAt`), `synced.add` or `unsynced.add`
(`watcherGroup.add`); the registration in the stream's ghost map (`wsIdFree` spent: `wsReg` with the
stamp of the channel's sends so far, `wsSentLb`). The closure's triple is `cancelWatcher`'s.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.WatchInternal
public import SpecPlan.Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire go_etcd_io.etcd.server.v3.storage.mvcc Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

def watchableStore.watch.spec : Prop :=
  ∀ (s : Loc) (γ : MvccName) (ι : WsNames) (key endk fcs : GoSlice) (k e : GoString)
    (ds : List (EvM → Bool)) (startRev id : w64) (Q : MvccState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wsInv s γ ∗ wsIdFree ι id ∗ key ↦*□ k ∗ endk ↦*□ e ∗ filtersAt fcs ds ∗
      ⌜0 ≤ sint.Z startRev⌝ ∗ mvccReaders γ 1 ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅ <{ mvccState γ σ, COMM Q σ }> }}
    (App (App (App (App (App (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"watch")) (Val #key)) (Val #endk))
      (Val #startRev)) (Val #id)) (Val #(wsChanOf ι))) (Val #fcs))
  {{ (wa : Loc) (c : GoFunc), RET (PairV #wa #c); mvccReaders γ 1 ∗
      ∃ (W : WatcherM) (σ : MvccState), Q σ ∗ watcherAt wa ι id W ∗ wsReg ι id W ∗
        wsSentLb ι W.stamp ∗ mvccLb γ σ.kv ∗
        ⌜σ.pending = [] ∧ W.range = { key := k, endNil := decide (endk = slice.nil), rangeEnd := e } ∧
          W.drops = ds ∧ W.startRev = sint.Z startRev ∧
          W.pos = (if startRev = W64 0 then σ.rev else (sint.Z startRev).toNat - 1)⌝ ∗
        □ {{ True }} (App (Val #c) (Val #())) {{ RET #(); ∃ n : Nat, wsCanceled ι id n }} }}

end spec

end Mvcc
end EtcdGrove
end Perennial
