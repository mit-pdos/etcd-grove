/-
**The API's transaction, over the internal one** (M4, track B, 2026-11-06; `notes/mvcc-api-invariants.md`
§2, `mvccTxn`). Lean-first (no Rocq counterpart). `Api.lean` imports it non-publicly and defines its
sealed `mvccTxn` as `mvccTxnI`.

A transaction of the API is the internal transaction (`isTxnReadT`, `isTxnWriteT`) **without its
trace** (`Tr := True`: `KV.Read`/`Write` give the trace back to the caller, which lends it to `Range`
and `Put`), at the state it began at (`σ.log`, `σ.crev`; nothing pending, reachable), with the
reader token's way back (`storeReaderC s γ ={⊤}=∗ ownToks γ.api.rdk 1`: the readers' pool's loan,
whatever the pool is; `End` gives the reader back through it), as an interface value of one of three types:
* a read transaction is `*metricsTxnWrite` (`store.Read`'s), or `NewReadOnlyTxnWrite`'s
  `*txnReadWrite` around a read transaction, to any depth (`roWrap n t mw`: the wrappers' chain down
  to the internal transaction `mw`; `NewReadOnlyTxnWrite` takes any read transaction);
* a write transaction is at the store's current physical names `p`, with the certificate map's free
  entry (`certFree`, `End`'s `certOkNext`): a store without watchers' `*metricsTxnWrite`, or a
  watchable store's `*watchableStoreTxnWrite` around it (`wsWrap`: the wrapper and the sole writer's
  certificate, tokens and notified-log half, `isWatchTxnWriteT`'s rest, at the watchable store's
  names with the current physical names, `WsNames.withPhys`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.TxnSteps
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiState

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The reader token's way back, from the reader the transaction holds (the reader tokens,
2026-11-06; 2026-11-07: the token, the API's `mvccReaders γ 1`, is the right to a whole reader, its
lock slots and ticket, from the handle's pool `rdkPool`; no thread token). -/
def tokBack (s : Loc) (γ : StoreNames) : IProp GF :=
  iprop(storeReaderC s γ ={⊤}=∗ ownToks γ.api.rdk 1)

/-- **The read-only wrappers' chain**, `n` deep, from `t` down to the read transaction `mw`. -/
def roWrap : Nat → GoInterface → Loc → IProp GF
  | 0, t, mw => iprop(⌜t = interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw⌝)
  | n + 1, t, mw => iprop(∃ (trw : Loc) (ty : go.GoType) (v : val),
      ⌜t = interface.mkOk (go.GoType.PointerType txnReadWrite.ty) #trw⌝ ∗
      trw.[txnReadWrite, go!"TxnRead"] ↦ (interface.mkOk ty v : GoInterface) ∗
      roWrap n (interface.mkOk ty v) mw)

/-- **A watchable store's wrapper of the write transaction `mw`** (`isWatchTxnWriteT`'s rest; no
sole writer's tokens or notified-log half since 2026-11-06). -/
def wsWrap (tw sw s : Loc) (γw : WsNames) (mw : Loc) (ilog : Log) : IProp GF :=
  iprop(tw ↦□ ({ TxnWrite' := interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw,
                 s' := sw } : watchableStoreTxnWrite) ∗
    isWatchableStore sw s γw ∗ idxCert γw.st.idx ilog)

/-- **The write transaction's interface value**: `*metricsTxnWrite` of a store without watchers, or a
watchable store's wrapper (at the names `γ`, the current ones). -/
def wrWrap (t : GoInterface) (γ : StoreNames) (s mw : Loc) (ilog : Log) : IProp GF :=
  iprop(⌜t = interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw ∧ γ.watchQ = false⌝ ∨
    ∃ (tw sw : Loc) (γw : WsNames),
      ⌜t = interface.mkOk (go.GoType.PointerType watchableStoreTxnWrite.ty) #tw ∧ γw.st = γ⌝ ∗
      wsWrap tw sw s γw mw ilog)

/-- **The API's transaction** (see the header). -/
def mvccTxnI (t : GoInterface) (γ : StoreNames) (trace : Loc) (k : MTxn) : IProp GF :=
  match k with
  | .read σ => iprop(∃ (mw s : Loc) (n : Nat), ⌜MvccReachable σ⌝ ∗
      isTxnReadT mw s γ trace σ.log (W64 ((σ.log.length : Int) - 1)) σ.crev iprop(True) iprop(True) ∗
      tokBack s γ ∗ roWrap n t mw)
  | .write σ pend => iprop(∃ (mw s : Loc) (p : PhysNames) (puts deletes putSize : w64),
      ⌜σ.pending = none ∧ MvccReachable σ⌝ ∗
      isTxnWriteT mw s (γ.withPhys p) trace σ.log pend puts deletes putSize σ.crev iprop(True) false
        iprop(True) ∗
      tokBack s (γ.withPhys p) ∗ certFree (γ.withPhys p) ∗ wrWrap t (γ.withPhys p) s mw σ.log)

/-! ### The interface values' types -/

end defs

end api
end mvcc
end EtcdGrove
end Perennial
