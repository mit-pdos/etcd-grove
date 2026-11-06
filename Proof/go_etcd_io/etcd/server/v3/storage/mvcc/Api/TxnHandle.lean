/-
**The API's transaction, over the internal one** (M4, track B, 2026-11-06; `notes/mvcc-api-invariants.md`
§2, `mvccTxn`). Lean-first (no Rocq counterpart). `Api.lean` imports it non-publicly and defines its
sealed `mvccTxn` as `mvccTxnI`.

A transaction of the API is the internal transaction (`isTxnReadT`, `isTxnWriteT`) **without its
trace** (`Tr := True`: `KV.Read`/`Write` give the trace back to the caller, which lends it to `Range`
and `Put`), at the state it began at (`σ.log`, `σ.crev`; nothing pending, reachable), with the
thread token's way back (`storeReaderC s γ ={⊤}=∗ threadTok`: the readers' pool's loan, whatever the
pool is; `End` gives the reader back through it). A write transaction (of a store without watchers,
`*metricsTxnWrite`) at the store's current physical names `p`, with the certificate map's free entry
(`certFree`, `End`'s `certOkNext`). The watchable store's write transaction (`*watchableStoreTxnWrite`)
and the read-only wrapper (`*txnReadWrite`) are not yet covered (`False`): the hand-off, "track B".
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.TxnSteps
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

/-- The thread token's way back, from the reader the transaction holds. -/
def tokBack (s : Loc) (γ : StoreNames) : IProp GF := iprop(storeReaderC s γ ={⊤}=∗ threadTok)

/-- **The API's transaction** (see the header). -/
def mvccTxnI (t : GoInterface) (γ : StoreNames) (trace : Loc) (k : MTxn) : IProp GF :=
  match k with
  | .read σ => iprop(∃ (mw s : Loc),
      ⌜t = interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw ∧ MvccReachable σ⌝ ∗
      isTxnReadT mw s γ trace σ.log (W64 ((σ.log.length : Int) - 1)) σ.crev iprop(True) iprop(True) ∗
      tokBack s γ)
  | .write σ pend => iprop(∃ (mw s : Loc) (p : PhysNames) (puts deletes putSize : w64),
      ⌜t = interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw ∧ γ.watchQ = false ∧
        σ.pending = none ∧ MvccReachable σ⌝ ∗
      isTxnWriteT mw s (γ.withPhys p) trace σ.log pend puts deletes putSize σ.crev iprop(True) false
        iprop(True) ∗
      tokBack s (γ.withPhys p) ∗ certFree (γ.withPhys p))

end defs

end api
end mvcc
end EtcdGrove
end Perennial
