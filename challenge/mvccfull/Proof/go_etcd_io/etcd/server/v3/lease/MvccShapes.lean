/-
**The update shapes the server and the lessor hand to mvcc's API, and the critical-section
contract** (strict M1, 2026-11-05; the frozen draft `notes/mvcc-api-clients/ServerSpecs.lean`, §1
and §4's `csContractA`, landed as drafted, namespace `srvApi`): `Write`'s begin (`auBegin`), a
read's (`auRead`), `Txn.End`'s two nested updates (`auEnd`), the snapshot's (`auSnap`), `Compact`'s
(`auCompact`) and `Restore`'s (`auRestore`), and the critical-section contract over the API's
`hookRun` (`csContractA`; txn's `csA` is it). Here, below the lessor, because `lessor.Revoke`'s spec
takes `auBegin`/`auEnd` and `csContractA`; the server's store invariant and builders are
`etcdserver/KVStoreApi.lean`. (M1: `auSnap` without the draft's `σ.crev = -1`, as the API's
`mvccImage_snapshot.law`.)
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.EtcdBackend

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section
namespace Perennial
namespace EtcdGrove
namespace srvApi
open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc mvcc.api

attribute [coe] etcdStorage

/-! ## 0. The pure part -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-! ## 1. The atomic updates the server hands to mvcc, by shape (round 16: with the receipts) -/

/-- `Write`'s begin update (and `mvccDeleter`'s), committing to `X` at the state `σ₀`. -/
def auBegin (γ : MvccName) (σ₀ : MvccState) (X : IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
    <{ ⌜σ.pending = none⌝ ∗ mvccState γ σ, COMM ⌜σ = σ₀⌝ ∗ X }>)

/-- `Txn.End`'s two nested updates of a write transaction begun at `σ₀` with `pend`, to `Y`; the
notify step gives the receipt of the history it makes (round 16). -/
def auEnd (γ : MvccName) (σ₀ : MvccState) (pend : List mvcc.Change) (Y : IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
    <{ ⌜σ = σ₀⌝ ∗ mvccState γ (σ.notify pend) ∗ ⧖ (mvcc.logCh (σ.log ++ [pend])), COMM
        AU <{ ∃∃ (σ' : MvccState), mvccState γ σ' }> @ ⊤ \ ↑mvccN, ∅
          <{ ⌜σ' = σ₀.notify pend⌝ ∗ mvccState γ σ'.commitPending, COMM Y }> }>)

/-- **The critical-section contract** over the API's `hookRun` (one definition: txn's `csA` is it;
the cross-review's §8: to live beside `hookRun` in the API). -/
def csContractA (P : IProp GF) (f : GoFunc) (Pre Q Post : IProp GF) : IProp GF :=
  iprop(Pre ∗ mvcc.api.hookRun P f Pre Q ∗ (Q ={⊤}=∗ P ∗ Post))

end defs

end srvApi
end EtcdGrove
end Perennial
