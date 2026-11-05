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

/-- **etcd's backend of a real instance, as mvcc's storage** (strict M1, phase A of the API over its
storage abstraction, 2026-11-06): the server and the lessor chose etcd's backend, so their
statements name a real instance `d : KBReal` and mvcc's storage at it, `etcdStorage d` (shown `↑d`),
the backend's own names (`d.γB`, `d.P`, `d.be`, `d.gx`) for what they write directly. -/
instance : Coe mvcc.KBReal MvccStorage := ⟨etcdStorage⟩

attribute [coe] etcdStorage

/-! ## 0. The pure part -/

/-- The writer's view of the state: the state at `(log, crev)` with nothing pending. -/
def stAt (log : mvcc.Log) (c : Int) : MvccState := ⟨log, c, none⟩

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

/-- A read's update (`Read`, `Rev`, `FirstRev`, `Range`), committing to `Q σ`. -/
def auRead (γ : MvccName) (Q : MvccState → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
    <{ mvccState γ σ, COMM Q σ }>)

/-- `Txn.End`'s two nested updates of a write transaction begun at `σ₀` with `pend`, to `Y`; the
notify step gives the receipt of the history it makes (round 16). -/
def auEnd (γ : MvccName) (σ₀ : MvccState) (pend : List mvcc.Change) (Y : IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
    <{ ⌜σ = σ₀⌝ ∗ mvccState γ (σ.notify pend) ∗ ⧖ (mvcc.logCh (σ.log ++ [pend])), COMM
        AU <{ ∃∃ (σ' : MvccState), mvccState γ σ' }> @ ⊤ \ ↑mvccN, ∅
          <{ ⌜σ' = σ₀.notify pend⌝ ∗ mvccState γ σ'.commitPending, COMM Y }> }>)

/-- **`mvccImage_snapshot.law`'s update**: at a state with nothing pending, left unchanged,
committing to `Φ σ`. Its atomic precondition says so, so a reader's update (`auRead`) does not give
it by monotonicity: the builder shows `pending = none` from the writer's half, at every access.
(M1, 2026-11-05: the draft's `σ.crev = -1` dropped with the law's, the backend's `Snapshot` axiom
strengthened; the draft's header.) -/
def auSnap (γ : MvccName) (Φ : MvccState → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (σ : MvccState), mvccState γ σ ∗ ⌜σ.pending = none⌝ }>
    @ ⊤ \ ↑mvccN, ∅ <{ mvccState γ σ, COMM Φ σ }>)

/-- `Compact(rev)`'s update. -/
def auCompact (γ : MvccName) (rev : w64) (Q : MvccState → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
    <{ mvccState γ (if σ.crev < sint.Z rev ∧ sint.Z rev ≤ (σ.rev : Int)
          then σ.compactTo (sint.Z rev) else σ), COMM Q σ }>)

/-- `Restore`'s update to `σ'`, which gives the restored history's receipt (round 16). -/
def auRestore (γ : MvccName) (σ' : MvccState) (Q : MvccState → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (σ : MvccState), mvccState γ σ ∗ ⌜σ.log <+: σ'.log ∧ σ.crev ≤ σ'.crev⌝ }>
      @ ⊤ \ ↑mvccN, ∅ <{ mvccState γ σ' ∗ ⧖ (mvcc.logCh σ'.log), COMM Q σ }>)

/-- **The critical-section contract** over the API's `hookRun` (one definition: txn's `csA` is it;
the cross-review's §8: to live beside `hookRun` in the API). -/
def csContractA (P : IProp GF) (f : GoFunc) (Pre Q Post : IProp GF) : IProp GF :=
  iprop(Pre ∗ mvcc.api.hookRun P f Pre Q ∗ (Q ={⊤}=∗ P ∗ Post))

end defs

end srvApi
end EtcdGrove
end Perennial
