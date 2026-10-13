/-
What the txn package's functions are given (Lean-first): the store as an `mvcc.KV`
(`isKV`) and the lessor with its `Lookup` (`isTxnLessor`). The sole-writer premise
(`soleWriter`) is `SoleWriter.lean`'s.

**`isKV kv s γ`**: the `mvcc.KV` interface value `kv` is the store `*store` at `s`
(`mvcc.isStore`, persistent); its `Read`/`Write` are mvcc's verified `store.Read`/`store.Write`.

**`isTxnLessor le γl`**: mvcc's `isLessor` (what the store calls: `GetLease`, `Attach`,
`Detach`, `SetRangeDeleter`) and `Lookup(id)`, which `checkLease` calls: it returns `nil` or a
lease that the lessor granted (`mvcc.leaseKnown γl id`, which mvcc's `Put` of a key with that
lease needs). Additive: mvcc's `isLessor` is unchanged. The lessor is the trust boundary
(`lease` is names-only); leases have no liveness here, so a lease found may expire later (its
keys' deletion is a write of the lessor's range deleter, outside this model's sole writer).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Requests
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace txn

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- The `mvcc.KV` `kv` is the store at `s` (with ghost names `γ`), over either backend instance
(`γ.kb`: mvcc's assumed contract, or the real backend; 2026-10-13, unit 6: it carried
`γ.kb = none` before). A write transaction spends a write token (`mvcc.storeWT γ`: the real
backend's write-back budget) and changes fewer than `mvcc.putMax γ` keys (`2 ^ 56` for the real
backend). -/
def isKV (kv : GoInterface) (s : Loc) (γ : mvcc.StoreNames) : IProp GF :=
  iprop(⌜kv = interface.mkOk (go.GoType.PointerType store.ty) #s⌝ ∗ mvcc.isStore s γ)

/-- Over mvcc's assumed backend a write token is free. -/
theorem storeWT_none (γ : mvcc.StoreNames) (h : γ.kb = none) : ⊢ mvcc.storeWT (GF := GF) γ := by
  unfold mvcc.storeWT mvcc.kbWT; rw [h]; iintro; itrivial

/-- Over mvcc's assumed backend a transaction's changes are bounded by `2 ^ 63` only. -/
theorem putMax_none (γ : mvcc.StoreNames) (h : γ.kb = none) : mvcc.putMax γ = 2 ^ 63 := by
  unfold mvcc.putMax mvcc.kbPutMax; rw [h]

/-- Either instance allows `2 ^ 56` changes per transaction. -/
theorem putMax_ge (γ : mvcc.StoreNames) : 2 ^ 56 ≤ mvcc.putMax γ := by
  unfold mvcc.putMax mvcc.kbPutMax; cases γ.kb <;> simp

/-- **A supply of `n` write tokens** of the store `γ` (`mvcc.storeWT γ` each): free over mvcc's
assumed backend; `n` of the real backend's write-back tokens (`backend.wbTok`, an `ownToks` of
its `wb` budget), which its creator hands out. -/
def storeWTs (γ : mvcc.StoreNames) (n : Nat) : IProp GF :=
  match γ.kb with
  | none => iprop(True)
  | some d => ownToks d.γB.wb n

instance storeWTs_timeless (γ : mvcc.StoreNames) (n : Nat) :
    Timeless (storeWTs (GF := GF) γ n) := by
  unfold storeWTs; split <;> infer_instance

/-- One write token off a supply. -/
theorem storeWTs_split (γ : mvcc.StoreNames) (n : Nat) :
    storeWTs (GF := GF) γ (n + 1) ⊢ mvcc.storeWT γ ∗ storeWTs γ n := by
  unfold storeWTs mvcc.storeWT mvcc.kbWT
  cases γ.kb with
  | none => iintro -; isplitl <;> itrivial
  | some d =>
    simp only [backend.wbTok]
    rw [Nat.add_comm]
    exact ownToks_add_1 n 1 d.γB.wb

instance isKV_persistent (kv : GoInterface) (s : Loc) (γ : mvcc.StoreNames) :
    Persistent (isKV (GF := GF) kv s γ) := by
  unfold isKV; infer_instance

/-- The `lease.Lessor` `le` as the txn package uses it: mvcc's contract, and `Lookup(id)`
returns `nil` or a lease the lessor granted. -/
def isTxnLessor (le : GoInterface) (γl : GName) : IProp GF :=
  iprop(mvcc.isLessor le γl ∗ ∃ li : GoInterfaceOk, ⌜le = GoInterface.ok li⌝ ∗
    □ (∀ id : w64,
      {{ True }} (App (Val #(methods li.ty go!"Lookup" li.v)) (Val #id))
      {{ (l : Loc), RET #l; ⌜l = null⌝ ∨ mvcc.leaseKnown γl id }}))

instance isTxnLessor_persistent (le : GoInterface) (γl : GName) :
    Persistent (isTxnLessor (GF := GF) le γl) := by
  unfold isTxnLessor; infer_instance

end defs

end txn
end EtcdGrove
end Perennial
