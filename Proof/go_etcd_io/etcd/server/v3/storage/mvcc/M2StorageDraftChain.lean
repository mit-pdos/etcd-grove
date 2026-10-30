/-
**M2, the storage side: the compaction chain's critical section by the hook's state (Draft)**
(`notes/m2-storage-plan.md`, "The switch of the approved items": item 17 switched 2026-10-30, with
the lease; what stays here is item 31's part of it). Imported by nothing; no `axiom`, no `sorry`.

Switched (2026-10-30): `compactJobPre` (with the jobs' leased share `storeStopR`), `compactRightR`,
`store.Compact.spec` (items 4 and 17), the internal `updateCompactRev.spec`/`compactLockfree.spec`
at the hook set (`hookIs ∗ csContract`, `lockCtxM`'s `some f` arm), the export
`mvcc_NewStore_backend_cmp` (item 24): `InvCompact.lean`, the specs, `Results.lean`.

**Switched with item 31 (2026-10-30, "The restore chain, mvcc part"):** `SetScheduledCompact.spec`
by the hook's state (`lockArmS`: the hook-set arm as before, the nil-hook arm over `lockNilSpec`,
`LockArm.lean`), proved. **Still a Draft**: the critical section's context by the hook's state at the
store (`lockCtxM`, `lockBackM`) and `updateCompactRev.specR`/`compactLockfree.specR` over it, for
`restore()`'s resumed compaction inside `Restore` (the new backend's hook unset), with `kbHookNil`/
`bt_lockInNil` in `M2StorageDraftRestore.lean`. Their `none` arm calls `SetScheduledCompact` at
`hk = none`, which takes `lockNilSpec` for the store's batch transaction: the store gets it only
from its backend contract, `batchTxSpecG`'s new clause `lockNilSpec bt RT WT W P (kbHookNil kb)
Locked`, which the backend bridge proves (`isKeyBackendG_of_backendC`, `BackendBridge.lean`: one
step, `bt_lockInNil`, proved). The bridge is the backend side's (branch `m2-backend`), so the clause,
and the chain's switch over it, wait for it. Its only consumer is the waiting `store.Restore` in
compaction mode (item 15).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Link
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.StoreBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Link
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.M2StorageDraftRestore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section draft
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The critical section's context, by the hook's state** (draft, A2): the hook set to `f`
(today's: the writer's hook and the caller's contract for it), or unset (`none`: the batch lock's
invariant `P` named, the writer's fragment, the new backend's unset hook lent, and the caller's
update from `Pre` to `Post`, `LockInsideApply` running nothing: `lockNilSpec`). -/
def mvcc.lockCtxM (γ : mvcc.StoreNames) (P : IProp GF) (hk : Option val) (Pre Q Post : IProp GF) :
    IProp GF :=
  match hk with
  | some f => iprop(mvcc.hookIs γ P f ∗ mvcc.csContract P f Pre Q Post)
  | none => iprop(mvcc.hookP γ P ∗ mvcc.writerFrag γ ∗ mvcc.kbHookNil γ.kb ∗ Pre ∗ (Pre ={⊤}=∗ Post))

/-- What the call gives back of the context (with `Post` or `Pre` beside it). -/
def mvcc.lockBackM (γ : mvcc.StoreNames) (P : IProp GF) (hk : Option val) : IProp GF :=
  match hk with
  | some f => mvcc.hookIs γ P f
  | none => iprop(mvcc.hookP γ P ∗ mvcc.writerFrag γ ∗ mvcc.kbHookNil γ.kb)

/-- **Draft of `store.updateCompactRev.spec`, step 2**: `updateCompactRev.specD` with the restorable
right, the job premise `compactJobPre`, and the critical section's context by the hook's state
(`lockCtxM`: `restore()`'s resumed call has it unset). -/
abbrev mvcc.store.updateCompactRev.specR : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (rev : w64) (c : Int) (P : IProp GF) (hk : Option val)
    (Pre Q Post : IProp GF) (log : mvcc.Log),
  mvcc.storeCmp γ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.muInvAt s γ 1 c ∗ mvcc.compactRightR s γ c ∗
      mvcc.idxCert γ.idx log ∗ ⌜sint.Z rev < log.length ∧ mvcc.NoDelPutAt log (sint.Z rev)⌝ ∗
      mvcc.lockCtxM γ P hk Pre Q Post ∗ mvcc.storeRT γ ∗ mvcc.kbWTSupplyM γ.kb }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"updateCompactRev")) (Val #rev))
  {{ (ch : GoChan) (prev : w64) (err : GoInterface), RET (PairV (PairV #ch #prev) #err);
      mvcc.storeRT γ ∗ mvcc.lockBackM γ P hk ∗
      ((⌜err = GoInterface.nil ∧ ch = chan.nil ∧ prev = W64 c ∧ c < sint.Z rev⌝ ∗
        mvcc.muInvAt s γ 1 (sint.Z rev) ∗ mvcc.compactRightR s γ (sint.Z rev) ∗ Post ∗
        mvcc.compactJobPre s γ rev) ∨
      (⌜sint.Z rev ≤ c ∧ prev = W64 0⌝ ∗
        (∃ ec : GoInterfaceOk, globalAddr ErrCompacted ↦□ GoInterface.ok ec ∗ ⌜err = GoInterface.ok ec⌝) ∗
        mvcc.muInvAt s γ 1 c ∗ mvcc.compactRightR s γ c ∗ Pre ∗ mvcc.compactChan ch iprop(True)) ∨
      (⌜c < sint.Z rev ∧ ch = chan.nil ∧ prev = W64 0⌝ ∗
        (∃ ef : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok ef ∗ ⌜err = GoInterface.ok ef⌝) ∗
        (∃ log : mvcc.Log, mvcc.idxCert γ.idx log ∗ ⌜(log.length : Int) ≤ sint.Z rev⌝) ∗
        mvcc.muInvAt s γ 1 c ∗ mvcc.compactRightR s γ c ∗ Pre)) }}

/-- **Draft of `store.compactLockfree.spec`, step 2**: `compactLockfree.specD` likewise (what
`restore()` calls for the compaction it resumes: `resumeK`, at `hk = none`). -/
abbrev mvcc.store.compactLockfree.specR : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (rev : w64) (c : Int) (P : IProp GF) (hk : Option val)
    (Pre Q Post : IProp GF) (log : mvcc.Log),
  mvcc.storeCmp γ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.muInvAt s γ 1 c ∗ mvcc.compactRightR s γ c ∗
      mvcc.idxCert γ.idx log ∗ ⌜sint.Z rev < log.length ∧ mvcc.NoDelPutAt log (sint.Z rev)⌝ ∗
      mvcc.lockCtxM γ P hk Pre Q Post ∗ mvcc.storeRT γ ∗ mvcc.kbWTSupplyM γ.kb }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"compactLockfree")) (Val #rev))
  {{ (ch : GoChan) (err : GoInterface), RET (PairV #ch #err); mvcc.storeRT γ ∗ mvcc.lockBackM γ P hk ∗
      ((⌜err = GoInterface.nil ∧ c < sint.Z rev⌝ ∗ mvcc.muInvAt s γ 1 (sint.Z rev) ∗
        mvcc.compactRightR s γ (sint.Z rev) ∗ mvcc.crevLb γ.idx (sint.Z rev) ∗ Post ∗
        mvcc.compactChan ch (mvcc.compactDone s γ (sint.Z rev))) ∨
      (⌜sint.Z rev ≤ c⌝ ∗
        (∃ ec : GoInterfaceOk, globalAddr ErrCompacted ↦□ GoInterface.ok ec ∗ ⌜err = GoInterface.ok ec⌝) ∗
        mvcc.muInvAt s γ 1 c ∗ mvcc.compactRightR s γ c ∗ Pre ∗ mvcc.compactChan ch iprop(True)) ∨
      (⌜c < sint.Z rev ∧ ch = chan.nil⌝ ∗
        (∃ ef : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok ef ∗ ⌜err = GoInterface.ok ef⌝) ∗
        mvcc.muInvAt s γ 1 c ∗ mvcc.compactRightR s γ c ∗ Pre)) }}

end draft

end EtcdGrove
end Perennial
