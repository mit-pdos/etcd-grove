/-
What the apply thread holds for `watchableStore.Restore` (D22 receiver epochs, S6): the sanity
check that its precondition's store half is assemblable from the apply thread's resources after S5
(`apply.kvOwn`) and the server's kept closer (`srvKVCloser`); the new backend's half is S7/S8's
(the docstring of `restorePre_of_apply`). Not used yet: `applySnapshot` (S8) calls `kv.Restore`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvWatchBuilt

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`watchableStore.Restore`'s store half, from the apply thread** (D22 receiver epochs, S6): the
apply thread's KV resources at the applied log `log` (`apply.kvOwn`: the sole writer, its half of
the watchable store's notified log, the writer's fragment, its retired backend token, the reader
slots whose `crevFrozen` says the store is never compacted) and the server's kept closer
(`srvKVCloser`: the inner store's `storeCloser`) give, at the watchable store `ws` of the writer's
notified log, everything of `watchableStore.Restore.spec`'s precondition but the new backend's and
the restored log's; the reader slots, the leases and the auth store's reader resource are kept, and
the watchable store's own closer's other parts (its stop channel's close, its wait group), given
back for the closer at the new names (S8d, 2026-10-26).

**What S7/S8 must supply besides** (the snapshot path, `applySnapshot`): `⌜∃ d, E.γ.kb = some d⌝`
(the server's store is over the real backend); the restored log `[[], []] ++ R` extending `log`
(`applySnapshot` panics on a snapshot not newer; the image is of a longer prefix of the same raft
log: `kvRaftOf_prefix`) with `restoreLogOk R` (the KV model's revisions are non-empty, well formed,
lease-free under the workload); its certificate `certOk E.γ ([[], []] ++ R)` (the server's `cok`
map element of the image's log); and the new backend's: `storeBackendT b' E.s (E.γ.withPhys p) P'`
for every physical names of its bucket and instance (`storeBackendT_of_backend` of
`OpenSnapshotBackend`'s `isBackend` with the late-bound `lateW gx'`), its full view of the `Key`
bucket at the image's log (`keyImage`), `kbNoCmp` (`OpenBackend`'s post with `keyImage_noCmp`),
`kbRegRight` (the creator's half of `gx'`), `nReaders` reader tokens (`newPost`'s `rdTok`s with
`bOpen` shares). And back from it: the new closer (`srvKVCloser` re-made with the watchable store's
own parts), the writer's fragment at the new names (`txn.kvWriter` at `E.γ.withPhys p'` with the
watchable store's names' `st` replaced: `isWatchableStore` reads only its logical names), the new
`writerOwn`, the old backend's `k + 1` tokens (with the storage-version monitor's, S7, every `bOpen`
share of the old backend for `oldbe.Close`), the new backend's left over (the monitor's). -/
theorem etcdserver.restorePre_of_apply (s : Loc) (E : apply.AEnv GF) (log : mvcc.Log)
    (hwq : E.γ.watchQ = true) :
    apply.kvOwn E log ∗ srvKVCloser s E ⊢
      ∃ (ws : Loc) (γw : mvcc.WsNames), ⌜γw.st = E.γ⌝ ∗ mvcc.isWatchableStore ws E.s γw ∗
        mvcc.storeCloser E.s γw.st ∗ mvcc.writerFrag γw.st ∗ mvcc.writerOwn γw.st ∗
        mvcc.crevFrozen γw.st ∗ mvcc.watchWriter γw log ∗
        (mvcc.storeReader E.s E.γ ∗ apply.leasesLive E.γ (mvcc.stateAfter log) ∗ E.RD) ∗
        (∃ (wsl stc : Loc), srvKVAddr s ↦□ (interface.mkOk (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl : GoInterface) ∗
          structFieldRef go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore go!"stopc" wsl ↦□ stc ∗ mvcc.stopCloser stc ∗ mvcc.wsWaiter wsl) := by
  iintro ⟨Hown, Hcl⟩
  iunfold apply.kvOwn at Hown
  icases Hown with ⟨Hrd, Hkw, Hll, HRD, Hwo⟩
  iunfold txn.kvWriter at Hkw
  icases Hkw with ⟨Hsw, Hwl, Hfrag⟩
  iunfold txn.wlogOwn at Hwl
  rw [hwq]
  simp only [↓reduceIte]
  icases Hwl with ⟨%ws, %γw, %hγw, #Hws, Hwl, -⟩
  iunfold srvKVCloser at Hcl
  icases Hcl with ⟨%wsl, #Hkvf, Hcl⟩
  iunfold mvcc.wsCloser at Hcl
  icases Hcl with ⟨%stc, #Hstc, Hstcl, Hwsw, Hcl⟩
  ihave #Hfrz : mvcc.crevFrozen E.γ $$ [Hrd]
  · iunfold mvcc.storeReader at Hrd; iNamed Hrd; iexact Hfrz
  iexists ws, γw
  iunfold mvcc.watchWriter
  rw [hγw]
  ihave Hcp : iprop(∃ (wsl stc : Loc), srvKVAddr s ↦□ (interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl : GoInterface) ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore go!"stopc" wsl ↦□ stc ∗
      mvcc.stopCloser stc ∗ mvcc.wsWaiter wsl) $$ [Hstcl Hwsw]
  · iexists wsl, stc
    iframe Hkvf Hstc Hstcl Hwsw
  iframe Hws Hcl Hfrag Hwo Hfrz Hrd Hll HRD Hcp
  isplitr
  · ipureintro; rfl
  iunfold txn.soleWriter at Hsw
  icases Hsw with ⟨#Hc, Htoks, -⟩
  simp only [txn.soleBudget, mvcc.wBudget]
  iframe Hc Htoks Hwl

/-- **A watchable store reads only its inner store's logical names** (D22 receiver epochs, S6):
after a restore, the watchable store's names with the inner store's at the new physical ones
are the same watchable store (what S8's `txn.wlogOwn` at the new names takes). -/
theorem mvcc.isWatchableStore_withPhys [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    (s st : Loc) (γ : mvcc.WsNames) (p : mvcc.PhysNames) :
    mvcc.isWatchableStore (GF := GF) s st { γ with st := γ.st.withPhys p } =
      mvcc.isWatchableStore s st γ := rfl

end lemmas

end EtcdGrove
end Perennial
