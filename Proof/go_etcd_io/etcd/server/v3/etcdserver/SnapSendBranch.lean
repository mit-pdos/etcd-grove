/-
**`applyAll`'s `msgSnapC` branch: the sender's backend and store contracts** (D22 S-h, 2026-10-20;
`notes/decisions.md`, "D22 S-h carried out"). Lean-first (no Rocq counterpart).

The branch is dead: `msgSnapC` carries nothing (`isRNMsgSnapC`'s `rnSnapMsg`, `False` since the
server's clusters send no snapshot, 2026-10-27). Until 2026-10-27 this file also proved the branch
itself (`snapBranch_send`, over `SnapSendBundle.lean`'s `srvMergedBundle`, the merged message as the
network's snapshot bundle) from raft's internals (`isRaftMsg`, `raftCommitInv`, `raftSnapCert`,
`isCommitted`, `termLB`): deleted with the port onto raft's node API, which has the server send no
snapshot. What is left are the sender's contracts of `s.KV().Commit()` (`srvKVCommitOk_of_kv`) and
`s.be.Snapshot()` (`srvBeSnapOk_of_backend`, `srvBeSnapOk_window`: the stored-index window), and the
sole writer's well-formed log (`soleWriter_idxWf`, the image's).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBuild
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvSnapSend
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__createMergedSnapshotMessage
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__sendMergedSnap
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__Snapshot
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Commit
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.KVView
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.KVWrite
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.CindexBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.HooksBackend
public import Spec.go_etcd_io.etcd.server.v3.storage.BackendHooks__OnPreCommitUnsafe

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The snapshot contract from the backend's** (`backend.Snapshot.spec`): the real backend `bl`'s
`Snapshot()`, with an open share, a write-back's budget token and the caller's resource `R`, whose
observation `Q` of every commit (with the batch lock's client resource `W` and hooks' `Pk`) is
what the snapshot's data `D` satisfies (as `Q (sData P D) (hkData P D) (rbData P D)`). -/
theorem srvBeSnapOk_of_backend (hSnap : backend.backend.Snapshot.spec (GF := GF) (hG := hG))
    (γ : backend.BNames) (P : backend.BParams) (W Pk : IProp GF) (bl : Loc) (qo : Qp)
    (R : IProp GF)
    (Q : backend.VData → GMap (GoString × GoString) GoString → GMap GoString backend.BktData →
      Prop) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      backend.isBackend γ P W Pk bl ∗
      □ (∀ (vd : backend.VData) (d : GMap (GoString × GoString) GoString)
          (r : GMap GoString backend.BktData),
        R -∗ W -∗ Pk -∗ backend.viewAt γ vd -∗ backend.hkOwn γ d -∗ backend.rbOwn γ r -∗
          ⌜Q vd d r⌝) ⊢
      srvBeSnapOk
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
          #bl)
        iprop(backend.bOpen γ qo ∗ backend.wbTok γ ∗ R) iprop(backend.bOpen γ qo ∗ R)
        (fun D => Q (backend.sData P D) (backend.hkData P D) (backend.rbData P D)) := by
  iintro ⟨#Hpkg, #Hb, #HQ⟩
  iunfold srvBeSnapOk
  iexists ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty, #bl⟩
  isplitr
  · ipureintro; rfl
  iintro %Φ !> ⟨Ho, Hwb, HR⟩ HΦ
  wp_apply hSnap γ P W Pk bl qo R Q $$ [Ho Hwb HR] as %sp %D ⟨Hsn, Ho, HR, %HQD⟩
  · iframe #; iframe
  iapply HΦ
  iframe
  ipureintro; exact HQD

/-- **`s.KV().Commit()`'s contract from `store.Commit`** (D22 S-l's sender items, 2026-10-22:
`store.Commit` translated and proved): over a KV of the store `st` (`txn.isKV`: the store itself
or the watchable store over it, whose `Commit` is promoted), for the store's sole writer: its
fragment, its reader token of the backend and a write session's token (`storeWT`: for the real
backend, a write-back's budget, `srvWTPool_take_extra`); a request `X ⇒ Y` its backend serves
(`mvcc.storeReq`: D22 the stored-index window, 2026-10-23, `storeReq_freeze`) and a frame `F`. -/
theorem srvKVCommitOk_of_kv (hC : mvcc.store.Commit.spec (GF := GF) (hG := hG))
    (kv : GoInterface) (st : Loc) (γ : mvcc.StoreNames) (X Y F : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ txn.isKV kv st γ ⊢
      srvKVCommitOk kv
        iprop(mvcc.writerFrag γ ∗ mvcc.writerOwn γ ∗ mvcc.storeWT γ ∗ X ∗ mvcc.storeReq γ X Y ∗ F)
        iprop(mvcc.writerFrag γ ∗ mvcc.writerOwn γ ∗ Y ∗ F) := by
  iintro ⟨#Hpkg, #Hkv⟩
  ihave ⟨#Hko, #Hs⟩ := txn.isKV_kvOver kv st γ $$ Hkv
  ihave %Hok := mvcc.kvOver_ok kv st $$ Hko
  obtain ⟨ty, v, rfl⟩ := Hok
  iunfold srvKVCommitOk
  iexists ⟨ty, v⟩
  isplitr
  · ipureintro; rfl
  iintro %Φ !> ⟨Hfr, Hro, Hwt, HX, Hrq, HF⟩ HΦ
  iapply mvcc.kvOver_commit_wp ty v st
  iframe Hko
  iapply (hC st γ X Y) $$ [Hfr Hro Hwt HX Hrq]
  · iframe #; iframe
  iintro !> ⟨Hfr, Hro, HY⟩
  iapply HΦ
  iframe

/-! ## The stored-index window (D22, 2026-10-23)

`notes/decisions.md`, "D22 the stored-index window carried out". Between `s.KV().Commit()` and
`s.be.Snapshot()` the apply thread holds the protocol frozen at its state `s` (`consFrozen`): its
`Commit()` asks the backend's hooks (`backend.commitReq`) to trade its state for `freezeY γA s` at
the consistent index's save (`commit_freeze_au`), every commit until it closes the window
(`unfreeze`) stores `s.k` again, and the snapshot's observation reads `s.k` in the committed meta
keys (`snapObs_window`): the image's index half (`imageAt_of_snap`'s `hci`, `htm`). -/

/-- **The apply thread's request over the server's backend** (`backend.commitReq`): the backend
whose hooks are the server's `BackendHooks` `bh` over the consistent index `ci` (as
`backend_server_hooks` makes it) serves `applyThread γA s ⇒ freezeY γA s` for a state `s` with
`ci` not 0 and nothing in flight. -/
theorem commitReq_freeze
    (hOn : storage.BackendHooks.OnPreCommitUnsafe.spec (GF := GF) (hG := hG))
    (hSave : consistentIndex.UnsafeSave.spec (GF := GF) (hG := hG))
    (hPut : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (γA : ApplyNames) (ci : Loc) (γ : backend.BNames) (P : backend.BParams) (W : IProp GF)
    (b bh lgh : Loc) (hP : ciKeys P) (hH : storage.hooksParams P) (s : ApplyState)
    (hk0 : s.k ≠ W64 0) (hps : s.pending = false) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗
      storage.isBackendHooks bh
        ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty,
          #ci⟩ lgh ∗
      backend.isBackendNH γ P W (batchLockInv γA (metaTM γ P)) b (storage.hooksIface bh) ∗
      backend.isBackend γ P W (batchLockInv γA (metaTM γ P)) b ∗
      isCI ci γA.ci ∗ inv applyN (consInv γA) ⊢
      backend.commitReq γ P (batchLockInv γA (metaTM γ P)) b (applyThread γA s)
        (freezeY γA s) := by
  iintro ⟨#Hspkg, #Hbpkg, #Hsch, #Hcpkg, #Hh, #Hnh, #Hb, #Hci, #Hinv⟩
  iunfold backend.isBackendNH at Hnh
  icases Hnh with ⟨%t, %rt, %tm, %db, %lg, #Ht, -, -, -, -, #Hhk, -⟩
  unfold backend.commitReq
  iright
  iexists t, storage.hooksIface bh
  iframe Ht Hhk
  iapply hooksReq_backendHooks hOn γ P W _ b t bh _ lgh hH
  iframe Hspkg Hbpkg Hsch Hh Hb Ht
  iapply ci_saveFreeze hSave hPut hUR hID hName hSafe γA ci γ P W _ b t hP hH s hk0 hps
  iframe #

/-- The apply thread's request as the store's (`mvcc.storeReq`), over the real instance `d`
holding the server's backend. -/
theorem storeReq_freeze
    (hOn : storage.BackendHooks.OnPreCommitUnsafe.spec (GF := GF) (hG := hG))
    (hSave : consistentIndex.UnsafeSave.spec (GF := GF) (hG := hG))
    (hPut : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (γA : ApplyNames) (ci : Loc) (γ : mvcc.StoreNames) (d : mvcc.KBReal) (hk : γ.kb = some d)
    (W : IProp GF) (bh lgh : Loc) (hP : ciKeys d.P) (hH : storage.hooksParams d.P)
    (s : ApplyState) (hk0 : s.k ≠ W64 0) (hps : s.pending = false) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗
      storage.isBackendHooks bh
        ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty,
          #ci⟩ lgh ∗
      backend.isBackendNH d.γB d.P W (batchLockInv γA (metaTM d.γB d.P)) d.be
        (storage.hooksIface bh) ∗
      backend.isBackend d.γB d.P W (batchLockInv γA (metaTM d.γB d.P)) d.be ∗
      isCI ci γA.ci ∗ inv applyN (consInv γA) ⊢
      mvcc.storeReq γ (applyThread γA s) (freezeY γA s) := by
  iintro #H
  unfold mvcc.storeReq mvcc.kbReq
  rw [hk]
  unfold mvcc.bkReq
  iright
  iexists W, batchLockInv γA (metaTM d.γB d.P)
  ihave #H2 := H
  icases H2 with ⟨-, -, -, -, -, -, #Hb, -⟩
  iframe Hb
  iapply commitReq_freeze hOn hSave hPut hUR hID hName hSafe γA ci d.γB d.P W d.be bh lgh hP hH s
    hk0 hps $$ H

/-- What the snapshot's observation finds of the committed meta keys in the window at `k`: the
consistent index `k` and some term. -/
def ciObs (k : w64) (d : GMap (GoString × GoString) GoString) : Prop :=
  d.lookup (go_etcd_io.etcd.server.v3.storage.schema.metaName,
      go_etcd_io.etcd.server.v3.storage.schema.ciKeyBytes) = encMeta k ∧
    ∃ t : w64, d.lookup (go_etcd_io.etcd.server.v3.storage.schema.metaName,
      go_etcd_io.etcd.server.v3.storage.schema.termKeyBytes) = encMeta t

/-- **The snapshot's observation in the window** (`backend.Snapshot.spec`'s `Q`): with the
server's batch-lock resource as the hooks' (`batchLockInv`), the window's `freezeY γA s` and the
apply thread's half of the tracked buckets at `rb`, a commit's hook keys hold `s.k` (`ciObs`) and
its tracked buckets are `rb`. -/
theorem snapObs_window (γA : ApplyNames) (γ : backend.BNames) (P : backend.BParams)
    (hP : ciKeys P) (W F : IProp GF) (s : ApplyState) (rb : GMap GoString backend.BktData) :
    ⊢ □ (∀ (vd : backend.VData) (d : GMap (GoString × GoString) GoString)
          (r : GMap GoString backend.BktData),
        iprop(freezeY γA s ∗ backend.rbOwn γ rb ∗ F) -∗ W -∗ batchLockInv γA (metaTM γ P) -∗
          backend.viewAt γ vd -∗ backend.hkOwn γ d -∗ backend.rbOwn γ r -∗
          ⌜ciObs s.k d ∧ r = rb⌝) := by
  iintro !> %vd %d %r ⟨HY, Hrb, -⟩ - Hbl - Hhk Hr
  iunfold freezeY at HY
  icases HY with ⟨-, Hmq, -⟩
  iunfold batchLockInv at Hbl
  icases Hbl with ⟨%mm, Hmt, HTM, -⟩
  icombine Hmt Hmq gives %Hm1
  iunfold metaTM at HTM
  icases HTM with ⟨%S, Hk, %HmS⟩
  iunfold backend.hkOwn at Hk Hhk
  icombine Hk Hhk gives %Hd
  iunfold backend.rbOwn at Hrb Hr
  icombine Hrb Hr gives %Hrr
  ipureintro
  obtain ⟨-, Hm1⟩ := Hm1
  obtain ⟨-, Hd⟩ := Hd
  obtain ⟨-, Hrr⟩ := Hrr
  subst Hd
  refine ⟨⟨?_, mm.2, ?_⟩, Hrr.symm⟩
  · rw [backend.hkData_lookup, ciKeys_hk hP (Or.inl rfl)]
    simp only [↓reduceIte]
    rw [HmS.1, Hm1]
  · rw [backend.hkData_lookup, ciKeys_hk hP (Or.inr rfl)]
    simp only [↓reduceIte]
    exact HmS.2

/-- **`s.be.Snapshot()` in the window**: `srvBeSnapOk_of_backend` with the window's observation
(`snapObs_window`): the snapshot's data holds the consistent index `s.k` and the tracked buckets
`rb` (`imageAt_of_snap`'s `hci`, `htm`, `hrb`). -/
theorem srvBeSnapOk_window (hSnap : backend.backend.Snapshot.spec (GF := GF) (hG := hG))
    (γA : ApplyNames) (γ : backend.BNames) (P : backend.BParams) (hP : ciKeys P) (W : IProp GF)
    (bl : Loc) (qo : Qp) (s : ApplyState) (rb : GMap GoString backend.BktData) (F : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      backend.isBackend γ P W (batchLockInv γA (metaTM γ P)) bl ⊢
      srvBeSnapOk
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
          #bl)
        iprop(backend.bOpen γ qo ∗ backend.wbTok γ ∗ (freezeY γA s ∗ backend.rbOwn γ rb ∗ F))
        iprop(backend.bOpen γ qo ∗ (freezeY γA s ∗ backend.rbOwn γ rb ∗ F))
        (fun D => ciObs s.k (backend.hkData P D) ∧ backend.rbData P D = rb) := by
  iintro ⟨#Hpkg, #Hb⟩
  iapply srvBeSnapOk_of_backend hSnap γ P W (batchLockInv γA (metaTM γ P)) bl qo
    iprop(freezeY γA s ∗ backend.rbOwn γ rb ∗ F)
    (fun _ d r => ciObs s.k d ∧ r = rb)
  iframe Hpkg Hb
  iapply snapObs_window γA γ P hP W F s rb

/-- **The sender's KV log is well formed as a store's committed log** (D22 J7b, 2026-10-26;
`imageAt_of_snap`'s `hwf`): the apply thread's sole writer (`apply.kvOwn`'s `txn.kvWriter`) at its
log `log` (the applied `kvModel γk A`, `kvApplied`) knows its certificate's sealed facts
(`idxSealed_pure`: `LogWf'`, fewer than `2 ^ 63` revisions and changes per revision) and, from its
budget, that the log has at least two and fewer than `2 ^ 48 + 2` revisions
(`soleWriter_small'`): `IdxWf log []`, with no change pending. -/
theorem soleWriter_idxWf (γ : mvcc.StoreNames) (log : mvcc.Log) :
    txn.soleWriter (GF := GF) γ log ⊢ ⌜mvcc.IdxWf log []⌝ := by
  iintro H
  ihave ⟨%H2, H⟩ := txn.soleWriter_len' γ log $$ H
  ihave ⟨H, #Hc⟩ := txn.soleWriter_cert γ log $$ H
  ihave %Hs := txn.soleWriter_small' γ log $$ H
  ihave #Hse := mvcc.idxCert_sealed γ.idx log $$ Hc
  ihave %Hp := mvcc.idxSealed_pure γ.idx log $$ Hse
  ipureintro
  obtain ⟨hwf, -, hcs⟩ := Hp
  have hne : log ≠ [] := by intro h; subst h; simp at H2
  refine ⟨mvcc.LogWf'.append_nil hwf hne, by omega, by simp, hcs⟩

end proof

end EtcdGrove
end Perennial
