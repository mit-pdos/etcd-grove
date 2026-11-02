/-
**`applyAll`'s `msgSnapC` branch: the sender's backend and store contracts** (D22 S-h, 2026-10-20;
`notes/decisions.md`, "D22 S-h carried out"). Lean-first (no Rocq counterpart).

(2026-10-31, S1) The branch is live again: `msgSnapC` carries raft's `MsgSnap`s (`isRNMsgSnapC`'s
`rnSnapMsg`), which `applyAll` merges with the backend's image when the guard holds
(`notes/decisions.md`, "The merged snapshot's index guard"). This file has what the branch's proof
uses beside `SnapCert.lean`'s `srv_merged_sent`: the bag's nonblocking receive
(`chanBag_nbRecv`), the conf states' agreement (`csPts_agree`), the merged message as the network's
snapshot bundle (`srvMerged_bundle`), and the two lemmas left for S2 (`sorry`): the snapshot window
(`mergedCreate_window`, the contracts `createMergedSnapshotMessage` takes of `s.KV().Commit()` and
`s.be.Snapshot()`, over the image's observation `mergedObs`) and the image (`merged_image`, the
observation as the network's image certificate). (2026-10-27 to 2026-10-31 the branch was dead,
`rnSnapMsg` `False`; until 2026-10-27 this file proved it from raft's internals, `snapBranch_send`,
deleted with the port onto raft's node API.) The rest are the sender's contracts of `s.KV().Commit()`
(`srvKVCommitOk_of_kv`) and `s.be.Snapshot()` (`srvBeSnapOk_of_backend`, `srvBeSnapOk_window`: the
stored-index window), and the sole writer's well-formed log (`soleWriter_idxWf`, the image's).
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
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.KeyObs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.CindexBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.HooksBackend
public import Spec.go_etcd_io.etcd.server.v3.storage.BackendHooks__OnPreCommitUnsafe
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyKVCore
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AppliedOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapCert

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
      Prop) (QR : backend.Data → Prop) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      backend.isBackend γ P W Pk bl ∗
      □ (∀ (vd : backend.VData) (d : GMap (GoString × GoString) GoString)
          (r : GMap GoString backend.BktData),
        R -∗ W -∗ Pk -∗ backend.viewAt γ vd -∗ backend.hkOwn γ d -∗ backend.rbOwn γ r -∗
          ⌜Q vd d r⌝) ∗
      □ (∀ D : backend.Data, R -∗ backend.fkRd γ P (D, ⟨∅, W64 0⟩) -∗ ⌜QR D⌝ ∗ R) ⊢
      srvBeSnapOk
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
          #bl)
        iprop(backend.bOpen γ qo ∗ backend.wbTok γ ∗ R) iprop(backend.bOpen γ qo ∗ R)
        (fun D => Q (backend.sData P D) (backend.hkData P D) (backend.rbData P D) ∧ QR D) := by
  iintro ⟨#Hpkg, #Hb, #HQ, #HQR⟩
  iunfold srvBeSnapOk
  iexists ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty, #bl⟩
  isplitr
  · ipureintro; rfl
  iintro %Φ !> ⟨Ho, Hwb, HR⟩ HΦ
  wp_apply hSnap γ P W Pk bl qo R Q $$ [Ho Hwb HR] as %sp %D ⟨Hsn, Ho, HR, #Hfk, %HQD⟩
  · iframe #; iframe
  ihave ⟨%HQRD, HR⟩ := HQR $$ %D HR Hfk
  iapply HΦ
  iframe
  ipureintro; exact ⟨HQD, HQRD⟩

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
nothing in flight. -/
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
    (hps : s.pending = false) :
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
  iapply ci_saveFreeze hSave hPut hUR hID hName hSafe γA ci γ P W _ b t hP hH s hps
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
    (s : ApplyState) (hps : s.pending = false) :
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
    hps $$ H

/-- What the snapshot's observation finds of the committed meta keys in the window at `k`: the
consistent index `k` and some term. -/
def ciObs (k : w64) (d : GMap (GoString × GoString) GoString) : Prop :=
  d.lookup (go_etcd_io.etcd.server.v3.storage.schema.metaName,
      go_etcd_io.etcd.server.v3.storage.schema.ciKeyBytes) = encMeta k ∧
    ∃ t : w64, d.lookup (go_etcd_io.etcd.server.v3.storage.schema.metaName,
      go_etcd_io.etcd.server.v3.storage.schema.termKeyBytes) = encMeta t

/-- **The snapshot's observation in the window** (`backend.Snapshot.spec`'s `Q`): with the
server's batch-lock resource as the hooks' (`batchLockInv`), the window's `freezeY γA s` and the
apply thread's half of the tracked buckets at `rb`, a commit's hook keys hold `ciEff γA s.k`
(`ciObs`; `s.k` itself unless `ci` is 0, then the keys the backend was opened with) and its tracked
buckets are `rb`; with what the frame `F` observes of the view with the batch lock's resource
`W` (`QF`, 2026-11-02: the writer's key observation, `txn.kvWriter_keyObs`). -/
theorem snapObs_window (γA : ApplyNames) (γ : backend.BNames) (P : backend.BParams)
    (hP : ciKeys P) (W F : IProp GF) (s : ApplyState) (rb : GMap GoString backend.BktData)
    (QF : backend.VData → Prop) :
    □ (∀ vd, F -∗ W -∗ backend.viewAt γ vd -∗ ⌜QF vd⌝) ⊢
      □ (∀ (vd : backend.VData) (d : GMap (GoString × GoString) GoString)
          (r : GMap GoString backend.BktData),
        iprop(freezeY γA s ∗ backend.rbOwn γ rb ∗ F) -∗ W -∗ batchLockInv γA (metaTM γ P) -∗
          backend.viewAt γ vd -∗ backend.hkOwn γ d -∗ backend.rbOwn γ r -∗
          ⌜(ciObs (ciEff γA s.k) d ∧ r = rb) ∧ QF vd⌝) := by
  iintro #HQF !> %vd %d %r ⟨HY, Hrb, HF⟩ HW Hbl Hv Hhk Hr
  ihave %hQF := HQF $$ %vd HF HW Hv
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
  refine ⟨⟨⟨?_, mm.2, ?_⟩, Hrr.symm⟩, hQF⟩
  · rw [backend.hkData_lookup, ciKeys_hk hP (Or.inl rfl)]
    simp only [↓reduceIte]
    rw [HmS.1, Hm1]
  · rw [backend.hkData_lookup, ciKeys_hk hP (Or.inr rfl)]
    simp only [↓reduceIte]
    exact HmS.2

/-- **`s.be.Snapshot()` in the window**: `srvBeSnapOk_of_backend` with the window's observation
(`snapObs_window`): the snapshot's data holds the consistent index `ciEff γA s.k` and the tracked
buckets `rb` (`imageAt_of_snap`'s `hci`, `htm`, `hrb`), and the frame's observation `QF` of its
view. -/
theorem srvBeSnapOk_window (hSnap : backend.backend.Snapshot.spec (GF := GF) (hG := hG))
    (γA : ApplyNames) (γ : backend.BNames) (P : backend.BParams) (hP : ciKeys P) (W : IProp GF)
    (bl : Loc) (qo : Qp) (s : ApplyState) (rb : GMap GoString backend.BktData) (F : IProp GF)
    (QF : backend.VData → Prop) (QR : backend.Data → Prop) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      backend.isBackend γ P W (batchLockInv γA (metaTM γ P)) bl ∗
      □ (∀ vd, F -∗ W -∗ backend.viewAt γ vd -∗ ⌜QF vd⌝) ∗
      □ (∀ D : backend.Data, F -∗ backend.fkRd γ P (D, ⟨∅, W64 0⟩) -∗ ⌜QR D⌝ ∗ F) ⊢
      srvBeSnapOk
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
          #bl)
        iprop(backend.bOpen γ qo ∗ backend.wbTok γ ∗ (freezeY γA s ∗ backend.rbOwn γ rb ∗ F))
        iprop(backend.bOpen γ qo ∗ (freezeY γA s ∗ backend.rbOwn γ rb ∗ F))
        (fun D => ((ciObs (ciEff γA s.k) (backend.hkData P D) ∧ backend.rbData P D = rb) ∧
          QF (backend.sData P D)) ∧ QR D) := by
  iintro ⟨#Hpkg, #Hb, #HQF, #HQR⟩
  iapply srvBeSnapOk_of_backend hSnap γ P W (batchLockInv γA (metaTM γ P)) bl qo
    iprop(freezeY γA s ∗ backend.rbOwn γ rb ∗ F)
    (fun vd d r => (ciObs (ciEff γA s.k) d ∧ r = rb) ∧ QF vd) QR
  iframe Hpkg Hb
  isplitl
  rotate_left
  · iintro !> %D ⟨HY, Hrb, HF⟩ Hfk
    ihave ⟨%h, HF⟩ := HQR $$ %D HF Hfk
    iframe HY Hrb HF
    ipureintro; exact h
  iapply snapObs_window γA γ P hP W F s rb QF $$ HQF

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

/-- **The backend with its hooks field known** (`isBackendNH`, what `commitReq_freeze` takes): the
backend's contract and its `hooks` field (`backend.hooksAt`, the creation specs'). -/
theorem isBackendNH_of_hooksAt (γ : backend.BNames) (P : backend.BParams) (W Pk : IProp GF)
    (b : Loc) (h : GoInterface) :
    backend.isBackend (GF := GF) γ P W Pk b ∗ backend.hooksAt b h ⊢
      backend.isBackendNH γ P W Pk b h := by
  iintro ⟨#Hb, #Hh⟩
  iunfold backend.isBackend at Hb
  iunfold backend.hooksAt at Hh
  icases Hb with ⟨%t, %rt, %tm, %db, %lg, %h', #Ht, #Hrt, #Hlim, #Hlg, %Hlg0, #Hh', #Hbe, #Htm, -,
    #Hmu, #Hrmu, #Htmu, #Hcmu, #Hci, #Hmet, #Hdbmu, #Hdb, %Hwf⟩
  icombine Hh Hh' gives %Heq
  subst Heq
  iunfold backend.isBackendNH
  imodintro
  iexists t, rt, tm, db, lg
  iframe #
  ipureintro; exact ⟨Hlg0, Hwf⟩

/-- `srvBeSnapOk` is monotone in its observation. -/
theorem srvBeSnapOk_mono (b : GoInterface) (RS RS' : IProp GF) (Q Q' : backend.Data → Prop)
    (hQ : ∀ D, Q D → Q' D) : srvBeSnapOk (GF := GF) b RS RS' Q ⊢ srvBeSnapOk b RS RS' Q' := by
  iintro H
  iunfold srvBeSnapOk at H
  iunfold srvBeSnapOk
  icases H with ⟨%bi, %Hb, #Ht⟩
  iexists bi
  isplitr
  · ipureintro; exact Hb
  iintro %Φ !> HR HΦ
  iapply Ht $$ HR
  iintro %sp %D
  inext
  iintro ⟨Hs, HR', %h⟩
  iapply HΦ
  iframe
  ipureintro; exact hQ D h

/-! ## The merged snapshot (2026-10-31, S1) -/

/-- **A bag's nonblocking receive**: whatever the bag holds, a value received carries `P`. (A fact
of Perennial's bag idiom, `Bag.lean`, beside `bag_recv_au`: `notes/perennial-changes.md`.) -/
theorem chanBag_nbRecv (γ : ChanNames) (ch : Loc) (P : Loc → IProp GF)
    (Φ : Loc → Bool → IProp GF) :
    isChanBag γ ch P ⊢ (∀ v, P v -∗ Φ v true) -∗ nonblockingRecvAuInner γ Loc Φ := by
  rw [isChanBag_unseal]; unfold isChanBagDef nonblockingRecvAuInner
  iintro ⟨-, #Hinv⟩ HΦ
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold chanBagInv
  icases Hi with ⟨%s, Hoc0, Hi⟩
  iexists s
  iframe Hoc0
  rcases s with (_ | ⟨v, rest⟩) | _ | v | _ | _ | _ | (_ | ⟨_, _⟩)
  all_goals dsimp only
  case Buffered.cons =>
    iintro Hoc
    icases BigSepL.bigSepL_cons.1 $$ Hi with ⟨HP, Hi⟩
    imod Hmask with -
    imod Hclose $$ [Hoc Hi] with -
    · inext; iexists .Buffered rest; iframe
    imodintro
    iapply HΦ $$ HP
  case SndPending =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc] with -
    · inext; iexists .RcvCommit; iframe
    imodintro
    iapply HΦ $$ Hi
  all_goals first | itrivial | (iexfalso; iexact Hi)

/-- Two read-only views of a conf state agree. -/
theorem csPts_agree (p : Loc) (c1 c2 : ConfStateM) (al1 al2 : Bool) :
    csPts (GF := GF) p DFrac.discard c1 al1 ∗ csPts p DFrac.discard c2 al2 ⊢ ⌜c1 = c2⌝ := by
  iintro ⟨H1, H2⟩
  iunfold csPts at H1 H2
  icases H1 with ⟨%sv1, %sl1, %so1, %sn1, %pa1, -, HV1, Hv1, HL1, Hl1, HO1, Ho1, HN1, Hn1, HA1,
    #cA1, -, -⟩
  icases H2 with ⟨%sv2, %sl2, %so2, %sn2, %pa2, -, HV2, Hv2, HL2, Hl2, HO2, Ho2, HN2, Hn2, HA2,
    #cA2, -, -⟩
  icombine HV1 HV2 gives %e1
  icombine HL1 HL2 gives %e2
  icombine HO1 HO2 gives %e3
  icombine HN1 HN2 gives %e4
  icombine HA1 HA2 gives %e5
  subst e1 e2 e3 e4 e5
  ihave %f1 := ownSlice_agree _ _ _ _ _ $$ Hv1 Hv2
  ihave %f2 := ownSlice_agree _ _ _ _ _ $$ Hl1 Hl2
  ihave %f3 := ownSlice_agree _ _ _ _ _ $$ Ho1 Ho2
  ihave %f4 := ownSlice_agree _ _ _ _ _ $$ Hn1 Hn2
  ihave %f5 : ⌜c1.AutoLeave' = c2.AutoLeave'⌝ $$ []
  · iapply cellRO_agree pa1
    isplit
    · iexact cA1
    · iexact cA2
  ipureintro
  cases c1; cases c2
  simp_all

/-- A conf state read back from a nested pointer (`createMergedSnapshotMessage`'s `csOpt`) is the
one a read-only view of it holds. -/
theorem csOpt_agree (p : Loc) (c1 c2 : ConfStateM) :
    csOpt (GF := GF) p DFrac.discard c1 ∗ csPts p DFrac.discard c2 false ⊢ ⌜c1 = c2⌝ := by
  iintro ⟨H1, H2⟩
  iunfold csOpt at H1
  icases H1 with (%Hn | H1)
  · iunfold csPts at H2
    icases H2 with ⟨%sv, %sl, %so, %sn, %pa, %Hnn, -⟩
    exact absurd Hn.1 Hnn
  · iapply csPts_agree p c1 c2 false false
    iframe H1 H2

/-- **A `MsgSnap` the server's node sent has a snapshot past index `0`**: its certificate
(`sentMsg_snapshot`) is of a non-empty committed log (`snapshotCert_made`). -/
theorem srv_sentSnap_pos (γr : ReadNames) (sid : w64) (st : MsgSt) (sv : SnapshotM)
    (hty : st.msg.Type' = MsgSnap) (hsv : st.snap = some sv) :
    letI := srvStor (GF := GF) γr.raft.raft
    srvRaftLogInv (GF := GF) γr.raft ∗ sentMsg γr.raft.raft.cl srvClusterN sid st ⊢
      ⌜0 < uint.Z sv.Metadata'.Index'⌝ := by
  letI := srvStor (GF := GF) γr.raft.raft
  iintro ⟨#Hinv, #Hs⟩
  ihave ⟨%sv0, %Hsv0, #Hk⟩ := sentMsg_snapshot _ _ _ _ hty $$ Hs
  rw [hsv] at Hsv0
  cases Hsv0
  iunfold srvRaftLogInv at Hinv
  icases Hinv with ⟨-, #Hcl, -⟩
  iunfold srvClusterOk at Hcl
  icases Hcl with ⟨#Hc, -⟩
  ihave ⟨%l, %m, -, -, -, %Hf⟩ := snapshotCert_made _ _ _ $$ [Hc Hk]
  · iframe Hc Hk
  ipureintro
  obtain ⟨hl, ht, -⟩ := Hf
  simp only [snapTrip, snapId] at hl ht
  rcases l with _ | ⟨e, l⟩
  · simp at ht
  · simp only [List.length_cons] at hl
    have := uint_nat_eq sv.Metadata'.Index'
    omega

/-- The frozen entry's index is below `2 ^ 61` (`memLog_bound`). -/
theorem srvFrozenTerm_bound (γs : MemStorNames) (ai at' : w64) :
    srvFrozenTerm (GF := GF) γs ai at' ⊢ ⌜uint.Z ai < 2 ^ 61⌝ := by
  iintro #Hft
  iunfold srvFrozenTerm at Hft
  icases Hft with (%H0 | ⟨%e, #He, -⟩)
  · ipureintro; have := uint_nat_eq ai; omega
  ihave %Hb := memLog_bound γs (uint.nat ai) DFrac.discard [e] $$ He
  ipureintro
  rcases Hb with h | h
  · cases h
  · have := uint_nat_eq ai; simp only [List.length_singleton] at h; omega

/-- **The merged message as the network's snapshot bundle** (`netSnapBundle`, `sendMergedSnap`'s
premise): read-only, of a `MsgSnap` the node `sid` sent (`srv_merged_sent`), with new credits (a
`MsgSnap` is no `MsgProp`, `msgCredits_intro`), the reader's streams of the image `D`, and the
image's certificate at the snapshot's index (`merged_image`). -/
theorem srvMerged_bundle (γ : SrvRaft) (ml : Loc) (rc : GoInterface) (st : MsgSt) (sid : w64)
    (c : ConfStateM) (ai at' : w64) (D : backend.Data) (hty : st.msg.Type' = MsgSnap) :
    letI := srvStor (GF := GF) γ
    msgOwn ml DFrac.discard (mergedSt st c ai at') ∗
      sentMsg γ.cl srvClusterN sid { st with snap := some (memSnapMade ai at' c []) } ∗
      backend.readerStreams rc (fun bs => backend.boltImage bs D) ∗
      □ (srvNet (GF := GF) γ).img ai D ⊢ |==> netSnapBundle (srvNet γ) ml rc := by
  have hP : (mergedSt st c ai at').msg.Type' ≠ MsgProp := by
    simp only [mergedSt]; rw [hty]; simp [MsgSnap, MsgProp]
  letI := srvStor (GF := GF) γ
  rw [show ({ st with snap := some (memSnapMade ai at' c []) } : MsgSt) = mergedSt st c ai at'
    from rfl]
  iintro ⟨#Hm, #Hs, Hrs, #Himg⟩
  ihave %Hsh := sentMsg_shape γ.cl srvClusterN sid _ $$ Hs
  imod msgCredits_intro γ.cl srvClusterN (mergedSt st c ai at')
    hP with HO
  imodintro
  iunfold netSnapBundle
  iexists mergedSt st c ai at', SnapshotM.mk [] (SnapshotMetadataM.mk c ai at'), D
  iframe Hm Hrs Himg
  isplitr
  · iintro !>
    simp only [srvNet]
    iexists sid; iexact Hs
  isplitl [HO]
  · simp only [srvNet]; iexact HO
  ipureintro
  exact ⟨by simp only [mergedSt]; exact hty, rfl, Hsh.1.2.2.2.2.2.2.2⟩

/-- **What the merged snapshot's image observes** (`createMergedSnapshotMessage`'s `Qd`): the
backend's data `D` holds at most the KV log `log` in its `Key` bucket (every key it has is `log`'s,
at its value), exactly `log` with the compaction mode `cmp` off (2026-11-02: with compaction on,
the compaction job deletes keys physically, so the snapshot can lack keys of `log`; the writer's
observation `txn.kvWriter_keyObs`), the consistent index `ai` and some
term in `Meta`, the other buckets of the committed log `A` (`bkRestAt`), and `log` is a well-formed
committed log (`IdxWf`): `imageAt`'s clauses, over the apply thread's KV log in place of the model
(`merged_image` relates them). (2026-10-31, the user's decision) No compaction key in `Meta` only
with the store's compaction mode `cmp` off (`noCmpData`; until then unconditionally, `keyImage`,
which is false of a snapshot taken with compactions applied): a compacted image is the image
certificate's to state (`merged_image`, the durability work's `srvImageR`). -/
def mergedObs (γr : ReadNames) (cmp : Bool) (ai : w64) (A : List EntryModel) (log : mvcc.Log)
    (D : backend.Data) : Prop :=
  (∀ k v, backend.dget D mvcc.keyName k = some v → (mvcc.bucketMap log).lookup k = some v) ∧
    (cmp = false → ∀ k, backend.dget D mvcc.keyName k = (mvcc.bucketMap log).lookup k) ∧
    (cmp = false → mvcc.noCmpData D) ∧
    backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName
      go_etcd_io.etcd.server.v3.storage.schema.ciKeyBytes = encMeta ai ∧
    (∃ t : w64, backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName
      go_etcd_io.etcd.server.v3.storage.schema.termKeyBytes = encMeta t) ∧
    bkRestAt γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A) D ∧ mvcc.IdxWf log []

/-- **(S2, open) The merged snapshot's window** (`createMergedSnapshotMessage`'s premise): with the
apply thread at the applied index `ai`, its consistent index (`loopOk`, `ciEff γ st.k = ai`) and
its KV at the log `x.log` (the shared row, `srvApplyKVCore`, in either auth mode), two time
receipts (for the commit's write token and the snapshot's write-back token), the contracts of
`s.KV().Commit()` (`srvKVCommitOk`) and `s.be.Snapshot()` (`srvBeSnapOk`) with the window's
resources (`RC`, the commit's `RC'` giving the snapshot's `RS`; D22 the stored-index window:
`storeReq_freeze`, `srvBeSnapOk_window`), the snapshot observing `mergedObs` at `ai`; once the
snapshot is taken (`RS'`, with `s.be` back), the apply thread's resources again, at a state of the
same consistent index. -/
theorem mergedCreate_window
    (hC : mvcc.store.Commit.spec (GF := GF) (hG := hG))
    (hSnap : backend.backend.Snapshot.spec (GF := GF) (hG := hG))
    (hOn : storage.BackendHooks.OnPreCommitUnsafe.spec (GF := GF) (hG := hG))
    (hSave : consistentIndex.UnsafeSave.spec (GF := GF) (hG := hG))
    (hPut : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (on : Bool) (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (b : GoInterface) (st : ApplyState)
    (ai a t : w64) (A : List EntryModel) (x : apply.ApplyKV) (γw γp : GName) (ua kv : GoInterface)
    (hok : loopOk γ st ai) (hci : ciEff γ st.k = ai) (hpos : 0 < uint.Z ai)
    (hlen : uint.Z ai = A.length) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerM on s γ ci TM E ρ γr ∗ srvKVAddr s ↦□ kv ∗ txn.isKV kv E.s E.γ ∗
      srvWTPool E γp ∗ appliedLogAt γr ai x.log ∗ srvRLogLb γr.raft A ∗ ⧗ 1 ∗ ⧗ 1 ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvApplyKVCore s E γw x ua ∗
      srvRest E γr A ⊢
    |={⊤}=> ∃ (be : GoInterface) (dq : DFrac) (RC RC' RS RS' : IProp GF),
      srvKVCommitOk kv RC RC' ∗ RC ∗ srvBeAddr s ↦{dq} be ∗
      srvBeSnapOk be RS RS' (mergedObs γr E.cmp ai A x.log) ∗ (RC' -∗ RS) ∗
      (RS' -∗ srvBeAddr s ↦{dq} be ={⊤}=∗ ∃ st' : ApplyState, applyThread γ st' ∗
        applyBackend γ ci b ∗ ciApplying ci a t ∗ srvApplyKVCore s E γw x ua ∗ srvRest E γr A ∗
        ⌜loopOk γ st' ai ∧ ciEff γ st'.k = ciEff γ st.k⌝) := by
  iintro ⟨#Hpkg, #Hsrv, #Hkva, #Hkv, #Hpool, -, -, Hr1, Hr2, Hst, Hab, Hca, HKV, HRs⟩
  -- the server's backend, its hooks and the protocol (`srvBeHooked`, `srvEnvOk`, `isServerCI`)
  iunfold isServerM at Hsrv
  icases Hsrv with ⟨-, #HCI, ⟨%v, #Hf⟩, -⟩
  iunfold srvFieldsAtM at Hf
  icases Hf with ⟨-, -, -, -, -, %Henv, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hbh⟩
  iunfold srvBeHooked at Hbh
  icases Hbh with ⟨%d, %bh, %lgh, %Hd, -, #Hbhk, #HhkAt, #HB⟩
  obtain ⟨hkb, hcK, hhP⟩ := Hd
  obtain ⟨-, -, -, γB, H, hRO, -, d', al, stl, lp, hkb', hγB, -, hcm⟩ := Henv
  rw [hkb] at hkb'
  obtain rfl := Option.some.inj hkb'
  subst hγB
  iunfold isServerCI at HCI
  icases HCI with ⟨-, #Hci, #Hinv⟩
  ihave #Hspkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage $$ []
  · iPkgInit
  ihave #Hbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  ihave #Hschpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave #Hcipkg : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex $$ []
  · iPkgInit
  ihave #Hmpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  ihave #Hnh := isBackendNH_of_hooksAt d.γB d.P (mvcc.lateW d.gx)
    (batchLockInv γ (metaTM d.γB d.P)) d.be (storage.hooksIface bh) $$ [HB HhkAt]
  · iframe #
  -- the commit's request: the window opened (`storeReq_freeze`)
  ihave #Hreq := storeReq_freeze hOn hSave hPut hUR hID hName hSafe γ ci E.γ d hkb
    (mvcc.lateW d.gx) bh lgh hcK hhP st hok.1 $$ [Hspkg Hbpkg Hschpkg Hcipkg Hbhk Hnh HB Hci Hinv]
  · iframe #
  -- the apply thread's KV resources
  iunfold srvApplyKVCore at HKV
  icases HKV with ⟨Hua, #Hap, Hakv, Hbo, Hra, Hw⟩
  iunfold apply.applyKV at Hakv
  icases Hakv with ⟨%p, %Hp, Hub, Hko, Hcmo⟩
  iunfold apply.kvOwn at Hko
  icases Hko with ⟨Hsr, Hkw, Hll, Hrd, Hwo⟩
  iunfold txn.kvWriter at Hkw
  icases Hkw with ⟨Hsw, Hwl, Hfr⟩
  ihave ⟨Hsw, %Hwf⟩ := keep_pure (soleWriter_idxWf E.γ x.log) $$ Hsw
  iunfold srvBeOwn at Hbo
  icases Hbo with ⟨%d2, %hd2, Hbe, Hg⟩
  rw [hkb] at hd2
  obtain rfl := Option.some.inj hd2
  -- two write-backs' tokens
  imod srvWTPool_take_extra_d E γp d _ $$ Hpool Hr1 Hg with ⟨Ht1, Hg⟩
  imod srvWTPool_take_extra_d E γp d _ $$ Hpool Hr2 Hg with ⟨Ht2, Hg⟩
  ihave Hwt := storeWT_of_wbTok E.γ d hkb $$ Ht1
  -- the rest buckets
  iunfold srvRest at HRs
  rw [hRO]
  iunfold srvRestOwnH at HRs
  icases HRs with ⟨Hro, HH⟩
  iunfold srvRestOwn at Hro
  icases Hro with ⟨Hrb, Hcl⟩
  have hRT : mvcc.storeRT (GF := GF) E.γ =
      iprop(backend.rdTok d.γB d.P d.be ∗ backend.bOpen d.γB backend.rdOpen) := by
    show mvcc.kbRT E.γ.kb = _
    rw [hkb]; rfl
  have hRB : ∀ n ∈ restBuckets, d.P.RB n = true := fun n hn => by
    simp [mvcc.KBReal.P, hn]
  imodintro
  iexists srvBeIface d.be, DFrac.own (1 : Qp).half
  iexists iprop(mvcc.writerFrag E.γ ∗ mvcc.writerOwn E.γ ∗ mvcc.storeWT E.γ ∗ applyThread γ st ∗
      mvcc.storeReq E.γ (applyThread γ st) (freezeY γ st) ∗ emp)
  iexists iprop(mvcc.writerFrag E.γ ∗ mvcc.writerOwn E.γ ∗ freezeY γ st ∗ emp)
  iexists iprop(backend.bOpen d.γB backend.rdOpen ∗ backend.wbTok d.γB ∗ (freezeY γ st ∗
      backend.rbOwn d.γB (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)).bk ∗
      (txn.kvWriter E.s E.γ x.log ∗ backend.rdTok d.γB d.P d.be ∗
        mvcc.retiredAt E.γ (2 + mvcc.nJobRd E.γ.kb))))
  iexists iprop(backend.bOpen d.γB backend.rdOpen ∗ (freezeY γ st ∗
      backend.rbOwn d.γB (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)).bk ∗
      (txn.kvWriter E.s E.γ x.log ∗ backend.rdTok d.γB d.P d.be ∗
        mvcc.retiredAt E.γ (2 + mvcc.nJobRd E.γ.kb))))
  isplitr
  · iapply srvKVCommitOk_of_kv hC kv E.s E.γ (applyThread γ st) (freezeY γ st) emp
    iframe #
  isplitl [Hfr Hwo Hwt Hst]
  · iframe Hfr Hwo Hwt Hst Hreq
  isplitl [Hbe]
  · iexact Hbe
  isplitr
  · -- the snapshot in the window, observing `mergedObs`
    iapply srvBeSnapOk_mono _ _ _ _ _ ?_
    rotate_left
    · iapply srvBeSnapOk_window hSnap γ d.γB d.P hcK (mvcc.lateW d.gx) d.be backend.rdOpen st
        (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)).bk
        iprop(txn.kvWriter E.s E.γ x.log ∗ backend.rdTok d.γB d.P d.be ∗
          mvcc.retiredAt E.γ (2 + mvcc.nJobRd E.γ.kb))
        (fun vd => (∀ k v, vd.lookup (mvcc.keyName, k) = some v →
            (mvcc.bucketMap x.log).lookup k = some v) ∧
          (d.cm = false → ∀ k, vd.lookup (mvcc.keyName, k) = (mvcc.bucketMap x.log).lookup k))
        (fun D => d.cm = false → backend.fkAbsD D)
      iframe Hbpkg HB
      isplitr
      · iintro !> %vd ⟨Hkw, -, -⟩ HW Hv
        iapply txn.kvWriter_keyObs E.s E.γ d hkb x.log vd $$ [Hkw HW Hv]
        iframe
      · iintro !> %D ⟨Hkw, Hrt, Hret⟩ #Hfk
        ihave ⟨%h, Hkw⟩ := txn.kvWriter_noCmp E.s E.γ d hkb x.log (D, ⟨∅, W64 0⟩) $$ [Hkw Hfk]
        · iframe Hkw Hfk
        iframe Hkw Hrt Hret
        ipureintro; exact fun hc => (h hc).1
    · intro D ⟨⟨⟨hciO, hrbD⟩, hthin, hex⟩, hnc⟩
      have hsd : ∀ k, (backend.sData d.P D).lookup (mvcc.keyName, k) =
          backend.dget D mvcc.keyName k := fun k => by
        rw [backend.sData_lookup]; simp [mvcc.KBReal.P]
      obtain ⟨hci1, t1, ht1⟩ := hciO
      rw [backend.hkData_lookup, ciKeys_hk hcK (Or.inl rfl)] at hci1
      rw [backend.hkData_lookup, ciKeys_hk hcK (Or.inr rfl)] at ht1
      refine ⟨fun k v h => hthin k v (by rw [hsd]; exact h), fun hc k => ?_,
        fun hc => mvcc.noCmpData_of_fkAbsD (hnc (hcm.trans hc)), ?_, ⟨t1, by simpa using ht1⟩,
        bkRestAt_of_rb hRB hrbD, Hwf⟩
      · rw [← hsd]; exact hex (hcm.trans hc) k
      · rw [← hci]; simpa using hci1
  isplitl [Hsw Hwl Ht2 Hrb]
  · iintro ⟨Hfr, Hwo, HY, -⟩
    iunfold mvcc.writerOwn at Hwo
    icases Hwo with ⟨Hrt, Hret⟩
    rw [hRT]
    icases Hrt with ⟨Hrdt, Hop⟩
    iframe Hop Ht2 HY Hrb Hrdt Hret
    iunfold txn.kvWriter
    iframe
  · iintro ⟨Hop, HY, Hrb, Hkw, Hrdt, Hret⟩ Hbe
    imod unfreeze γ st $$ Hinv HY with Hst
    imodintro
    iexists st
    iframe Hst Hab Hca
    isplitl [Hua Hub Hcmo Hsr Hll Hrd Hkw Hrdt Hret Hop Hra Hw Hbe Hg]
    · iunfold srvApplyKVCore
      isplitl [Hua]
      · iexact Hua
      isplitr
      · iexact Hap
      isplitl [Hub Hcmo Hsr Hll Hrd Hkw Hrdt Hret Hop]
      · iunfold apply.applyKV
        iexists p
        iframe Hub Hcmo
        isplitr
        · ipureintro; exact Hp
        iunfold apply.kvOwn
        iframe Hsr Hkw Hll Hrd
        iunfold mvcc.writerOwn
        iframe Hret
        rw [hRT]
        iframe Hrdt Hop
      isplitl [Hbe Hg]
      · iunfold srvBeOwn
        iexists d
        iframe Hbe Hg
        ipureintro; exact hkb
      isplitl [Hra]
      · iexact Hra
      iexact Hw
    isplitl [Hrb Hcl HH]
    · iunfold srvRest
      rw [hRO]
      iunfold srvRestOwnH
      iframe HH
      iunfold srvRestOwn
      iframe Hrb Hcl
    ipureintro; exact ⟨hok, rfl⟩

/-- **(S2, open) The merged snapshot's image** (the network's image certificate, `srvNet`'s `img`,
which the bundle carries): an observation `mergedObs` at the applied index `ai` of the applied log
`A` (`kvApplied`: the KV log the model's, `kvModel`) of the server, with the KV's start values
(`isServerApplyAll`'s). The image is exact at `ai` (the consistent index the applied index:
`mergedCreate_window`'s `ciEff γ st.k = ai`). With the auth mode off: with auth on, the KV log is
the mode-on model's (`kvModelOn`), not the image `srvNet` carries (`srvImage`, mode off), so the
on-mode branch is open (`notes/decisions.md`, "applyAll's merge branch (S1)"). Reach the image only
through this lemma (`srvImage`, `srvImageR` change with the durability work). -/
theorem merged_image (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ai : w64) (A : List EntryModel)
    (x : apply.ApplyKV) (D : backend.Data) (hlen : uint.Z ai = A.length)
    (h0 : γr.kv.c0 = W64 0 ∧ γr.kv.log0 = [[], []]) :
    ⌜mergedObs γr E.cmp ai A x.log D⌝ ∗ isServer s γ ci TM E ρ γr ∗ kvApplied γr.raft γr.kv A x ⊢
      |={⊤}=> kvApplied γr.raft γr.kv A x ∗ □ (srvNet (GF := GF) γr.raft.raft).img ai D := by
  sorry

end proof

end EtcdGrove
end Perennial
