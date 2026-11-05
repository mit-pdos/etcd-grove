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
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyCmpArm

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

/-- **`backend.Snapshot`'s statement before F2's stage 3** (its approved restatement, 2026-11-03:
the observation also handed the batch lock's halves `pvHalf`/`ckHalf`, and `Q` the compaction
keys' values): an instance of today's spec (`Q` ignoring the new argument, the observation
ignoring the new halves), so the restatement only strengthens the axiom. -/
theorem backend.backend.Snapshot.spec_of_specF2
    (h : backend.backend.Snapshot.spec (GF := GF) (hG := hG)) :
    ∀ (γ : backend.BNames) (P : backend.BParams) (W Pk : IProp GF) (b : Loc) (qo : Qp)
      (R : IProp GF)
      (Q : backend.VData → GMap (GoString × GoString) GoString → GMap GoString backend.BktData →
        Prop),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
        backend.isBackend γ P W Pk b ∗ backend.bOpen γ qo ∗ backend.wbTok γ ∗ R ∗
        □ (∀ (vd : backend.VData) (d : GMap (GoString × GoString) GoString)
            (r : GMap GoString backend.BktData),
          R -∗ W -∗ Pk -∗ backend.viewAt γ vd -∗ backend.hkOwn γ d -∗ backend.rbOwn γ r -∗
            ⌜Q vd d r⌝) }}
      (App (Val (b @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty
        @!! go!"Snapshot")) (Val #()))
    {{ (sp : Loc) (D : backend.Data), RET #(interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.storage.backend.snapshot.ty) #sp);
        backend.snapOpen sp D ∗ backend.bOpen γ qo ∗ R ∗ backend.fkRd γ P (D, ⟨∅, W64 0⟩) ∗
        ⌜Q (backend.sData P D) (backend.hkData P D) (backend.rbData P D)⌝ }} := by
  intro γ P W Pk b qo R Q
  iintro %Φ ⟨#Hpkg, #Hb, Ho, Hwb, HR, #HQ⟩ HΦ
  wp_apply h γ P W Pk b qo R (fun vd d r _ => Q vd d r) $$ [Ho Hwb HR]
    as %sp %D ⟨Hsn, Ho, HR, #Hfk, %HQD⟩
  · iframe #; iframe
    iintro !> %vd %d %r %v HR' HW HPk Hv - Hh Hr -
    iapply HQ $$ HR' HW HPk Hv Hh Hr
  iapply HΦ
  iframe Hsn Ho HR Hfk
  ipureintro; exact HQD

/-- **The snapshot contract from the backend's** (`backend.Snapshot.spec`): the real backend `bl`'s
`Snapshot()`, with an open share, a write-back's budget token and the caller's resource `R`, whose
observation `Q` of every commit (with the batch lock's client resource `W` and hooks' `Pk`, and
(F2, stage 4) its halves of the physical view and of the compaction keys' values) is what the
snapshot's data `D` satisfies (as `Q (sData P D) (hkData P D) (rbData P D) (fkVals D)`). -/
theorem srvBeSnapOk_of_backend (hSnap : backend.backend.Snapshot.spec (GF := GF) (hG := hG))
    (γ : backend.BNames) (P : backend.BParams) (W Pk : IProp GF) (bl : Loc) (qo : Qp)
    (R : IProp GF)
    (Q : backend.VData → GMap (GoString × GoString) GoString → GMap GoString backend.BktData →
      backend.FkVals → Prop) (QR : backend.Data → Prop) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      backend.isBackend γ P W Pk bl ∗
      □ (∀ (vd : backend.VData) (d : GMap (GoString × GoString) GoString)
          (r : GMap GoString backend.BktData) (v : backend.FkVals),
        R -∗ W -∗ Pk -∗ backend.viewAt γ vd -∗ backend.pvHalf γ vd -∗ backend.hkOwn γ d -∗
          backend.rbOwn γ r -∗ backend.ckHalf γ v -∗ ⌜Q vd d r v⌝) ∗
      □ (∀ D : backend.Data, R -∗ backend.fkRd γ P (D, ⟨∅, W64 0⟩) -∗ ⌜QR D⌝ ∗ R) ⊢
      srvBeSnapOk
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
          #bl)
        iprop(backend.bOpen γ qo ∗ backend.wbTok γ ∗ R) iprop(backend.bOpen γ qo ∗ R)
        (fun D => Q (backend.sData P D) (backend.hkData P D) (backend.rbData P D)
          (backend.fkVals D) ∧ QR D) := by
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
`W` (`QF`, 2026-11-02: the writer's key observation, `txn.kvWriter_keyObs`; F2, stage 4: with the
batch lock's halves of the physical view and the compaction keys' values, `apply.cmpObs`). -/
theorem snapObs_window (γA : ApplyNames) (γ : backend.BNames) (P : backend.BParams)
    (hP : ciKeys P) (W F : IProp GF) (s : ApplyState) (SR : GoString → Prop)
    (rb : GMap GoString backend.BktData) (SA : GoString → Prop) (ra : GMap GoString backend.BktData)
    (QF : backend.VData → backend.FkVals → Prop) :
    □ (∀ vd v, F -∗ W -∗ backend.viewAt γ vd -∗ backend.pvHalf γ vd -∗ backend.ckHalf γ v -∗
      ⌜QF vd v⌝) ⊢
      □ (∀ (vd : backend.VData) (d : GMap (GoString × GoString) GoString)
          (r : GMap GoString backend.BktData) (v : backend.FkVals),
        iprop(freezeY γA s ∗ iprop(backend.rbOwnIn γ membership.clusterBkts rb ∗
          backend.rbPart γ SR rb ∗ backend.rbPart γ SA ra) ∗ F) -∗ W -∗
          batchLockInv γA (metaTM γ P) -∗
          backend.viewAt γ vd -∗ backend.pvHalf γ vd -∗ backend.hkOwn γ d -∗ backend.rbOwn γ r -∗
          backend.ckHalf γ v -∗ ⌜(ciObs (ciEff γA s.k) d ∧
            (∀ n, (membership.clusterBkts n ∨ SR n) → r.lookup n = rb.lookup n) ∧
            ∀ n, SA n → r.lookup n = ra.lookup n) ∧ QF vd v⌝) := by
  iintro #HQF !> %vd %d %r %v ⟨HY, Hrb, HF⟩ HW Hbl Hv Hpv Hhk Hr Hck
  ihave %hQF := HQF $$ %vd %v HF HW Hv Hpv Hck
  iunfold freezeY at HY
  icases HY with ⟨-, Hmq, -⟩
  iunfold batchLockInv at Hbl
  icases Hbl with ⟨%mm, Hmt, HTM, -⟩
  icombine Hmt Hmq gives %Hm1
  iunfold metaTM at HTM
  icases HTM with ⟨%S, Hk, %HmS⟩
  iunfold backend.hkOwn at Hk Hhk
  icombine Hk Hhk gives %Hd
  -- (2026-11-02, the backend-auth-split stage) the cluster's buckets idle, the others a part:
  -- each agrees with the batch lock's
  icases Hrb with ⟨Hrc, Hrn, Hra⟩
  iunfold backend.rbOwn at Hr
  icases backend.rbOwnIn_agree γ membership.clusterBkts (fun _ => True) rb r $$ [$Hrc $Hr]
    with ⟨-, Hr, %Hr1⟩
  icases backend.rbPart_agree γ SR (fun _ => True) rb r $$ [$Hrn $Hr]
    with ⟨-, Hr, %Hr2⟩
  icases backend.rbPart_agree γ SA (fun _ => True) ra r $$ [$Hra $Hr]
    with ⟨-, -, %Hr3⟩
  have Hrr : ∀ n, (membership.clusterBkts n ∨ SR n) → r.lookup n = rb.lookup n := fun n h =>
    h.elim (fun h => (Hr1 n h trivial).symm) (fun h => (Hr2 n h trivial).symm)
  ipureintro
  obtain ⟨-, Hm1⟩ := Hm1
  obtain ⟨-, Hd⟩ := Hd
  subst Hd
  refine ⟨⟨⟨?_, mm.2, ?_⟩, Hrr, fun n h => (Hr3 n h trivial).symm⟩, hQF⟩
  · rw [backend.hkData_lookup, ciKeys_hk hP (Or.inl rfl)]
    simp only [↓reduceIte]
    rw [HmS.1, Hm1]
  · rw [backend.hkData_lookup, ciKeys_hk hP (Or.inr rfl)]
    simp only [↓reduceIte]
    exact HmS.2

/-- **`s.be.Snapshot()` in the window**: `srvBeSnapOk_of_backend` with the window's observation
(`snapObs_window`): the snapshot's data holds the consistent index `ciEff γA s.k` and the tracked
buckets `rb` (`imageAt_of_snap`'s `hci`, `htm`, `hrb`), and the frame's observation `QF` of its
view (F2, stage 4: and of the compaction keys' values, `QF (sData P D) (fkVals D)`, from the
batch lock's halves `pvHalf`/`ckHalf` the snapshot hands the observation). -/
theorem srvBeSnapOk_window (hSnap : backend.backend.Snapshot.spec (GF := GF) (hG := hG))
    (γA : ApplyNames) (γ : backend.BNames) (P : backend.BParams) (hP : ciKeys P) (W : IProp GF)
    (bl : Loc) (qo : Qp) (s : ApplyState) (S : GoString → Prop) (rb : GMap GoString backend.BktData)
    (SA : GoString → Prop) (ra : GMap GoString backend.BktData) (F : IProp GF)
    (QF : backend.VData → backend.FkVals → Prop) (QR : backend.Data → Prop) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      backend.isBackend γ P W (batchLockInv γA (metaTM γ P)) bl ∗
      □ (∀ vd v, F -∗ W -∗ backend.viewAt γ vd -∗ backend.pvHalf γ vd -∗ backend.ckHalf γ v -∗
        ⌜QF vd v⌝) ∗
      □ (∀ D : backend.Data, F -∗ backend.fkRd γ P (D, ⟨∅, W64 0⟩) -∗ ⌜QR D⌝ ∗ F) ⊢
      srvBeSnapOk
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
          #bl)
        iprop(backend.bOpen γ qo ∗ backend.wbTok γ ∗ (freezeY γA s ∗ iprop(backend.rbOwnIn γ
          membership.clusterBkts rb ∗ backend.rbPart γ S rb ∗ backend.rbPart γ SA ra) ∗ F))
        iprop(backend.bOpen γ qo ∗ (freezeY γA s ∗ iprop(backend.rbOwnIn γ membership.clusterBkts rb ∗
          backend.rbPart γ S rb ∗ backend.rbPart γ SA ra) ∗ F))
        (fun D => ((ciObs (ciEff γA s.k) (backend.hkData P D) ∧
            (∀ n, (membership.clusterBkts n ∨ S n) → (backend.rbData P D).lookup n = rb.lookup n) ∧
            ∀ n, SA n → (backend.rbData P D).lookup n = ra.lookup n) ∧
          QF (backend.sData P D) (backend.fkVals D)) ∧ QR D) := by
  iintro ⟨#Hpkg, #Hb, #HQF, #HQR⟩
  iapply srvBeSnapOk_of_backend hSnap γ P W (batchLockInv γA (metaTM γ P)) bl qo
    iprop(freezeY γA s ∗ iprop(backend.rbOwnIn γ membership.clusterBkts rb ∗
      backend.rbPart γ S rb ∗ backend.rbPart γ SA ra) ∗ F)
    (fun vd d r v => (ciObs (ciEff γA s.k) d ∧
      (∀ n, (membership.clusterBkts n ∨ S n) → r.lookup n = rb.lookup n) ∧
      ∀ n, SA n → r.lookup n = ra.lookup n) ∧ QF vd v) QR
  iframe Hpkg Hb
  isplitl
  rotate_left
  · iintro !> %D ⟨HY, Hrb, HF⟩ Hfk
    ihave ⟨%h, HF⟩ := HQR $$ %D HF Hfk
    iframe HY Hrb HF
    ipureintro; exact h
  iapply snapObs_window γA γ P hP W F s S rb SA ra QF $$ HQF

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
    #Hmu, #Hrmu, #Htmu, #Hcmu, #Hci, #Hmet, #Hdbmu, #Hdb, %Hwf, #Hdbf⟩
  icombine Hh Hh' gives %Heq
  subst Heq
  iunfold backend.isBackendNH
  imodintro
  iexists t, rt, tm, db, lg
  iframe #
  isplitr
  · ipureintro; exact Hlg0
  ipureintro; exact Hwf

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

/-- **The writer's observation of the compaction tracking** (F2, stage 4; in place of
SNAPSHOT-SORRY #7-cmp's `srvBeSnapOk_cmpRecs`): in compaction mode, the KV's sole writer at `log`
(its pin's share of the log tie, `writerPin`), the apply thread's compaction resources at `crev`
(the compaction right's half of the revision tie), the batch lock's resource (`lateWD d`, its
tracking `cmpTrack`) and the backend's halves of the physical view and of the compaction keys'
values (as `backend.Snapshot.spec` hands them to its observer) give the physical cut of `log` at
records `r` of revision `crev`, the keys' values the records' (`mvcc.lateWD_cmpObsP`); the writer,
the right and the lock's resource kept. -/
theorem apply.cmpObs (E : apply.AEnv GF) (d : mvcc.KBReal) (hk : E.γ.kb = some d)
    (hcm : d.cm = true) (log : mvcc.Log) (crev : Int) (vd : backend.VData) (v : backend.FkVals) :
    txn.kvWriter E.s E.γ log ∗ apply.cmpOwn E crev ∗ mvcc.lateWD d ∗
      backend.pvHalf d.γB vd ∗ backend.ckHalf d.γB v ⊢
    txn.kvWriter E.s E.γ log ∗ apply.cmpOwn E crev ∗ mvcc.lateWD d ∗
      ⌜∃ r : mvcc.CmpRecs, mvcc.physCut log r vd ∧
        v = (mvcc.recBytes r.fin, mvcc.recBytes r.sched) ∧ r.crev = crev⌝ := by
  have hon : mvcc.kbCmpM E.γ.kb := by rw [hk]; exact hcm
  have hcr : apply.cmpRight (GF := GF) E crev =
      iprop(mvcc.compactRightR E.s E.γ crev ∗ ⌜-1 ≤ crev⌝) := by
    unfold apply.cmpRight; rw [if_pos hon]
  iintro ⟨Hkw, Hco, HW, Hp, Hc⟩
  iunfold txn.kvWriter at Hkw
  icases Hkw with ⟨Hsw, Hwl, Hfr⟩
  iunfold txn.wlogOwn at Hwl
  icases Hwl with ⟨Hww, Hpin⟩
  iunfold apply.cmpOwn at Hco
  rw [hcr]
  icases Hco with ⟨⟨Hcr, %hc1⟩, Hsup⟩
  icases mvcc.lateWD_cmpObsP E.s E.γ d hk hcm log crev vd v $$ [$Hpin $Hcr $HW $Hp $Hc]
    with ⟨Hpin, Hcr, HW, -, -, %ho⟩
  iframe HW
  isplitl [Hsw Hww Hpin Hfr]
  · iunfold txn.kvWriter
    iframe Hsw Hfr
    iunfold txn.wlogOwn
    iframe Hww Hpin
  isplitl [Hcr Hsup]
  · iunfold apply.cmpOwn
    rw [hcr]
    iframe Hcr Hsup
    ipureintro; exact hc1
  ipureintro; exact ho

/-- **What the window's snapshot observes of the records** (F2, stage 4: `srvBeSnapOk_window`'s
observation of the physical view `vd` and the compaction keys' values `v`, from `apply.cmpObs`):
in compaction mode, the physical cut of `log` at records of revision `crev`, the keys' values the
records'. -/
def apply.windowObs (d : mvcc.KBReal) (log : mvcc.Log) (crev : Int) (vd : backend.VData)
    (v : backend.FkVals) : Prop :=
  d.cm = true → ∃ r : mvcc.CmpRecs, mvcc.physCut log r vd ∧
    v = (mvcc.recBytes r.fin, mvcc.recBytes r.sched) ∧ r.crev = crev

/-- What the window's post then gives, by `mvcc.keyImageM_of_tracked`: the image at the records. -/
theorem apply.windowObs_image (d : mvcc.KBReal) (log : mvcc.Log) (crev : Int) (D : backend.Data)
    (h : apply.windowObs d log crev (backend.sData d.P D) (backend.fkVals D)) :
    d.cm = true → ∃ r : mvcc.CmpRecs, mvcc.keyImageM true log r D ∧ r.crev = crev := by
  intro hc
  obtain ⟨r, hcut, hv, hr⟩ := h hc
  exact ⟨r, mvcc.keyImageM_of_tracked d log r D hcut hv, hr⟩

/-- **What the merged snapshot observes** (S2; #7-cmp's Freeze, 2026-11-02, the user's approval):
the backend's data `D` is the image, by the store's compaction mode `cmp`, of the KV log `log` at
compaction records `r` (`mvcc.keyImageM`: off, the `Key` bucket exactly `log`'s and no compaction
key; on, the entries of `log` the job at `r.crev` has not yet deleted, per key a prefix of the ones
it deletes, and the records), on at the store's compaction revision `crev` (the apply thread's
`x.crev`, Go's `compactMainRev`), the consistent index `ai` and some term in `Meta`, the other
buckets of the committed log `A` (`bkRestAt`), and `log` a well-formed committed log (`IdxWf`):
`imageAt`'s clauses, over the apply thread's KV log in place of the model (`merged_image` relates
them). Off the records are none, so `crev` is not read. (The lease-grant stage, by the cluster's
`lg`:) the other buckets the leased ones (`bkRestAtL`) in a cluster that grants leases. -/
def mergedObs (γr : ReadNames) (cmp lg : Bool) (ai : w64) (A : List EntryModel) (log : mvcc.Log)
    (crev : Int) (D : backend.Data) : Prop :=
  (∃ r : mvcc.CmpRecs, mvcc.keyImageM cmp log r D ∧ (cmp = true → r.crev = crev)) ∧
    backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName
      go_etcd_io.etcd.server.v3.storage.schema.ciKeyBytes = encMeta ai ∧
    (∃ t : w64, backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName
      go_etcd_io.etcd.server.v3.storage.schema.termKeyBytes = encMeta t) ∧
    (if lg then bkRestAtL γr.kv γr.raft.raft.boot (γr.raft.pre ++ A) D
      else bkRestAt γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A) D) ∧ mvcc.IdxWf log []

/-- **The gated rest observation from the snapshot's tracked buckets** (the window at `srvRest`'s
image, either arm). -/
theorem bkRestIf_of_rb {P : backend.BParams} (hRB : ∀ n ∈ restBuckets, P.RB n = true)
    (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (f : w64 → w64) (D : backend.Data)
    (hrb : backend.rbData P D = (apply.restLeasesWith f (srvIds E (appliedTable γr A).ids)
      (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))).bk) :
    if E.lg then bkRestAtL γr.kv γr.raft.raft.boot (γr.raft.pre ++ A) D
    else bkRestAt γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A) D := by
  unfold srvIds at hrb
  cases h : E.lg
  · simp only [h, Bool.false_eq_true, ↓reduceIte, apply.restLeasesWith_nil] at hrb ⊢
    exact bkRestAt_of_rb hRB hrb
  · simp only [h, ↓reduceIte] at hrb ⊢
    exact bkRestAtL_of_rb hRB f hrb

/-- **The rest buckets of `D` the committed log's, of the buckets the rest resource holds in the
mode `M`** (the auth-on snapshot plan's P5, 2026-11-03): `bkRestAt` at the cluster's buckets and
`restSet M`'s, which in `on` leaves out the auth store's (whose contents are the auth realization's,
not the rest model's); with the records of the leases `T` at some TTLs (the lease-grant stage's
`bkRestAtL`; `T` empty in a cluster that grants none). -/
def bkRestAtM (M : auth.AuthMode) (T : List w64) (c0 : w64) (bootLog : List EntryM)
    (L : List EntryModel) (D : backend.Data) : Prop :=
  ∃ f : w64 → w64, ∀ n ∈ restBuckets, (membership.clusterBkts n ∨ restSet M n) →
    D.lookup n = (apply.restLeasesWith f T (restModel c0 bootLog L)).bk.lookup n

/-- **`mergedObs` in the mode `M`** (P5): its rest buckets `bkRestAtM M`, the auth ones left out in
`on`, with the records of the applied log's leases in a cluster that grants them (`lg`); in `off`,
`mergedObs` (`mergedObs_of_M`). -/
def mergedObsM (M : auth.AuthMode) (γr : ReadNames) (cmp lg : Bool) (ai : w64) (A : List EntryModel)
    (log : mvcc.Log) (crev : Int) (D : backend.Data) : Prop :=
  (∃ r : mvcc.CmpRecs, mvcc.keyImageM cmp log r D ∧ (cmp = true → r.crev = crev)) ∧
    backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName
      go_etcd_io.etcd.server.v3.storage.schema.ciKeyBytes = encMeta ai ∧
    (∃ t : w64, backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName
      go_etcd_io.etcd.server.v3.storage.schema.termKeyBytes = encMeta t) ∧
    bkRestAtM M (if lg then (kvLeases γr.kv (γr.raft.pre ++ A)).ids else []) γr.kv.c0
      γr.raft.raft.boot (γr.raft.pre ++ A) D ∧ mvcc.IdxWf log []

theorem mergedObs_of_M {M : auth.AuthMode} (hM : M = .off) {γr : ReadNames} {cmp lg : Bool}
    {ai : w64} {A : List EntryModel} {log : mvcc.Log} {crev : Int} {D : backend.Data}
    (h : mergedObsM M γr cmp lg ai A log crev D) : mergedObs γr cmp lg ai A log crev D := by
  subst hM
  obtain ⟨h1, h2, h3, ⟨f, h4⟩, h5⟩ := h
  have h4' : ∀ n ∈ restBuckets, D.lookup n = (apply.restLeasesWith f
      (if lg then (kvLeases γr.kv (γr.raft.pre ++ A)).ids else [])
      (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))).bk.lookup n :=
    fun n hn => h4 n hn (Classical.em _ |>.elim Or.inl Or.inr)
  refine ⟨h1, h2, h3, ?_, h5⟩
  cases lg
  · simp only [Bool.false_eq_true, ↓reduceIte, apply.restLeasesWith_nil] at h4' ⊢
    exact h4'
  · simp only [↓reduceIte] at h4' ⊢
    exact ⟨f, h4'⟩

/-- **Nothing lent** (`bkLendW` of no bucket): what the merged snapshot's window takes with the auth
mode off. -/
theorem bkLendW_none (E : apply.AEnv GF) :
    ⊢ bkLendW (GF := GF) E (fun _ => False) (fun _ => True) emp := by
  unfold bkLendW
  iintro %d %_
  imodintro
  iexists ∅
  isplitr
  · ipureintro; trivial
  isplitr
  · iapply backend.rbPart_none
  iintro -
  imodintro
  iempintro

/-- **(S2, open) The merged snapshot's window** (`createMergedSnapshotMessage`'s premise): with the
apply thread at the applied index `ai`, its consistent index (`loopOk`, `ciEff γ st.k = ai`) and
its KV at the log `x.log` (the shared row, `srvApplyKVCore`, in either auth mode), two time
receipts and two later credits (for the commit's write token and the snapshot's write-back token), the contracts of
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
    (hlen : uint.Z ai = A.length) (SA : GoString → Prop)
    (QA : GMap GoString backend.BktData → Prop) (RA : IProp GF)
    (hSA : ∀ n, SA n → n ∈ restBuckets) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerM on s γ ci TM E ρ γr ∗ srvKVAddr s ↦□ kv ∗ txn.isKV kv E.s E.γ ∗
      srvWTPool E γp ∗ appliedLogAt γr ai x.log ∗ srvRLogLb γr.raft A ∗ ⧗ 1 ∗ £ 1 ∗ ⧗ 1 ∗ £ 1 ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvApplyKVCore s E γw x ua ∗
      srvRest E γr A ∗ bkLendW E SA QA RA ⊢
    |={⊤}=> ∃ (be : GoInterface) (dq : DFrac) (RC RC' RS RS' : IProp GF),
      srvKVCommitOk kv RC RC' ∗ RC ∗ srvBeAddr s ↦{dq} be ∗
      srvBeSnapOk be RS RS' (fun D => mergedObsM E.authMode γr E.cmp E.lg ai A x.log x.crev D ∧
        ∃ r, QA r ∧ ∀ n, SA n → D.lookup n = r.lookup n) ∗ (RC' -∗ RS) ∗
      (RS' -∗ srvBeAddr s ↦{dq} be ={⊤}=∗ ∃ st' : ApplyState, applyThread γ st' ∗
        applyBackend γ ci b ∗ ciApplying ci a t ∗ srvApplyKVCore s E γw x ua ∗ srvRest E γr A ∗
        RA ∗ ⌜loopOk γ st' ai ∧ ciEff γ st'.k = ciEff γ st.k⌝) := by
  iintro ⟨#Hpkg, #Hsrv, #Hkva, #Hkv, #Hpool, -, -, Hr1, Hl1, Hr2, Hl2, Hst, Hab, Hca, HKV, HRs,
    HL⟩
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
  -- the lent buckets (#7-on: the auth buckets, with auth on)
  iunfold bkLendW at HL
  imod HL $$ %d %hkb with ⟨%ra, %hQA, Hpa, Hlb⟩
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
  ihave #Hnh := isBackendNH_of_hooksAt d.γB d.P (mvcc.lateWD d)
    (batchLockInv γ (metaTM d.γB d.P)) d.be (storage.hooksIface bh) $$ [HB HhkAt]
  · iframe #
  -- the commit's request: the window opened (`storeReq_freeze`)
  ihave #Hreq := storeReq_freeze hOn hSave hPut hUR hID hName hSafe γ ci E.γ d hkb
    (mvcc.lateWD d) bh lgh hcK hhP st hok.1 $$ [Hspkg Hbpkg Hschpkg Hcipkg Hbhk Hnh HB Hci Hinv]
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
  icases Hbo with ⟨%d2, %hd2, Hbe, Hg, HbRO, HbPl⟩
  rw [hkb] at hd2
  obtain rfl := Option.some.inj hd2
  -- two write-backs' tokens
  imod srvWTPool_take_extra_d E γp d _ $$ Hpool Hr1 Hl1 Hg with ⟨Ht1, Hg⟩
  imod srvWTPool_take_extra_d E γp d _ $$ Hpool Hr2 Hl2 Hg with ⟨Ht2, Hg⟩
  ihave Hwt := storeWT_of_wbTok E.γ d hkb $$ Ht1
  -- the rest buckets
  ihave ⟨%f, HRs, HLt, #HGI, HEv⟩ := srvRest_open E γr A $$ HRs
  rw [hRO]
  iunfold srvRestOwnH at HRs
  icases HRs with ⟨Hro, HH⟩
  iunfold srvRestOwn at Hro
  icases Hro with ⟨Hrc, Hrn, Hcl, %Hmi⟩
  ihave Hrb : iprop(backend.rbOwnIn (GF := GF) d.γB membership.clusterBkts
      (apply.restLeasesWith f (srvIds E (appliedTable γr A).ids)
        (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))).bk ∗
    backend.rbPart d.γB (restSet E.authMode)
      (apply.restLeasesWith f (srvIds E (appliedTable γr A).ids)
        (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))).bk ∗
    backend.rbPart d.γB SA ra) $$ [Hrc Hrn Hpa]
  · iframe Hrc Hrn Hpa
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
      iprop(backend.rbOwnIn d.γB membership.clusterBkts
          (apply.restLeasesWith f (srvIds E (appliedTable γr A).ids)
        (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))).bk ∗
        backend.rbPart d.γB (restSet E.authMode)
          (apply.restLeasesWith f (srvIds E (appliedTable γr A).ids)
        (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))).bk ∗
        backend.rbPart d.γB SA ra) ∗
      (txn.kvWriter E.s E.γ x.log ∗ backend.rdTok d.γB d.P d.be ∗
        mvcc.retiredAt E.γ (2 + mvcc.nJobRd E.γ.kb) ∗ apply.cmpOwn E x.crev)))
  iexists iprop(backend.bOpen d.γB backend.rdOpen ∗ (freezeY γ st ∗
      iprop(backend.rbOwnIn d.γB membership.clusterBkts
          (apply.restLeasesWith f (srvIds E (appliedTable γr A).ids)
        (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))).bk ∗
        backend.rbPart d.γB (restSet E.authMode)
          (apply.restLeasesWith f (srvIds E (appliedTable γr A).ids)
        (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))).bk ∗
        backend.rbPart d.γB SA ra) ∗
      (txn.kvWriter E.s E.γ x.log ∗ backend.rdTok d.γB d.P d.be ∗
        mvcc.retiredAt E.γ (2 + mvcc.nJobRd E.γ.kb) ∗ apply.cmpOwn E x.crev)))
  isplitr
  · iapply srvKVCommitOk_of_kv hC kv E.s E.γ (applyThread γ st) (freezeY γ st) emp
    iframe #
  isplitl [Hfr Hwo Hwt Hst]
  · iframe Hfr Hwo Hwt Hst Hreq
  isplitl [Hbe]
  · iexact Hbe
  isplitr
  · -- the snapshot in the window, observing `mergedObs`: on, the records (`apply.cmpObs`)
    iapply srvBeSnapOk_mono _ _ _ _ _ ?_
    rotate_left
    · iapply srvBeSnapOk_window hSnap γ d.γB d.P hcK (mvcc.lateWD d) d.be backend.rdOpen st
        (restSet E.authMode) (apply.restLeasesWith f (srvIds E (appliedTable γr A).ids)
        (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))).bk SA ra
        iprop(txn.kvWriter E.s E.γ x.log ∗ backend.rdTok d.γB d.P d.be ∗
          mvcc.retiredAt E.γ (2 + mvcc.nJobRd E.γ.kb) ∗ apply.cmpOwn E x.crev)
        (fun vd v => ((∀ k v, vd.lookup (mvcc.keyName, k) = some v →
            (mvcc.bucketMap x.log).lookup k = some v) ∧
          (d.cm = false → ∀ k, vd.lookup (mvcc.keyName, k) = (mvcc.bucketMap x.log).lookup k)) ∧
          apply.windowObs d x.log x.crev vd v)
        (fun D => d.cm = false → backend.fkAbsD D)
      iframe Hbpkg HB
      isplitr
      · iintro !> %vd %v ⟨Hkw, -, -, Hcmo⟩ HW Hv Hp Hc
        rcases Bool.eq_false_or_eq_true d.cm with hc | hc
        · icases apply.cmpObs E d hkb hc x.log x.crev vd v $$ [$Hkw $Hcmo $HW $Hp $Hc]
            with ⟨Hkw, -, -, %ho⟩
          ihave %hk := txn.kvWriter_keyObs E.s E.γ d hkb x.log vd $$ [Hkw Hv]
          · iframe
          ipureintro
          exact ⟨hk, fun _ => ho⟩
        · ihave %hk := txn.kvWriter_keyObs E.s E.γ d hkb x.log vd $$ [Hkw Hv]
          · iframe
          ipureintro
          exact ⟨hk, fun h => by rw [hc] at h; cases h⟩
      · iintro !> %D ⟨Hkw, Hrt, Hret, Hcmo⟩ #Hfk
        ihave ⟨%h, Hkw⟩ := txn.kvWriter_noCmp E.s E.γ d hkb x.log (D, ⟨∅, W64 0⟩) $$ [Hkw Hfk]
        · iframe Hkw Hfk
        iframe Hkw Hrt Hret Hcmo
        ipureintro; exact fun hc => (h hc).1
    · intro D ⟨⟨⟨hciO, hrbD, hraD⟩, ⟨_, hex⟩, hwo⟩, hnc⟩
      have hrec := apply.windowObs_image d x.log x.crev D hwo
      have hsd : ∀ k, (backend.sData d.P D).lookup (mvcc.keyName, k) =
          backend.dget D mvcc.keyName k := fun k => by
        rw [backend.sData_lookup]; simp [mvcc.KBReal.P]
      obtain ⟨hci1, t1, ht1⟩ := hciO
      rw [backend.hkData_lookup, ciKeys_hk hcK (Or.inl rfl)] at hci1
      rw [backend.hkData_lookup, ciKeys_hk hcK (Or.inr rfl)] at ht1
      have hrest : bkRestAtM E.authMode (if E.lg then (kvLeases γr.kv (γr.raft.pre ++ A)).ids else [])
          γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A) D := by
        refine ⟨f, fun n hn hs => ?_⟩
        have := hrbD n hs
        simp only [backend.rbData_lookup, hRB n hn, ↓reduceIte] at this
        unfold srvIds appliedTable at this
        exact this
      refine ⟨⟨?_, ?_, ⟨t1, by simpa using ht1⟩, hrest, Hwf⟩, ra, hQA, fun n h => ?_⟩
      · cases hc : E.cmp
        · -- off: the whole bucket and no compaction key, no record
          have hdc : d.cm = false := hcm.trans hc
          refine ⟨mvcc.CmpRecs.empty, (mvcc.keyImageM_off _ _ D).2 ⟨?_, rfl⟩, fun h => by cases h⟩
          refine ⟨fun k => ?_, (mvcc.noCmpData_of_fkAbsD (hnc hdc)).1,
            (mvcc.noCmpData_of_fkAbsD (hnc hdc)).2⟩
          rw [← hsd]; exact hex hdc k
        · obtain ⟨r, hr, hrc⟩ := hrec (hcm.trans hc)
          exact ⟨r, hr, fun _ => hrc⟩
      · rw [← hci]; simpa using hci1
      · have := hraD n h
        simp only [backend.rbData_lookup, hRB n (hSA n h), ↓reduceIte] at this
        exact this
  isplitl [Hsw Hwl Ht2 Hrb Hcmo]
  · iintro ⟨Hfr, Hwo, HY, -⟩
    iunfold mvcc.writerOwn at Hwo
    icases Hwo with ⟨Hrt, Hret⟩
    rw [hRT]
    icases Hrt with ⟨Hrdt, Hop⟩
    iframe Hop Ht2 HY Hrb Hrdt Hret Hcmo
    iunfold txn.kvWriter
    iframe
  · iintro ⟨Hop, HY, Hrb, Hkw, Hrdt, Hret, Hcmo⟩ Hbe
    icases Hrb with ⟨Hrc, Hrn, Hpa⟩
    imod Hlb $$ Hpa with HRA
    imod unfreeze γ st $$ Hinv HY with Hst
    imodintro
    iexists st
    iframe Hst Hab Hca
    isplitl [Hua Hub Hcmo Hsr Hll Hrd Hkw Hrdt Hret Hop Hra Hw Hbe Hg HbRO HbPl]
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
      isplitl [Hbe Hg HbRO HbPl]
      · iunfold srvBeOwn
        iexists d
        iframe Hbe Hg HbRO HbPl
        ipureintro; exact hkb
      isplitl [Hra]
      · iexact Hra
      iexact Hw
    isplitl [Hrc Hrn Hcl HH HLt HEv]
    · iapply srvRest_close
      iframe HLt HGI HEv
      iexists f
      rw [hRO]
      iunfold srvRestOwnH
      iframe HH
      iunfold srvRestOwn
      iframe Hrc Hrn Hcl
      ipureintro; exact Hmi
    isplitl [HRA]
    · iexact HRA
    ipureintro; exact ⟨hok, rfl⟩

/-- **(S2) The merged snapshot's image** (the network's image certificate, `srvNet`'s `img`, which
the bundle carries), in either compaction mode (#7-cmp's Freeze, 2026-11-02, the user's approval: in
place of the mode-off `merged_image` and the false `merged_image_cmp`): an observation `mergedObs`
at the applied index `ai` of the applied log `A` (`kvApplied`: the KV log the model's, `kvModel`,
the compaction revision the model's, `crevOf`), by the store's mode at the apply thread's compaction
revision, and the KV log's receipt (the sole writer's `idxCert`, `idxCert_rcpt`), of the server
with the KV's start values (`isServerApplyAll`'s). The image is `srvImage` of the apply thread's KV
names: `mergedObs`'s key image is `imageAt`'s at the KV names' mode (`srvKVInvs`'s tie), its records
at `crevOf` (on, `kvApplied`'s; off, none, the committed log having no compaction, `crevOf_offM`),
its `Meta` and rest clauses the rest of `imageAt`; the KV invariant gives the start chain
(`kvInv_ch0_off`), the raft log's invariant the fresh start's names (`srvRaftLogInv_fresh`). The
image is exact at `ai` (`mergedCreate_window`'s `ciEff γ st.k = ai`). With the auth mode off; with
auth on, `merged_imageOn` (`MergedImageOn.lean`). Reach the image only through these lemmas. -/
theorem merged_image (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ai : w64) (A : List EntryModel)
    (x : apply.ApplyKV) (D : backend.Data) (hlen : uint.Z ai = A.length)
    (h0 : γr.kv.c0 = W64 0 ∧ γr.kv.log0 = [[], []]) :
    ⌜mergedObs γr E.cmp E.lg ai A x.log x.crev D⌝ ∗ ⧖ (mvcc.logCh x.log) ∗ isServer s γ ci TM E ρ γr ∗
      kvApplied γr.raft γr.kv A x ⊢
      |={⊤}=> kvApplied γr.raft γr.kv A x ∗ □ (srvNet (GF := GF) γr.raft.raft).img ai D := by
  iintro ⟨%hobs, #Hrc, #Hsrv, Hka⟩
  obtain ⟨⟨r, hkI, hr⟩, hci, hterm, hrest, hwf⟩ := hobs
  iunfold isServer at Hsrv
  icases Hsrv with ⟨-, -, -, Hat, -, -⟩
  iunfold srvAtomics at Hat
  icases Hat with ⟨-, -, Hki⟩
  iunfold srvKVInvs at Hki
  icases Hki with ⟨#Hki, -, #Hrl, -, %Hcm, %Hlgk, -⟩
  ihave %hraft := srvRaftLogInv_fresh γr.raft $$ Hrl
  imod (kvInv_ch0_off γr.raft γr.kv) $$ Hki with %hch
  imod (kvInv_authOn γr.raft γr.kv) $$ Hki with %hao
  iunfold kvApplied at Hka
  icases Hka with ⟨Hka, %hx⟩
  iunfold kvAppliedL at Hka
  icases Hka with ⟨#HA, Hhi, Hcert, %hlog⟩
  imod crevOf_offM γr.raft γr.kv A $$ Hki Hrl HA with %Hoff
  imod kv_log_plain γr.raft γr.kv A $$ Hki Hrl HA with %Hpl0
  imodintro
  isplitl [Hhi Hcert]
  · iunfold kvApplied
    iunfold kvAppliedL
    iframe HA Hhi Hcert
    ipureintro; exact ⟨hlog, hx⟩
  ihave #HA' : srvRLogLb (GF := GF) ⟨γr.raft.raft, [], W64 0⟩ A $$ []
  · rw [← hraft]; iexact HA
  iintro !>
  simp only [srvNet]
  rw [hao, srvImageM_off]
  iapply (srvImage_of_dbImage (γk := γr.kv) h0.1 hch h0.2)
  iunfold dbImage
  iexists A
  iframe HA'
  rw [← hlog]
  iframe Hrc
  ipureintro
  have hpre : γr.raft.pre = [] := by rw [hraft]
  have hz : uint.Z (W64 0) = 0 := rfl
  rw [hlog] at hkI hwf
  have hrc : r.crev = crevOf γr.kv A := by
    cases hc : E.cmp
    · rw [hc] at hkI
      obtain ⟨-, rfl⟩ := (mvcc.keyImageM_off _ _ D).1 hkI
      rw [mvcc.CmpRecs.crev_empty]; exact (Hoff (Hcm.1.trans hc)).symm
    · rw [hr hc, hx.2]
  refine ⟨by simp only []; omega, ⟨⟨r, ?_, hrc⟩, hci, hterm, ?_, hwf⟩⟩
  · rw [Hcm.1]; exact hkI
  · cases hlg : E.lg
    · -- (the lease-grant stage) a cluster that grants none: its log grants nothing, the plain image
      rw [hlg] at hrest
      simp only [Bool.false_eq_true, ↓reduceIte] at hrest
      have hpl : plainLogM γr.kv.cmp .none A := by
        have := Hpl0.1
        rw [Hlgk.2, apply.AEnv.lm_of_lg_false hlg] at this
        exact this
      have hn : (kvLeases γr.kv (γr.raft.pre ++ A)).ids = [] := by
        rw [hpre, List.nil_append]; unfold kvLeases; rw [kvTableOf_plainM _ _ _ A hpl]; rfl
      simpa [hpre] using bkRestAtL_of_nil hn hrest
    · rw [hlg] at hrest
      simpa [hpre] using hrest

end proof

end EtcdGrove
end Perennial
