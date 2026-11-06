/-
**`applyAll`'s `msgSnapC` branch: the sender's backend and store contracts** (D22 S-h, 2026-10-20;
`notes/decisions.md`, "D22 S-h carried out"). Lean-first (no Rocq counterpart).

(2026-10-31, S1) The branch is live again: `msgSnapC` carries raft's `MsgSnap`s (`isRNMsgSnapC`'s
`rnSnapMsg`), which `applyAll` merges with the backend's image when the guard holds
(`notes/decisions.md`, "The merged snapshot's index guard"). This file has what the branch's proof
uses beside `SnapCert.lean`'s `srv_merged_sent`: the bag's nonblocking receive
(`chanBag_nbRecv`), the conf states' agreement (`csPts_agree`), the merged message as the network's
snapshot bundle (`srvMerged_bundle`), the snapshot window (`mergedCreate_window`, the contracts
`createMergedSnapshotMessage` takes of `s.KV().Commit()` and `s.be.Snapshot()`, the snapshot's
image `mergedImg`) and the image (`merged_image`, as the network's image certificate). (2026-10-27
to 2026-10-31 the branch was dead, `rnSnapMsg` `False`; until 2026-10-27 this file proved it from
raft's internals, `snapBranch_send`, deleted with the port onto raft's node API.) The rest are the
sender's contract of `s.KV().Commit()` (`srvKVCommitOk_of_kv`) and the stored-index window
(`commitReq_freeze`, `snapObsA`). (Strict M1, 2026-11-06: over mvcc's API, `KV.Commit.contract` and
`mvccImage_snapshot.law` at the writer's update (`KVStoreLaws.snapImageG`), compacting stores
included; until then over the sole writer, `backend.Snapshot`'s view and SNAPSHOT-SORRY #7-cmp.)
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBuild
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvSnapSend
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__createMergedSnapshotMessage
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__sendMergedSnap
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__Snapshot
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVStoreLaws
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



/-- **`s.KV().Commit()`'s contract from the API's** (strict M1, 2026-11-06: `KV.Commit.contract` at
the KV's dynamic type, `shapes.law`; until then `store.Commit` over the store's sole writer): for
the thread's token, a share of the store's backend, a request `X ⇒ Y` the storage serves
(`storageReq`) and a frame `F`. -/
theorem srvKVCommitOk_of_kv [mvccSem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (kv : GoInterface) (γ : mvcc.api.MvccName) (q : Qp) (B : mvcc.api.MvccStorage)
    (Pk X Y F : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      □ mvcc.api.isMvcc kv γ ⊢
      srvKVCommitOk kv
        iprop(threadTok ∗ mvcc.api.mvccBackend γ q B Pk ∗ X ∗ mvcc.api.storageReq B Pk X Y ∗ F)
        iprop(threadTok ∗ mvcc.api.mvccBackend γ q B Pk ∗ Y ∗ F) := by
  iintro ⟨#Hpkg, #Hkv⟩
  ihave %Hsh := hsh.1 kv γ $$ Hkv
  obtain ⟨ty, v, rfl, -, -, -, -, -, -, -, -, hC, -⟩ := Hsh
  iunfold srvKVCommitOk
  iexists ⟨ty, v⟩
  isplitr
  · ipureintro; rfl
  iintro %Φ !> ⟨Ht, Hb, HX, #Hrq, HF⟩ HΦ
  iapply (hC γ q B Pk X Y) $$ [Ht Hb HX]
  · iframe #; iframe
  iintro !> ⟨Ht, Hb, HY⟩
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



/-- What the snapshot's observation finds of the committed meta keys in the window at `k`: the
consistent index `k` and some term. -/
def ciObs (k : w64) (d : GMap (GoString × GoString) GoString) : Prop :=
  d.lookup (go_etcd_io.etcd.server.v3.storage.schema.metaName,
      go_etcd_io.etcd.server.v3.storage.schema.ciKeyBytes) = encMeta k ∧
    ∃ t : w64, d.lookup (go_etcd_io.etcd.server.v3.storage.schema.metaName,
      go_etcd_io.etcd.server.v3.storage.schema.termKeyBytes) = encMeta t

/-- **The snapshot's observation in the window** (`mvccImage_snapshot.law`'s `Q`; strict M1,
2026-11-06: over the API's snapshot, which hands the observation the batch lock's invariant `Pk`, the
hook keys and the tracked buckets, no view; until then `snapObs_window`, over `backend.Snapshot`'s
view and the batch lock's client resource): with the server's batch-lock resource as the hooks'
(`batchLockInv`), the window's `freezeY γA s` and the apply thread's half of the tracked buckets at
`rb`, a commit's hook keys hold `ciEff γA s.k` (`ciObs`; `s.k` itself unless `ci` is 0, then the
keys the backend was opened with) and its tracked buckets are `rb`. -/
theorem snapObsA (γA : ApplyNames) (γ : backend.BNames) (P : backend.BParams) (hP : ciKeys P)
    (s : ApplyState) (rb : GMap GoString backend.BktData) :
    ⊢ □ (∀ (d : GMap (GoString × GoString) GoString) (r : GMap GoString backend.BktData),
        iprop(freezeY γA s ∗ iprop(backend.rbOwnIn γ membership.clusterBkts rb ∗
          backend.rbPart γ (fun n => ¬ membership.clusterBkts n) rb)) -∗
          batchLockInv (GF := GF) γA (metaTM γ P) -∗ backend.hkOwn γ d -∗ backend.rbOwn γ r -∗
          ⌜ciObs (ciEff γA s.k) d ∧ r = rb⌝) := by
  iintro !> %d %r ⟨HY, Hrb⟩ Hbl Hhk Hr
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
  icases Hrb with ⟨Hrc, Hrn⟩
  iunfold backend.rbOwn at Hr
  icases backend.rbOwnIn_agree γ membership.clusterBkts (fun _ => True) rb r $$ [$Hrc $Hr]
    with ⟨-, Hr, %Hr1⟩
  icases backend.rbPart_agree γ (fun n => ¬ membership.clusterBkts n) (fun _ => True) rb r $$ [$Hrn $Hr]
    with ⟨-, -, %Hr2⟩
  have Hrr : rb = r := GMap.ext fun n => by
    by_cases h : membership.clusterBkts n
    · exact Hr1 n h trivial
    · exact Hr2 n h trivial
  ipureintro
  obtain ⟨-, Hm1⟩ := Hm1
  obtain ⟨-, Hd⟩ := Hd
  subst Hd
  refine ⟨⟨?_, mm.2, ?_⟩, Hrr.symm⟩
  · rw [backend.hkData_lookup, ciKeys_hk hP (Or.inl rfl)]
    simp only [↓reduceIte]
    rw [HmS.1, Hm1]
  · rw [backend.hkData_lookup, ciKeys_hk hP (Or.inr rfl)]
    simp only [↓reduceIte]
    exact HmS.2

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

/-- **What the merged snapshot's data is** (persistent; strict M1, 2026-11-06, in place of the
pure `mergedObs` over mvcc's internal key image): the image, by mvcc's `mvccImage`, of the apply
thread's KV history `log` at its compaction revision `crev` (from `mvccImage_snapshot.law` at the
writer's state, `snapImageG`; compacting stores included), and the server's parts at the applied
index `ai` of the committed log `A` (`imageRestAt`: the consistent index `ai` and some term in
`Meta`, the other buckets `bkRestAt`), and the writer's state reachable, its history short
(`imageStOk`, `writer_facts`: what the receiver's `Restore` takes). `merged_image` turns it into the network's certificate. -/
def mergedImg (γr : ReadNames) (ai : w64) (A : List EntryModel) (log : mvcc.Log) (crev : Int)
    (D : backend.Data) : IProp GF :=
  iprop(⌜imageRestAt γr.kv γr.raft.raft.boot ai (γr.raft.pre ++ A) D ∧
      imageStOk log crev⌝ ∗
    ∃ u : Bool, mvcc.api.mvccImage D log crev u)

instance mergedImg_persistent (γr : ReadNames) (ai : w64) (A : List EntryModel) (log : mvcc.Log)
    (crev : Int) (D : backend.Data) : Persistent (mergedImg (GF := GF) γr ai A log crev D) := by
  unfold mergedImg; infer_instance

/-- **The store invariant of a server, in either auth mode** (`srvKVInvs`', `srvKVInvsOn`'s), with
its witness and permit persistent and timeless (`envWitOk`). -/
theorem isServerM_kvStoreInv (on : Bool) (s : Loc) (γ : ApplyNames) (ci : Loc)
    (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) :
    isServerM (GF := GF) on s γ ci TM E ρ γr ⊢
      □ srvApi.kvStoreInvG E.kv E.γ E.Nx E.Cp E.γs ∗ ⌜envWitOk E⌝ := by
  iintro #H
  iunfold isServerM at H
  icases H with ⟨-, -, -, #Hat, -⟩
  iunfold srvAtomicsM at Hat
  icases Hat with ⟨-, -, #Hk⟩
  cases on
  · iunfold srvKVInvsM at Hk
    iunfold srvKVInvs at Hk
    icases Hk with ⟨-, -, -, #Hk, %Hw, -⟩
    iframe Hk
    ipureintro; exact Hw.2.2.1
  · iunfold srvKVInvsM at Hk
    icases Hk with ⟨#Hk, -⟩
    iunfold srvKVInvsOn at Hk
    icases Hk with ⟨-, -, -, -, #Hk, %Hw, -⟩
    iframe Hk
    ipureintro; exact Hw.1

/-- **(S2) The merged snapshot's window** (`createMergedSnapshotMessage`'s premise): with the
apply thread at the applied index `ai`, its consistent index (`loopOk`, `ciEff γ st.k = ai`), its
KV at the log `x.log` (the shared row, `srvApplyKVCore`, in either auth mode), the store invariant,
its thread's token (the commit's), a time receipt and a later credit (the snapshot's write-back
token), the contracts of `s.KV().Commit()` (`srvKVCommitOk`, over the API's `KV.Commit.contract`)
and `s.be.Snapshot()` (`srvBeSnapOk`, over the API's `mvccImage_snapshot.law` at the writer's update,
`snapImageG`) with the window's resources (`RC`, the commit's `RC'` giving the snapshot's `RS`; D22
the stored-index window: `commitReq_freeze`, `snapObsA`); once the snapshot is taken (`RS'`, its
observation `Qd D`, `s.be` back), the apply thread's resources again, at a state of the same
consistent index, with the snapshot's image `mergedImg` at the apply thread's history and
compaction revision. (Strict M1, 2026-11-06: in place of the proof over mvcc's internals, the sole
writer's key observation and SNAPSHOT-SORRY #7-cmp's records; compacting stores covered.) -/
theorem mergedCreate_window
    [mvccSem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hPers : mvcc.api.persistent.law (GF := GF))
    (hReach : mvcc.api.mvccState_reachable.law (GF := GF))
    (hImg : mvcc.api.mvccImage_snapshot.law (GF := GF) (hG := hG))
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
    (hok : loopOk γ st ai) (hci : ciEff γ st.k = ai) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerM on s γ ci TM E ρ γr ∗ srvKVAddr s ↦□ kv ∗ □ mvcc.api.isMvcc kv E.γ ∗
      srvWTPool E γp ∗ ⧗ 1 ∗ £ 1 ∗ threadTok ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvApplyKVCore s E γw x ua ∗
      srvRest E γr A ⊢
    |={⊤}=> ∃ (be : GoInterface) (dq : DFrac) (RC RC' RS RS' : IProp GF)
        (Qd : backend.Data → IProp GF),
      srvKVCommitOk kv RC RC' ∗ RC ∗ srvBeAddr s ↦{dq} be ∗
      srvBeSnapOk be RS RS' Qd ∗ (RC' -∗ RS) ∗
      (∀ D : backend.Data, RS' -∗ Qd D -∗ srvBeAddr s ↦{dq} be ={⊤}=∗ ∃ st' : ApplyState,
        threadTok ∗ applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗
        srvApplyKVCore s E γw x ua ∗ srvRest E γr A ∗ mergedImg γr ai A x.log x.crev D ∗
        ⌜loopOk γ st' ai ∧ ciEff γ st'.k = ciEff γ st.k⌝) := by
  haveI := srvApi.kvStoreInvG_persistent hPers E.kv E.γ E.Nx E.Cp E.γs
  iintro ⟨#Hpkg, #Hsrv, #Hkva, #Hkv, #Hpool, Hr1, Hl1, Ht, Hst, Hab, Hca, HKV, HRs⟩
  ihave ⟨#Hks, %Hwit⟩ := isServerM_kvStoreInv on s γ ci TM E ρ γr $$ Hsrv
  obtain ⟨hw1, hw2, hw3, hw4⟩ := Hwit
  -- the server's backend, its hooks and the protocol (`srvBeHooked`, `srvEnvOk`, `isServerCI`)
  iunfold isServerM at Hsrv
  icases Hsrv with ⟨-, #HCI, ⟨%v, #Hf⟩, -⟩
  iunfold srvFieldsAtM at Hf
  icases Hf with ⟨-, -, -, -, -, %Henv, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hbh⟩
  iunfold srvBeHooked at Hbh
  icases Hbh with ⟨%B, %bh, %lgh, %gx, %Hd, -, #Hbhk, #HhkAt, #HB⟩
  obtain ⟨hBT, hcK, hhP, hPk⟩ := Hd
  obtain ⟨-, -, γB, H, hRO, -, B', al, stl, lp, hBT', hγB, -⟩ := Henv
  have hBB' : B' = B := srvBkTie_inj B' B (hBT'.symm.trans hBT)
  subst B γB
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
  ihave #Hnh := isBackendNH_of_hooksAt B'.γB B'.P (mvcc.api.mvccW gx)
    (batchLockInv γ (metaTM B'.γB B'.P)) B'.be (storage.hooksIface bh) $$ [HB HhkAt]
  · iframe #
  -- the commit's request: the window opened (`commitReq_freeze`)
  ihave #Hreq := commitReq_freeze hOn hSave hPut hUR hID hName hSafe γ ci B'.γB B'.P
    (mvcc.api.mvccW gx) B'.be bh lgh hcK hhP st hok.1
    $$ [Hspkg Hbpkg Hschpkg Hcipkg Hbhk Hnh HB Hci Hinv]
  · iframe #
  -- the apply thread's KV resources
  iunfold srvApplyKVCore at HKV
  icases HKV with ⟨Hua, #Hap, Hakv, Hbo, Hra, Hw⟩
  iunfold apply.applyKV at Hakv
  icases Hakv with ⟨%p, %Hp, Hub, Hko, Hcmo⟩
  iunfold apply.kvOwn at Hko
  icases Hko with ⟨⟨%c, Hws⟩, Hkb, Hll, Hrd⟩
  iunfold apply.kvBk at Hkb
  icases Hkb with ⟨%B2, HmB, #Hhi, HtB⟩
  ihave %HB2 : ⌜B2 = B'⌝ $$ [HtB]
  · rw [hBT]; iunfold srvBkTie at HtB; iexact HtB
  subst B2
  iunfold apply.cmpOwn at Hcmo
  icases Hcmo with ⟨Hop, Hcr⟩
  -- the writer's half at the apply thread's compaction revision
  iunfold srvApi.wSt at Hws
  icases Hws with ⟨Hws1, Hws2⟩
  iunfold srvApi.crOwn at Hcr
  icombine Hws2 Hcr gives %Hcc
  have hc : c = x.crev := Hcc.2
  subst hc
  ihave Hws : srvApi.wSt (GF := GF) E.γs x.log x.crev $$ [Hws1 Hws2]
  · iunfold srvApi.wSt; iframe Hws1 Hws2
  iunfold srvBeOwn at Hbo
  icases Hbo with ⟨%d, %hd, Hbe, Hg, #HbRO, HbPl, Hrt⟩
  have hdB : d = B' := srvBkTie_inj d B' (hd.symm.trans hBT)
  subst B'
  iunfold apply.bkRT at Hrt
  icases Hrt with ⟨Hrdt, Hopn⟩
  -- the snapshot's write-back token
  imod srvWTPool_take_extra_d E γp d _ $$ Hpool Hr1 Hl1 Hg with ⟨Ht1, Hg⟩
  -- the rest buckets
  iunfold srvRest at HRs
  rw [hRO]
  iunfold srvRestOwnH at HRs
  icases HRs with ⟨Hro, HH⟩
  iunfold srvRestOwn at Hro
  icases Hro with ⟨Hrc, Hrn, Hcl, %Hmi⟩
  ihave Hrb : iprop(backend.rbOwnIn (GF := GF) d.γB membership.clusterBkts
      (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)).bk ∗
    backend.rbPart d.γB (fun n => ¬ membership.clusterBkts n)
      (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)).bk) $$ [Hrc Hrn]
  · iframe Hrc Hrn
  have hRB : ∀ n ∈ restBuckets, d.P.RB n = true := fun n hn => by
    simp [mvcc.KBReal.P, hn]
  have hPkd : E.Pk d = batchLockInv γ (metaTM d.γB d.P) := hPk
  imodintro
  iexists srvBeIface d.be, DFrac.own (1 : Qp).half
  iexists iprop(threadTok ∗ mvcc.api.mvccBackend E.γ 1 (mvcc.api.etcdStorage d) (E.Pk d) ∗
      applyThread γ st ∗
      mvcc.api.storageReq (mvcc.api.etcdStorage d) (E.Pk d) (applyThread γ st) (freezeY γ st) ∗ emp)
  iexists iprop(threadTok ∗ mvcc.api.mvccBackend E.γ 1 (mvcc.api.etcdStorage d) (E.Pk d) ∗
      freezeY γ st ∗ emp)
  iexists iprop(threadTok ∗ (mvcc.api.mvccBackend E.γ 1 (mvcc.api.etcdStorage d) (E.Pk d) ∗
      backend.bOpen d.γB backend.rdOpen ∗ backend.wbTok d.γB ∗
      (freezeY γ st ∗ iprop(backend.rbOwnIn d.γB membership.clusterBkts
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)).bk ∗
        backend.rbPart d.γB (fun n => ¬ membership.clusterBkts n)
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)).bk)) ∗
      srvApi.wSt E.γs x.log x.crev))
  iexists iprop(threadTok ∗ (backend.bOpen d.γB backend.rdOpen ∗
      (freezeY γ st ∗ iprop(backend.rbOwnIn d.γB membership.clusterBkts
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)).bk ∗
        backend.rbPart d.γB (fun n => ¬ membership.clusterBkts n)
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)).bk)) ∗
      mvcc.api.mvccBackend E.γ 1 (mvcc.api.etcdStorage d) (E.Pk d)))
  iexists (fun D : backend.Data =>
    iprop(srvApi.wSt (GF := GF) E.γs x.log x.crev ∗ mergedImg γr ai A x.log x.crev D))
  isplitr
  · iapply srvKVCommitOk_of_kv hsh kv E.γ 1 (mvcc.api.etcdStorage d) (E.Pk d)
      (applyThread γ st) (freezeY γ st) emp
    iframe #
  isplitl [Ht HmB Hst]
  · iframe Ht HmB Hst
    rw [mvcc.api.etcdStorage_req, hPkd]
    iframe Hreq
  isplitl [Hbe]
  · iexact Hbe
  isplitr
  · -- the snapshot in the window, at the writer's update (`snapImageG`)
    iunfold srvBeSnapOk
    iexists ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty, #d.be⟩
    isplitr
    · ipureintro; rfl
    iintro %Φ !> ⟨Ht, HmB, Ho, Hwb, HR, Hws⟩ HΦ
    wp_apply (srvApi.snapImageG hPers hReach hImg hSnap E.Nx E.Cp E.kv E.γ E.γs x.log x.crev d (E.Pk d)
        backend.rdOpen
        iprop(freezeY γ st ∗ iprop(backend.rbOwnIn d.γB membership.clusterBkts
            (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)).bk ∗
          backend.rbPart d.γB (fun n => ¬ membership.clusterBkts n)
            (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)).bk))
        (fun dd r => ciObs (ciEff γ st.k) dd ∧
          r = (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)).bk))
      $$ [HmB Ho Hwb HR Hws]
      as %sp %D ⟨Hsn, Ho, HR, HmB, Hws, %HQD, %Hre, %u, #Him⟩
    · iframe #; iframe HmB Ho Hwb HR Hws
      rw [hPkd]
      iintro !> %dd %r HR' HPk Hhk Hrb'
      iapply (snapObsA γ d.γB d.P hcK st
        (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)).bk) $$ HR' HPk Hhk Hrb'
    iapply HΦ
    simp only []
    iframe Hsn Ht Ho HR HmB Hws
    iunfold mergedImg
    isplitr
    · ipureintro
      unfold imageRestAt
      obtain ⟨⟨hci1, t1, ht1⟩, hrbD⟩ := HQD
      rw [backend.hkData_lookup, ciKeys_hk hcK (Or.inl rfl)] at hci1
      rw [backend.hkData_lookup, ciKeys_hk hcK (Or.inr rfl)] at ht1
      exact ⟨⟨by rw [← hci]; simpa using hci1, ⟨t1, by simpa using ht1⟩, bkRestAt_of_rb hRB hrbD⟩,
        Hre⟩
    iexists u; iexact Him
  isplitl [Hopn Ht1 Hrb Hws]
  · iintro ⟨Ht, HmB, HY, -⟩
    iframe Ht HmB Hopn Ht1 HY Hrb Hws
  · iintro %D ⟨Ht, Hopn, ⟨HY, Hrb⟩, HmB⟩ ⟨Hws, #Hmi⟩ Hbe
    imod unfreeze γ st $$ Hinv HY with Hst
    imodintro
    iexists st
    iframe Ht Hst Hab Hca Hmi
    isplitl [Hua Hub Hop Hcr Hws Hll Hrd HmB Hrdt Hopn Hra Hw Hbe Hg HbPl]
    · iunfold srvApplyKVCore
      isplitl [Hua]
      · iexact Hua
      isplitr
      · iexact Hap
      isplitl [Hub Hop Hcr Hws Hll Hrd HmB]
      · iunfold apply.applyKV
        iexists p
        iframe Hub
        isplitr
        · ipureintro; exact Hp
        isplitl [Hws Hll Hrd HmB]
        · iunfold apply.kvOwn
          iframe Hll Hrd
          isplitl [Hws]
          · iexists x.crev
            iexact Hws
          iunfold apply.kvBk
          iexists d
          iframe HmB Hhi
          rw [hBT]
          iunfold srvBkTie
          ipureintro; rfl
        iunfold apply.cmpOwn
        iframe Hop
        iunfold srvApi.crOwn
        iexact Hcr
      isplitl [Hbe Hg HbPl Hrdt Hopn]
      · iunfold srvBeOwn
        iexists d
        iframe Hbe Hg HbRO HbPl
        isplitr
        · ipureintro; exact hd
        iunfold apply.bkRT
        iframe Hrdt Hopn
      isplitl [Hra]
      · iexact Hra
      iexact Hw
    isplitl [Hrb Hcl HH]
    · iunfold srvRest
      rw [hRO]
      iunfold srvRestOwnH
      iframe HH
      iunfold srvRestOwn
      icases Hrb with ⟨Hrc, Hrn⟩
      iframe Hrc Hrn Hcl
      ipureintro; exact Hmi
    ipureintro; exact ⟨hok, rfl⟩

/-- **(S2) The merged snapshot's image** (the network's image certificate, `srvNet`'s `img`, which
the bundle carries): the snapshot's image `mergedImg` at the applied index `ai` of the applied log
`A`, at the apply thread's history and compaction revision, which `kvApplied` ties to the model's
(`kvModel`, `crevOf`), of the server with the KV's start values (`isServerApplyAll`'s): `dbImage`
at the fresh cluster's start (the raft log's invariant's names, `srvRaftLogInv_fresh`; the KV
invariant's start chain, `kvInv_ch0_off`), so the network's `srvImage`. (Strict M1, 2026-11-06:
the image is mvcc's `mvccImage`, in either compaction mode; until then `mergedObs`'s key image by
the store's mode and the sole writer's receipt.) With the auth mode off: with auth on, the KV log
is the mode-on model's (`kvModelOn`), not the image `srvNet` carries, so the on-mode branch is open
(#7-on). Reach the image only through this lemma. -/
theorem merged_image (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ai : w64) (A : List EntryModel)
    (x : apply.ApplyKV) (D : backend.Data) (hlen : uint.Z ai = A.length)
    (h0 : γr.kv.c0 = W64 0 ∧ γr.kv.log0 = [[], []]) :
    mergedImg γr ai A x.log x.crev D ∗ isServer s γ ci TM E ρ γr ∗
      kvApplied γr.raft γr.kv A x ⊢
      |={⊤}=> kvApplied γr.raft γr.kv A x ∗ □ (srvNet (GF := GF) γr.raft.raft).img ai D := by
  iintro ⟨#Hmi, #Hsrv, Hka⟩
  iunfold isServer at Hsrv
  icases Hsrv with ⟨-, -, -, Hat, -, -⟩
  iunfold srvAtomics at Hat
  icases Hat with ⟨-, -, Hki⟩
  iunfold srvKVInvs at Hki
  icases Hki with ⟨#Hki, -, #Hrl, -⟩
  ihave %hraft := srvRaftLogInv_fresh γr.raft $$ Hrl
  imod (kvInv_ch0_off γr.raft γr.kv) $$ Hki with %hch
  iunfold kvApplied at Hka
  icases Hka with ⟨Hka, %hx⟩
  iunfold kvAppliedL at Hka
  icases Hka with ⟨#HA, Hhi, Hcert, %hlog⟩
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
  iapply (srvImage_of_dbImage (γk := γr.kv) h0.1 hch h0.2)
  iunfold mergedImg at Hmi
  icases Hmi with ⟨%hmi, %u, #Him⟩
  obtain ⟨hrest, hre⟩ := hmi
  iunfold dbImage
  iexists A, u
  iframe HA'
  rw [← hlog, ← hx.2]
  iframe Him
  ipureintro
  have hpre : γr.raft.pre = [] := by rw [hraft]
  have hz : uint.Z (W64 0) = 0 := rfl
  refine ⟨by simp only []; omega, by simpa [hpre] using hrest, ?_⟩
  exact hre

end proof

end EtcdGrove
end Perennial
