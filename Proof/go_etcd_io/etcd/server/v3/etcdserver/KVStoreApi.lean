/-
**The server's store over mvcc's API** (strict M1, 2026-11-05; the frozen draft
`notes/mvcc-api-clients/ServerSpecs.lean`, `clients-server.md`, landed as drafted, namespace
`srvApi`, a restated definition with the suffix `A`): the update shapes the server hands to mvcc
(§1, in `lease/MvccShapes.lean` with the critical-section contract `csContractA`: the lessor's
`Revoke` takes them), the server's ghost names of the store's state and its store invariant `kvStoreInv`, which
holds the client's `mvccState γ σ` (§2), the builders of every update shape the server needs
(`kvAus.law`), the watch path's peek (`kvPeek.law`) and the notified log's certified bounds
(`histLb`, §3), the snapshot's image over `mvccImage` (§3c) and the `Restore` builder (§3d), the
apply chain's environment and resources (§4) and the server's changed conjuncts (§6).

Laws are stated as `abbrev <name>.law : Prop` (stated, not assumed); `KVStoreLaws.lean` proves
them, over mvcc's API laws as hypotheses. Differences from the draft (its own header's M1 note):
`auSnap`, `kvAus.law`'s snapshot conjunct and `senderImage.law` drop `σ.crev = -1` and
`γr.kv.cmp = false`, the API's `mvccImage_snapshot.law` having dropped them (the backend's
`Snapshot` axiom strengthened, 2026-11-04). The lessor's restated specs are in their `Spec/` files
(`lessor__Revoke.lean`, `lessor__Grant.lean`); `applierV3backend.Compaction`'s waits for the
chain's `backendIsA` (`notes/mvcc-migration/server.md`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__Snapshot
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVModelM
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvImage
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Chain
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVStoreCore
public import Proof.go_etcd_io.etcd.cache.v3.EtcdModel
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVLogOk

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section
namespace Perennial
namespace EtcdGrove
namespace srvApi
open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc mvcc.api

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-! ## 2. The server's names and its store invariant -/

/-- The watchable store at `wsl` as the store handle (`v3rpc.wsIface`, by `rfl`). -/
abbrev wsIfaceA (wsl : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl


variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The log `log` is the KV model of a committed raft log** (persistent, timeless:
`srvRLogLb_timeless`, raft's API exporting `isCommittedLogLb_timeless`): the server's raft witness
(`kvLogAt`'s, without the index). Today's `kvCert`/`certOk` role. No receipt: the apply thread
needs the witness of a target log before the update that gives the receipt fires. -/
def kvNx (γr : ReadNames) (on : Bool) (log : mvcc.Log) : IProp GF :=
  iprop(∃ A : List EntryModel, srvRLogLb γr.raft A ∗ ⌜kvModelM on γr.kv A = log ∧
    mvcc.LogPutsLe etcdKeyMax log⌝)

/-- **The compaction revision is permitted** (persistent): never compacted, or a cluster permit;
and `-1` in a cluster that never compacts. Downward closed by `kvCmpPermit_le`. -/
def crevOk (γr : ReadNames) (c : Int) : IProp GF :=
  iprop((⌜c = -1⌝ ∨ kvCmpPermit γr.kv c) ∗ ⌜γr.kv.cmp = false → c = -1⌝)

/-- **A certified lower bound of the notified log** (persistent; the watch path's `histLb`): `L` a
prefix of the notified log, and of a log that is the KV model of a committed raft log, well formed,
with its receipt (round 16: so `LogSmall L` follows, `histLb_model.law`), and a revision per change
past its first two (R8, 2026-11-07: so its length is below `2 ^ 63`; with the witness's key bound,
`histLb_pure`). Prefix-closed; two are prefix-comparable (`monoListLbOwn`'s agreement). -/
def histLb (γr : ReadNames) (on : Bool) (γs : KVSNames) (L : mvcc.Log) : IProp GF :=
  iprop(monoListLbOwn γs.nlog L ∗ ∃ L' : mvcc.Log, ⌜L <+: L' ∧ mvcc.LogWf' L'⌝ ∗ kvNx γr on L' ∗
    ⧖ (mvcc.logCh L') ∗ ⌜L'.length ≤ mvcc.logCh L' + 2⌝)

omit package_sem in
instance kvNx_persistent (γr : ReadNames) (on : Bool) (log : mvcc.Log) :
    Persistent (kvNx (GF := GF) γr on log) := by
  unfold kvNx; infer_instance

omit package_sem in
instance kvNx_timeless (γr : ReadNames) (on : Bool) (log : mvcc.Log) :
    Timeless (kvNx (GF := GF) γr on log) := by
  unfold kvNx; infer_instance

omit package_sem in
instance crevOk_persistent (γr : ReadNames) (c : Int) : Persistent (crevOk (GF := GF) γr c) := by
  unfold crevOk; infer_instance

omit package_sem in
instance crevOk_timeless (γr : ReadNames) (c : Int) : Timeless (crevOk (GF := GF) γr c) := by
  unfold crevOk; infer_instance

omit package_sem in
instance histLb_persistent (γr : ReadNames) (on : Bool) (γs : KVSNames) (L : mvcc.Log) :
    Persistent (histLb (GF := GF) γr on γs L) := by
  unfold histLb; infer_instance

omit package_sem in
instance histLb_timeless (γr : ReadNames) (on : Bool) (γs : KVSNames) (L : mvcc.Log) :
    Timeless (histLb (GF := GF) γr on γs L) := by
  unfold histLb; infer_instance

/-- **The server's store invariant**, at `kvsN` (outside `↑mvccN` and v3rpc's `wsN`): the client's
state `σ` of the store `kv`, its writer's halves at `σ`, the committed and the notified logs'
monotone lists, both logs the KV model of a committed raft log, the notified log's receipt (round
16: the notify step and `Restore` give it), the compaction revision permitted. Every conjunct is
timeless (`mvccState`: `persistent.law`; `ghostVar`, `monoListAuthOwn`; `kvNx`: `srvRLogLb_timeless`;
`⧖`: `preceipt_timeless`; `crevOk`: pure and `kvRevLbZ`'s ghost), so the peek strips no later. -/
def kvStoreInv (kv : GoInterface) (γ : MvccName) (γr : ReadNames) (on : Bool) (γs : KVSNames) :
    IProp GF :=
  iprop(isMvcc kv γ ∗ inv kvsN iprop(∃ σ : MvccState, mvccState γ σ ∗
    ghostVar γs.st (1 : Qp).half (σ.log, σ.pending) ∗ ghostVar γs.cr (1 : Qp).half σ.crev ∗
    monoListAuthOwn γs.slog 1 σ.log ∗ monoListAuthOwn γs.nlog 1 σ.notifiedLog ∗
    kvNx γr on σ.log ∗ kvNx γr on σ.notifiedLog ∗ ⧖ (mvcc.logCh σ.notifiedLog) ∗
    crevOk γr σ.crev))

/-- **The store invariant is the generic one** at the raft witness and the compaction permit
(`KVStoreCore.lean`, where its builders are proved). -/
theorem kvStoreInv_eq (kv : GoInterface) (γ : MvccName) (γr : ReadNames) (on : Bool)
    (γs : KVSNames) : kvStoreInv (GF := GF) kv γ γr on γs = kvStoreInvG kv γ (kvNx γr on) (crevOk γr) γs :=
  rfl

theorem histLb_eq (γr : ReadNames) (on : Bool) (γs : KVSNames) (L : mvcc.Log) :
    histLb (GF := GF) γr on γs L = histLbG (kvNx γr on) γs L := rfl

/-- **What a reader learns at its update** (`Q σ` of `auRead`): the floor `L₀` extended, the
state's log a floor itself, the model of a committed raft log, with its receipt (the invariant's,
of the notified log, by `preceipt_mono`), reachable (`mvccState_reachable`: well formed by
`reach_logWf.law`, fewer than `2 ^ 63 - 3` revisions). -/
def kvReadAt (γr : ReadNames) (on : Bool) (γs : KVSNames) (L₀ : mvcc.Log) (σ : MvccState) :
    IProp GF :=
  iprop(⌜L₀ <+: σ.log⌝ ∗ kvLogLb γs σ.log ∗ kvNx γr on σ.log ∗ ⧖ (mvcc.logCh σ.log) ∗
    crevOk γr σ.crev ∗ ⌜MvccReachable σ ∧ σ.log.length + 3 ≤ 2 ^ 63⌝)

omit package_sem in
instance kvReadAt_persistent (γr : ReadNames) (on : Bool) (γs : KVSNames) (L₀ : mvcc.Log)
    (σ : MvccState) : Persistent (kvReadAt (GF := GF) γr on γs L₀ σ) := by
  unfold kvReadAt; infer_instance

theorem kvReadAt_eq (γr : ReadNames) (on : Bool) (γs : KVSNames) (L₀ : mvcc.Log) (σ : MvccState) :
    kvReadAt (GF := GF) γr on γs L₀ σ = kvReadAtG (kvNx γr on) (crevOk γr) γs L₀ σ := rfl

/-! ## 3. The AU builders (the server proves them from `kvStoreInv`) -/

/-- **The builders**, given the store invariant. The apply thread's take its halves (`wSt`,
`crOwn`) and, for a change of the history, the raft witness of the target (`kvNx`); the receipt
of the new notified log comes from mvcc's notify step (round 16). -/
abbrev kvAus.law : Prop :=
  ∀ (kv : GoInterface) (γ : MvccName) (γr : ReadNames) (on : Bool) (γs : KVSNames),
  kvStoreInv (GF := GF) kv γ γr on γs ⊢
    -- a write's begin (`Write`, `mvccDeleter`), continuation form (the end nests in `X`)
    □ (∀ log c (X : IProp GF), wSt γs log c -∗ (wSt γs log c -∗ X) -∗
        auBegin γ (stAt log c) X) ∗
    -- the writer's own read (the apply's `Range`, `Txn`'s pinned read, the header after `Compact`)
    □ (∀ log c (X : IProp GF), wSt γs log c -∗ (wSt γs log c -∗ X) -∗
        auRead γ (fun σ => iprop(⌜σ = stAt log c⌝ ∗ X))) ∗
    -- the merged snapshot's update (`mvccImage_snapshot.law`): at every access `pending = none`
    -- from the half (the writer is not inside an `End` while it snapshots); the state the writer's
    □ (∀ log c (X : IProp GF), wSt γs log c -∗ (wSt γs log c -∗ X) -∗
        auSnap γ (fun σ => iprop(⌜σ = stAt log c⌝ ∗ X))) ∗
    -- a write's end: the committed log's witness
    □ (∀ log c pend, wSt γs log c -∗ kvNx γr on (mvcc.commitLog log pend) -∗
        auEnd γ (stAt log c) pend (wSt γs (mvcc.commitLog log pend) c)) ∗
    -- a compaction at `rev`, one of the log's, permitted
    □ (∀ log c (rev : w64), ⌜sint.Z rev < log.length⌝ → wSt γs log c -∗ crOwn γs c -∗
        crevOk γr (sint.Z rev) -∗
        auCompact γ rev (fun σ => iprop(⌜σ = stAt log c⌝ ∗
          wSt γs log (apply.cmpRevAfter c rev) ∗ crOwn γs (apply.cmpRevAfter c rev)))) ∗
    -- a restore to an extension (linked: `EtcdServer.applySnapshot`; §3d)
    □ (∀ log c log' c', ⌜log <+: log' ∧ c ≤ c'⌝ → wSt γs log c -∗ crOwn γs c -∗
        kvNx γr on log' -∗ crevOk γr c' -∗
        auRestore γ (stAt log' c') (fun σ => iprop(⌜σ = stAt log c⌝ ∗ wSt γs log' c' ∗
          crOwn γs c'))) ∗
    -- anyone's read, from a floor
    □ (∀ L₀, kvLogLb γs L₀ -∗ auRead γ (kvReadAt γr on γs L₀)) ∗
    -- the writer's facts at its state, outside any update (no credit: the contents are timeless):
    -- a floor of its log, its raft witness (xreview §7: the end builder at `pend = []`), its
    -- receipt (`Revoke`'s sort premise, `rqOk`'s room), reachability and the length bound
    □ (∀ log c, wSt γs log c ={⊤}=∗ wSt γs log c ∗ kvLogLb γs log ∗ kvNx γr on log ∗
        ⧖ (mvcc.logCh log) ∗ ⌜MvccReachable (stAt log c) ∧ log.length + 3 ≤ 2 ^ 63⌝)

/-- **The watch path's peek**: at any mask with `kvsN`, the state with its certified notified-log
bound and its permit, and a closer for the same state. -/
abbrev kvPeek.law : Prop :=
  ∀ (kv : GoInterface) (γ : MvccName) (γr : ReadNames) (on : Bool) (γs : KVSNames) (E : CoPset),
  ↑kvsN ⊆ E →
  kvStoreInv (GF := GF) kv γ γr on γs ⊢ |={E, E \ ↑kvsN}=> ∃ σ : MvccState, mvccState γ σ ∗
    histLb γr on γs σ.notifiedLog ∗ crevOk γr σ.crev ∗ kvLogLb γs σ.log ∗
    (mvccState γ σ ={E \ ↑kvsN, E}=∗ True)

/-- **The never-compacting cluster**: its compaction revision `-1`. -/
abbrev crevOk_off.law : Prop :=
  ∀ (γr : ReadNames) (c : Int), γr.kv.cmp = false → crevOk (GF := GF) γr c ⊢ ⌜c = -1⌝

/-- The boot's bound. -/
abbrev histLb_boot.law : Prop :=
  ∀ (kv : GoInterface) (γ : MvccName) (γr : ReadNames) (on : Bool) (γs : KVSNames),
  kvStoreInv (GF := GF) kv γ γr on γs ={⊤}=∗ histLb γr on γs [[], []]

omit package_sem in
/-- **A certified notified-log bound's pure facts** (R8, 2026-11-07, for R9; `histLb_model.law`'s
pure part, without opening an invariant): well formed (a prefix of a well-formed log), fewer than
`2 ^ 63` revisions and small (the receipt, under `receiptBound GF ≤ 2 ^ 62`, with a revision per
change past the first two), and its keys short (the witness's). -/
theorem histLb_pure (hrb : receiptBound GF ≤ 2 ^ 62) (γr : ReadNames) (on : Bool) (γs : KVSNames)
    (L : mvcc.Log) :
    histLb (GF := GF) γr on γs L ⊢
      ⌜mvcc.LogWf' L ∧ L.length < 2 ^ 63 ∧ txn.LogSmall L ∧ mvcc.LogPutsLe etcdKeyMax L⌝ := by
  unfold histLb
  iintro ⟨-, %L', %hp, Hnx, Hrc, %hlen⟩
  ihave %Hm := preceipt_lt _ $$ Hrc
  iunfold kvNx at Hnx
  icases Hnx with ⟨%A, -, %hA⟩
  ipureintro
  have hs : txn.LogSmall L' := by
    unfold txn.LogSmall txn.logChanges; unfold mvcc.logCh at Hm; omega
  have hl : L.length ≤ L'.length := hp.1.length_le
  refine ⟨logWf'_of_prefix hp.1 hp.2, ?_, logSmall_of_prefix hp.1 hs, hA.2.prefix hp.1⟩
  unfold mvcc.logCh at hlen Hm; omega

end defs

/-! ## 3b. G3: the sender's update, from `kvStoreInv`

The API's `mvccImage_snapshot.law` takes `isMvcc kv γ` (`kvStoreInv` holds it), the whole backend
share, held through `backend.Snapshot`, and an update at the state (`auSnap`), which its proof
commits before the snapshot. The server builds the update by `kvAus.law`'s third conjunct: from the
apply thread's half `wSt γs log c`, the update opens `kvStoreInv`, gives `mvccState γ σ` with
`⌜σ.pending = none⌝` (the halves of `st` agree at `(log, none)`), takes it back unchanged, and
commits `⌜σ = stAt log c⌝ ∗ wSt γs log c`. The model tie is outside the update: the apply thread's
`kvApplied` at `A` says `log = kvModel A`, `c = crevOf A` (pure), so `Φ` needs only the halves. §3c
composes them (`senderImage.law`). (M1, 2026-11-05: the draft's scope, a cluster that never
compacts, is lifted with the law's `σ.crev = -1`: the backend's `Snapshot` axiom now sees the
compaction keys' values. Not to confuse with `on`, the auth mode, `kvModelM on`: the send is at
`on = false`, `#7-on` deferred.) -/

/-! ## 3c. The image certificate over `mvccImage` (`InvImage.lean:148`'s `dbImage`) -/

section image
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [bk_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **`D`'s parts the server's model fixes, besides the store's**: `InvImage.lean`'s
`imageRestAt` (the draft's, moved there beside `dbImage`, 2026-11-06). -/
abbrev imageRestAt (γk : KVNames) (bootLog : List EntryM) (i : w64) (L : List EntryModel)
    (D : backend.Data) : Prop :=
  EtcdGrove.imageRestAt γk bootLog i L D

/-- **The image certificate, restated**: `InvImage.lean`'s `dbImage`, restated in place as the
draft's `dbImageA` (2026-11-06): `D` the image of the KV model of a committed prefix `A` ending at
`i` (the store's part: `mvccImage`, its receipt inside, in place of `imageAt`'s
`keyImageM`/records, `IdxWf` and the separate `⧖ (logCh (kvModel γk A))`), and the server's parts
(`imageRestAt`). The sender makes it by `mvccImage_snapshot.law` at its update
(`SnapSendBranch.mergedCreate_window`, `merged_image`); the receiver opens the snapshot backend
with it (`dbImageA_open.law`). -/
abbrev dbImageA (γ : ServerRaftNames) (γk : KVNames) (i : w64) (D : backend.Data) : IProp GF :=
  dbImage γ γk i D

/-- **The sender's image, from the snapshot's** (proved; the step after `mvccImage_snapshot.law`):
the image of the pinned state's history, with the server's parts the client's observation gave. -/
theorem dbImageA_of_send (γ : ServerRaftNames) (γk : KVNames) (i : w64) (D : backend.Data)
    (A : List EntryModel) (u : Bool)
    (hi : uint.Z i = uint.Z γ.ai0 + A.length) (hr : imageRestAt γk γ.raft.boot i (γ.pre ++ A) D)
    (hre : imageStOk (kvModel γk A) (crevOf γk A)) :
    srvRLogLb (GF := GF) γ A ∗
      mvccImage D (kvModel γk A) (crevOf γk A) u ⊢ dbImageA γ γk i D := by
  iintro ⟨#Hlb, Him⟩
  unfold dbImageA dbImage
  iexists A, u
  iframe Hlb Him
  ipureintro; exact ⟨hi, hr, hre⟩

/-- **The merged snapshot's send** (`createMergedSnapshotMessage`'s `s.be.Snapshot()`, after
`s.KV().Commit()`), derived from the API's `mvccImage_snapshot.law` (its `isMvcc` from `kvStoreInv`)
and the server's builders: the apply thread, at its applied prefix `A` (its half at the model's
`(kvModel A, crevOf A)`), with the whole backend share and the client's observation `Q` of the meta keys and the tracked buckets (the
stored-index window's, `srvBeSnapOk_window`, whose `D`-level reading is `imageRestAt`), gets the
snapshot open over `D` and the image certificate `dbImageA` at the snapshot's index `i`. -/
abbrev senderImage.law : Prop :=
  backend.backend.Snapshot.spec (GF := GF) (hG := hG) →
  mvccImage_snapshot.law (GF := GF) (hG := hG) → kvAus.law (GF := GF) →
  ∀ [ThreadBoundLe GF (2 ^ 29)] (kv : GoInterface) (γ : MvccName) (γr : ReadNames) (γs : KVSNames)
    (i : w64)
    (A : List EntryModel) (B : mvcc.KBReal) (Pk : IProp GF) (qo : Qp) (R : IProp GF)
    (Q : GMap (GoString × GoString) GoString → GMap GoString backend.BktData → Prop),
  (∀ D, Q (backend.hkData B.P D) (backend.rbData B.P D) →
    imageRestAt γr.kv γr.raft.raft.boot i (γr.raft.pre ++ A) D) →
  uint.Z i = uint.Z γr.raft.ai0 + A.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      kvStoreInv kv γ γr false γs ∗ wSt γs (kvModel γr.kv A) (crevOf γr.kv A) ∗
      srvRLogLb γr.raft A ∗ mvccBackend γ 1 B Pk ∗ backend.bOpen B.γB qo ∗ backend.wbTok B.γB ∗
      threadTok ∗ R ∗ □ (∀ (d : GMap (GoString × GoString) GoString) (r : GMap GoString backend.BktData),
        R -∗ Pk -∗ backend.hkOwn B.γB d -∗ backend.rbOwn B.γB r -∗ ⌜Q d r⌝) }}
    (App (Val (B.be @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty
      @!! go!"Snapshot")) (Val #()))
  {{ (sp : Loc) (D : backend.Data),
      RET #(interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.snapshot.ty) #sp);
      backend.snapOpen sp D ∗ backend.bOpen B.γB qo ∗ R ∗ mvccBackend γ 1 B Pk ∗
      wSt γs (kvModel γr.kv A) (crevOf γr.kv A) ∗ dbImageA γr.raft γr.kv i D }}

/-- **The receiver's backend over the image** (from `etcdStorage_open.law`, at the snapshot
opener's post `newPostKP` at `K := snapOpenK`, with the store's part of the payment rights): the
store's resources at the image's history. (Phase A of mvcc's API over its storage abstraction,
2026-11-06: at a real instance `bk` of etcd's backend with mvcc's layout, `bridgeParams bk.P`, in
compaction mode, `mvccStorageFor` of its storage `etcdStorage bk`; until then `mvccBackendFor` at
the `BkRef` `⟨γB, P, b⟩` with the registration name `gx`.) (2026-11-06, the server's reader-slot
request, decided by the coordinator) `rdStockN - 2` open shares, and two counted slots back for the
server's long-lived readers (the apply thread's, the storage-version monitor's). -/
abbrev dbImageA_open.law : Prop :=
  ∀ (γ : ServerRaftNames) (γk : KVNames) (i : w64) (D : backend.Data) (bk : mvcc.KBReal)
    (Pk K : backend.BNames → IProp GF),
  mvcc.bridgeParams bk.P → bk.cm = true →
  dbImageA (GF := GF) γ γk i D ∗ □ (∀ γ' b', mvcc.keySized γ' bk.P b') ∗
    backend.newPostKP bk.γB bk.P (fun _ => mvccW bk.gx) Pk K bk.be D ∗ mvccWReg bk.gx ∗
    backend.wbTok bk.γB ∗ backend.wbTok bk.γB ∗ □ (⧗ 1 ={⊤}=∗ backend.wbTok bk.γB) ∗
    ([∗list] _x ∈ List.replicate (backend.rdStockN - 2) (), backend.bOpen bk.γB backend.rdOpen) ={⊤}=∗
  ∃ (A : List EntryModel) (u : Bool), srvRLogLb γ A ∗
    ⌜uint.Z i = uint.Z γ.ai0 + A.length ∧ imageRestAt γk γ.raft.boot i (γ.pre ++ A) D⌝ ∗
    mvccStorageFor bk (Pk bk.γB) (kvModel γk A) (crevOf γk A) u ∗ backendRest bk.γB bk.P K bk.be D ∗
    backend.rdTok bk.γB bk.P bk.be ∗ backend.rdTok bk.γB bk.P bk.be

/-- **The boot's backend for the store** (`NewServer`'s step 4-5, F3: `mvccImage_fresh.law` under an
update, which the boot's fupd absorbs): `backend.New`'s pooled post at the store's write invariant
over fresh data (no `Key` entry, no compaction key: a new cluster's data directory, `bootOk`'s
empty bucket), with the store's part of the payment rights, gives `New`'s `mvccStorageFor` at
`mvccStart` and the client's rest. Derived from `mvccImage_fresh.law` and `etcdStorage_open.law`
(phase A, 2026-11-06: at a real instance `bk` with `bridgeParams bk.P`, in compaction mode). -/
abbrev bootBackend.law : Prop :=
  mvccImage_fresh.law (GF := GF) → etcdStorage_open.law (GF := GF) →
  ∀ (bk : mvcc.KBReal) (Pk K : backend.BNames → IProp GF) (D : backend.Data),
  mvcc.bridgeParams bk.P → mvcc.leaseParams bk.P → bk.cm = true →
  (∀ k, backend.dget D mvcc.keyName k = none) →
  backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName mvcc.schedKeyBytes = none →
  backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName mvcc.finKeyBytes = none →
  □ (∀ γ' b', mvcc.keySized (GF := GF) γ' bk.P b') ∗
    backend.newPostKP bk.γB bk.P (fun _ => mvccW bk.gx) Pk K bk.be D ∗ mvccWReg bk.gx ∗
    backend.wbTok bk.γB ∗ backend.wbTok bk.γB ∗ □ (⧗ 1 ={⊤}=∗ backend.wbTok bk.γB) ∗
    ([∗list] _x ∈ List.replicate (backend.rdStockN - 2) (), backend.bOpen bk.γB backend.rdOpen) ={⊤}=∗
  mvccStorageFor bk (Pk bk.γB) mvccStart.log mvccStart.crev false ∗ backendRest bk.γB bk.P K bk.be D ∗
    backend.rdTok bk.γB bk.P bk.be ∗ backend.rdTok bk.γB bk.P bk.be

/-- **The model's restored state is reachable** (a server model lemma, from the KV invariant's
claims of the committed entries: their changes well formed, deletes of present keys, compactions
increasing and at most the current revision; today's `IdxWf (kvModel γk A) []` conjunct of
`imageAt`, proved by the sender from its store, now of the model). -/
abbrev kvModel_reachable.law : Prop :=
  ∀ (γr : ReadNames) (on : Bool) (A : List EntryModel),
  kvInv (GF := GF) γr.raft γr.kv ∗ srvRLogLb γr.raft A ={⊤}=∗
    ⌜MvccReachable (stAt (kvModelM on γr.kv A) (crevOf γr.kv A))⌝

end image

/-! ## 3d. The Restore builder, with every premise of `KV.Restore.contract` -/

section restore
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`KV.Restore.contract`'s precondition** (round 16; without `pkgInit`), at the update `Q`. -/
def restorePreA (kv : GoInterface) (γ : MvccName) (B B' : mvcc.KBReal) (Pk Pk' : IProp GF)
    (σ' : MvccState) (u : Bool) (L : List w64) (dq : DFrac) (f : GoFunc)
    (Pre Q' Post X Y : IProp GF) (Q : MvccState → IProp GF) : IProp GF :=
  iprop(isMvcc kv γ ∗ mvccOpen γ ∗ mvccBackend γ 1 B Pk ∗
    mvccStorageFor B' Pk' σ'.log σ'.crev u ∗ ⌜MvccReachable σ' ∧ σ'.pending = none⌝ ∗
    backend.plHookAt B'.γB dq f ∗ Pre ∗ mvcc.api.hookRun Pk' f Pre Q' ∗ (Q' ={⊤}=∗ Pk' ∗ Post) ∗
    X ∗ backend.commitReq B'.γB B'.P Pk' B'.be X Y ∗
    lease.leaseOwn (mvccLeases γ) L ∅ ∗
    ⌜∀ it lid, (mvcc.pendItems σ'.log []).lookup it = some lid →
      lid ∈ L ∧ (it.Key'.length : Int) < 2 ^ 63 - 1⌝ ∗
    auRestore γ σ' Q)

/-- **The Restore builder** (`EtcdServer.applySnapshot`, linked: `Link.lean:2407`): from the apply
thread's state at the applied prefix `A` (its halves, the open token, the old backend's whole share,
the snapshot's prefix `A'` extending it (both committed, `A` the shorter: the
snapshot's index is above the applied one), the new backend's store resources at the image's
history (`dbImageA_open.law`), the new backend's unset hook (`plHook B'.γB nil` at `dq = ½`,
`f = nil`: `hookRun`'s view-shift row, the hook set after `Restore`, `server.go:1078`), the apply
protocol's `Pre`/`Q'`/`Post` across the resumed compaction's lock, the commit request `True ⇒ True`
(`commitReq_true`), the lessor recovered over the new backend (`leaseOwn … Ls ∅`, `Recover` before
`Restore`), and the model's facts: the restored state reachable (`kvModel_reachable.law`), its
compaction revision permitted (the committed compaction entries' claims), its leased items' leases
live (the image's lease bucket, `bkRestAt`: the workload has no lease, so `Ls = []` and no item) —
the contract's whole precondition, its update committing the apply thread to the restored state.
(2026-11-06, proved: `KVStoreLaws.restoreArgs_holds`; the two backends' batch-lock invariants `Pk`,
`Pk'` separate, the old one the old names', the new one the new names'.) -/
abbrev restoreArgs.law : Prop :=
  ∀ (kv : GoInterface) (γ : MvccName) (γr : ReadNames) (on : Bool) (γs : KVSNames)
    (log : mvcc.Log) (c : Int) (A A' : List EntryModel) (B B' : mvcc.KBReal) (Pk Pk' : IProp GF)
    (u : Bool) (Ls : List w64) (dq : DFrac) (f : GoFunc) (Pre Q' Post : IProp GF),
  let σ' := stAt (kvModelM on γr.kv A') (crevOf γr.kv A')
  log = kvModelM on γr.kv A → c = crevOf γr.kv A → A <+: A' → MvccReachable σ' →
  mvcc.LogPutsLe etcdKeyMax σ'.log →
  (∀ it lid, (mvcc.pendItems σ'.log []).lookup it = some lid →
    lid ∈ Ls ∧ (it.Key'.length : Int) < 2 ^ 63 - 1) →
  kvStoreInv (GF := GF) kv γ γr on γs ∗ wSt γs log c ∗ crOwn γs c ∗ srvRLogLb γr.raft A' ∗
    crevOk γr σ'.crev ∗ mvccOpen γ ∗ mvccBackend γ 1 B Pk ∗
    mvccStorageFor B' Pk' σ'.log σ'.crev u ∗
    backend.plHookAt B'.γB dq f ∗ Pre ∗ mvcc.api.hookRun Pk' f Pre Q' ∗
    (Q' ={⊤}=∗ Pk' ∗ Post) ∗ lease.leaseOwn (mvccLeases γ) Ls ∅ ⊢
  restorePreA kv γ B B' Pk Pk' σ' u Ls dq f Pre Q' Post iprop(True) iprop(True)
    (fun σ => iprop(⌜σ = stAt log c⌝ ∗ wSt γs σ'.log σ'.crev ∗ crOwn γs σ'.crev))

end restore

/-! ## 4. The apply chain's environment and resources

Restated in place in `apply/Chain.lean` (strict M1, 2026-11-05: `apply.AEnv` has the draft's
`AEnvA` fields, `apply.kvOwn` is `kvOwnA`, ...); the draft's names are these aliases. -/

section apply
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

abbrev AEnvA (G : BundledGFunctors) := apply.AEnv G

abbrev envAus (E : AEnvA GF) : IProp GF := apply.envAus E
abbrev kvBk (E : AEnvA GF) : IProp GF := apply.kvBk E
abbrev leasesLiveA (E : AEnvA GF) (s : List EtcdKv) : IProp GF := apply.leasesLive E s
abbrev kvOwnA (E : AEnvA GF) (log : mvcc.Log) : IProp GF := apply.kvOwn E log
abbrev cmpOwnA (E : AEnvA GF) (c : Int) : IProp GF := apply.cmpOwn E c
abbrev mPreA (E : AEnvA GF) (c : apply.Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    IProp GF := apply.mPre E c a info log Pre Q Post
abbrev certPreA (E : AEnvA GF) (c : apply.Chain) (rq : apply.IRRModel) (log : mvcc.Log) :
    IProp GF := apply.certPre E c rq log
abbrev cmpChanA (crev : Int) (rev : w64) (ch : GoChan) : IProp GF := apply.cmpChan (GF := GF) crev rev ch

end apply

/-! ## 6. The server's construction, reads and compaction: the changed conjuncts -/

section server
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The server's KV invariants, restated** (`srvKVInvs`): the KV invariant and raft's committed
log's; the store invariant; the chain's witness and permit the server's; the mode tie the KV
names'; and (xreview §6c) the store handle the watchable store at `wsl` (`New`'s; `shapes.law`'s
`PW` conjunct then gives `NewWatchStream`'s contract, which `isMvcc` alone does not). -/
def srvKVInvsA (on : Bool) (E : AEnvA GF) (γr : ReadNames) (wsl : Loc) : IProp GF :=
  iprop(kvInv γr.raft γr.kv ∗ srvRaftLogInv γr.raft ∗ kvStoreInv E.kv E.γ γr on E.γs ∗
    ⌜E.kv = wsIfaceA wsl ∧ E.Nx = kvNx γr on ∧ E.Cp = crevOk γr ∧ γr.kv.cmp = E.cmp ∧
      γr.kv.cret = E.cret⌝)

/-- **The client model's laws over `histLb`** (xreview §6b; today's `watchLaws_srv` over `evLog`,
`cli/InvWatch.lean:425`): a certified notified-log bound is well formed, has fewer than `2 ^ 63`
revisions, is small (its receipt, `receiptBound ≤ 2 ^ 62`: `preceipt_lt`), its keys short (the
server's request checks: `srvKVCoreM_keys`), and each of its revisions is reached (`srvRevLbA`,
restating `etcdReached_of_certOk`'s `srvReachedAt`). `srvEtcdState`/`srvStep` restate over
`srvLogA` (below) with `histLb` in place of `idxSealed ∗ certOk`. -/
abbrev histLb_model.law : Prop :=
  ∀ (on : Bool) (E : AEnvA GF) (γr : ReadNames) (wsl : Loc),
  receiptBound GF ≤ 2 ^ 62 →
  srvKVInvsA on E γr wsl ⊢ □ ∀ L : mvcc.Log, histLb γr on E.γs L ={⊤}=∗
    ⌜mvcc.LogWf' L ∧ L.length < 2 ^ 63 ∧ txn.LogSmall L ∧ mvcc.LogPutsLe etcdKeyMax L⌝ ∗
    □ (∀ r : w64, ⌜sint.Z r < L.length⌝ -∗
        ∃ A : List EntryModel, srvRLogLb γr.raft A ∗ ⌜sint.Z r < (kvModelM on γr.kv A).length⌝)

/-- **`NewServer.spec`'s mvcc-related premises, restated**: the store-state names fresh. -/
def newServerStoreFreshA (γs : KVSNames) : IProp GF :=
  iprop(ghostVar γs.st 1 (([[], []] : mvcc.Log), (none : Option (List mvcc.Change))) ∗
    ghostVar γs.cr 1 (-1 : Int) ∗ monoListAuthOwn γs.slog 1 ([[], []] : mvcc.Log) ∗
    monoListAuthOwn γs.nlog 1 ([[], []] : mvcc.Log))

/-- **The boot's store** (inside `NewServer`): after `mvccW_alloc`, `backend.New` at `mvccW gx`,
`bootBackend.law` (`mvccImage_fresh.law`'s update, the open law) and `mvcc.New`, the store invariant
at `mvccStart` (its receipt `⧖ 0`, `preceipt_zero`). -/
abbrev bootStore.law : Prop :=
  ∀ (kv : GoInterface) (γ : MvccName) (γr : ReadNames) (on : Bool) (γs : KVSNames),
  kvModelM on γr.kv [] = [[], []] →
  isMvcc (GF := GF) kv γ ∗ mvccState γ mvccStart ∗ newServerStoreFreshA γs ∗ srvRLogLb γr.raft [] ={⊤}=∗
    kvStoreInv kv γ γr on γs ∗ wSt γs [[], []] (-1) ∗ crOwn γs (-1)

end server

end srvApi
end EtcdGrove
end Perennial
