/-
(2026-11-06, the server track's ninth session: `dbImageA` (§3c) landed in place as `InvImage.lean`'s
`dbImage` with one more pure conjunct, `imageStOk (kvModel γk A) (crevOf γk A)` (reachable, history
short: the sender's `writer_facts`), so `kvModel_reachable.law` is not needed; `senderImage.law` is
proved (`KVStoreLaws.senderImage_holds`, over `snapImageG`), `dbImageA_of_send` takes the fact.)
(2026-11-06, decided by the coordinator: `lessor.Revoke.specA` takes its update only for a live
lease, `if decide (id ∈ L) then auBegin … else True`, and does not give it back in the not-live arm;
§5.)
(2026-11-04: `mvccImage_snapshot.law` no longer takes `σ.crev = -1` (the user strengthened
`backend.Snapshot`'s axiom), so `auSnap`, `kvAus.law`'s snapshot conjunct and `senderImage.law` below
no longer need `γr.kv.cmp = false`; this draft is not built, and the M1 proofs drop the premise.)
# The server-side clients of mvcc over the API (rounds 15-16): restated specs and the server's invariant

Scratch draft (outside the repository). Typecheck from the worktree `mvcc-api` (at `6cc29c14f0`):
`lake env lean ~/.claude-D/jobs/e4ba2bf8/tmp/clients/server/ServerSpecs.lean`.
Companion note: `~/mvcc-api-candidates/clients-server.md`.

Names are under `srvApi` and carry the suffix `A` where they restate a definition of today's.
Large specs are given by their changed conjuncts (as definitions) and by reference for the rest.
Statements that a proof will establish are `abbrev <name>.law : Prop` (stated, not assumed).
G3 (the sender's image) is the API's `mvccImage_snapshot.law` (`ac1e686407`, by an update at the
state, no pin predicate; since `6cc29c14f0`, the review of round 16's F1-F3, for a store that never
compacted, `isMvcc` in its pre): §3b builds its update from `kvStoreInv` in the cluster's
compaction-off mode (`γr.kv.cmp = false`), §3c the sender's image over it; the compacting sender is
deferred (F1: `backend.Snapshot.spec` does not give the compaction keys' committed values).

Changes since round 14 (the cross-review `~/mvcc-api-candidates/xreview-clients.md`, API rounds 15-16):
the receipt `⧖ (logCh ..)` in the update shapes and in `kvStoreInv`, carried by `histLb`,
`kvReadAt`, `rangeReadOkA`, `newHeaderPostA` and the writer's facts (§1, §5); G3 over the API's
`mvccImage_snapshot.law` (§3b, §3c);
`dbImage` over `mvccImage` (§3c); the Restore builder with every premise of `KV.Restore.contract`
(§3d); `AEnvA.Pk : BkRef → IProp` (§2); Revoke's nested update (§3); `histLb_model.law`, the tie
`E.kv = wsIfaceA wsl` (§6); `kvNx log` in the writer's facts, `threadTok` outside `kvOwnA` (§7).
-/
import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__Snapshot
import Proof.go_etcd_io.etcd.server.v3.etcdserver.ServerOn
import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvImage
import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Chain
import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Revoke
import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Grant

set_option linter.unusedSectionVars false

noncomputable section
namespace Perennial
namespace EtcdGrove
namespace srvApi
open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc mvcc.api

/-! ## 0. The pure part -/

/-- The writer's view of the state: the state at `(log, crev)` with nothing pending. -/
def stAt (log : mvcc.Log) (c : Int) : MvccState := ⟨log, c, none⟩

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The watchable store at `wsl` as the store handle (`v3rpc.wsIface`, by `rfl`). -/
abbrev wsIfaceA (wsl : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl

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

/-- **`mvccImage_snapshot.law`'s update** (the API's, `6cc29c14f0`): at a state with nothing
pending and never compacted (F1: the law covers only a store that never compacted, as today's
sender proof does), left unchanged, committing to `Φ σ`. Its atomic precondition says both, so a
reader's update (`auRead`) does not give it by monotonicity: the builder shows `pending = none`
from the writer's half and `crev = -1` from the invariant's permit in a cluster that never compacts
(`crevOk`'s second conjunct), at every access. -/
def auSnap (γ : MvccName) (Φ : MvccState → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (σ : MvccState), mvccState γ σ ∗ ⌜σ.pending = none ∧ σ.crev = -1⌝ }>
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

/-! ## 2. The server's names and its store invariant -/

/-- **The server's ghost names of the store's state** (allocated by `NewServer`'s caller, with
the read names: the floors are indexed by `slog`): `st` the `(log, pending)` part (½ the
invariant, ½ the apply thread's `kvOwn`), `cr` the compaction revision (½ the invariant, ¼
`kvOwn`, ¼ `cmpOwn`), `slog` the monotone list of the committed log (authority the invariant's,
fragments the floors), `nlog` the monotone list of the notified log (the pending revision
included: the watch path's `histLb`). -/
structure KVSNames where
  st : GName
  cr : GName
  slog : GName
  nlog : GName

/-- The store invariant's namespace (outside `mvccN`, as every `server_*` one). -/
def kvsN : Namespace := nroot .@ "server_kv_store"

variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The log `log` is the KV model of a committed raft log** (persistent, timeless:
`srvRLogLb_timeless`, raft's API exporting `isCommittedLogLb_timeless`): the server's raft witness
(`kvLogAt`'s, without the index). Today's `kvCert`/`certOk` role. No receipt: the apply thread
needs the witness of a target log before the update that gives the receipt fires. -/
def kvNx (γr : ReadNames) (on : Bool) (log : mvcc.Log) : IProp GF :=
  iprop(∃ A : List EntryModel, srvRLogLb γr.raft A ∗ ⌜kvModelM on γr.kv A = log⌝)

/-- A floor: the committed log extends `L` (today's `idxCert γ.idx L`; persistent). -/
def kvLogLb (γs : KVSNames) (L : mvcc.Log) : IProp GF := monoListLbOwn γs.slog L

/-- **The compaction revision is permitted** (persistent): never compacted, or a cluster permit;
and `-1` in a cluster that never compacts. Downward closed by `kvCmpPermit_le`. -/
def crevOk (γr : ReadNames) (c : Int) : IProp GF :=
  iprop((⌜c = -1⌝ ∨ kvCmpPermit γr.kv c) ∗ ⌜γr.kv.cmp = false → c = -1⌝)

/-- **A certified lower bound of the notified log** (persistent; the watch path's `histLb`): `L` a
prefix of the notified log, and of a log that is the KV model of a committed raft log, well formed,
with its receipt (round 16: so `LogSmall L` follows, `histLb_model.law`). Prefix-closed; two are
prefix-comparable (`monoListLbOwn`'s agreement). -/
def histLb (γr : ReadNames) (on : Bool) (γs : KVSNames) (L : mvcc.Log) : IProp GF :=
  iprop(monoListLbOwn γs.nlog L ∗ ∃ L' : mvcc.Log, ⌜L <+: L' ∧ mvcc.LogWf' L'⌝ ∗ kvNx γr on L' ∗
    ⧖ (mvcc.logCh L'))

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

/-- The apply thread's half of the state (`kvOwn`'s): the log `log`, nothing pending, and a
quarter of the compaction revision `c`. -/
def wSt (γs : KVSNames) (log : mvcc.Log) (c : Int) : IProp GF :=
  iprop(ghostVar γs.st (1 : Qp).half (log, (none : Option (List mvcc.Change))) ∗
    ghostVar γs.cr (1 : Qp).half.half c)

/-- The compaction right's quarter of the compaction revision (`cmpOwn`'s). -/
def crOwn (γs : KVSNames) (c : Int) : IProp GF := ghostVar γs.cr (1 : Qp).half.half c

/-- **What a reader learns at its update** (`Q σ` of `auRead`): the floor `L₀` extended, the
state's log a floor itself, the model of a committed raft log, with its receipt (the invariant's,
of the notified log, by `preceipt_mono`), reachable (`mvccState_reachable`: well formed by
`reach_logWf.law`, fewer than `2 ^ 63 - 3` revisions). -/
def kvReadAt (γr : ReadNames) (on : Bool) (γs : KVSNames) (L₀ : mvcc.Log) (σ : MvccState) :
    IProp GF :=
  iprop(⌜L₀ <+: σ.log⌝ ∗ kvLogLb γs σ.log ∗ kvNx γr on σ.log ∗ ⧖ (mvcc.logCh σ.log) ∗
    ⌜MvccReachable σ ∧ σ.log.length + 3 ≤ 2 ^ 63⌝)

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
    -- the merged snapshot's update (`mvccImage_snapshot.law`), in a cluster that never compacts:
    -- at every access `pending = none` from the half (the writer is not inside an `End` while it
    -- snapshots) and `crev = -1` from the invariant's `crevOk σ.crev` (`γr.kv.cmp = false`); the
    -- state the writer's
    □ (⌜γr.kv.cmp = false⌝ → ∀ log c (X : IProp GF), wSt γs log c -∗ (wSt γs log c -∗ X) -∗
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

end defs

/-! ## 3b. G3: the sender's update, from `kvStoreInv`

The API's `mvccImage_snapshot.law` (`6cc29c14f0`) takes `isMvcc kv γ` (F2: `kvStoreInv` holds it),
the whole backend share, held through `backend.Snapshot`, and an update at the state (`auSnap`),
which its proof commits before the snapshot; it covers only a store that never compacted (F1). The
server builds the update by `kvAus.law`'s third conjunct, in a cluster that never compacts
(`γr.kv.cmp = false`, the server's `E.cmp = false`): from the apply thread's half `wSt γs log c`, the
update opens `kvStoreInv`, gives `mvccState γ σ` with `⌜σ.pending = none ∧ σ.crev = -1⌝` (the halves
of `st` agree at `(log, none)`; the invariant's `crevOk γr σ.crev` with `cmp = false`), takes it
back unchanged, and commits `⌜σ = stAt log c⌝ ∗ wSt γs log c`. The model tie is outside the update:
the apply thread's `kvApplied` at `A` says `log = kvModel A`, `c = crevOf A` (pure), so `Φ` needs
only the halves. §3c composes them (`senderImage.law`). **A compacting cluster's sender is
deferred** (F1): the backend's snapshot spec gives the law no fact of the compaction keys once
written (the review's minimal fix: `fkdAt` in `backend.Snapshot.spec`'s observation, a
trust-boundary strengthening, the user's decision). (Not to confuse with this draft's `on`, the
auth mode, `kvModelM on`: the send is at `on = false` too, `#7-on` deferred.) -/


/-! ## 3c. The image certificate over `mvccImage` (`InvImage.lean:148`'s `dbImage`) -/

section image
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [bk_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

open backend go_etcd_io.etcd.server.v3.storage in
/-- **`D`'s parts the server's model fixes, besides the store's** (pure; `imageAt` without its
`Key`-bucket/compaction-records and `IdxWf` conjuncts, which move into `mvccImage`): the stored
consistent index `i`, some stored term, the other buckets the committed log's (`bkRestAt`). -/
def imageRestAt (γk : KVNames) (bootLog : List EntryM) (i : w64) (L : List EntryModel) (D : Data) :
    Prop :=
  dget D schema.metaName schema.ciKeyBytes = encMeta i ∧
    (∃ t : w64, dget D schema.metaName schema.termKeyBytes = encMeta t) ∧
    bkRestAt γk.c0 bootLog L D

/-- **The image certificate, restated** (`dbImage`): `D` the image of the KV model of a committed
prefix `A` ending at `i` (the store's part: `mvccImage`, its receipt inside, in place of
`imageAt`'s `keyImageM`/records, `IdxWf` and the separate `⧖ (logCh (kvModel γk A))`), and the
server's parts (`imageRestAt`). The sender makes it by `mvccImage_snapshot.law` at its update
(`senderImage.law`, `dbImageA_of_send`): the state the apply thread's at `(kvModel γk A, crevOf γk
A)` (its `wSt` and `kvApplied` at `A`), its observation `Q` (the stored index in the window, the
tracked buckets' `restModel`: today's `srvBeSnapOk_window`, `bkRestAt_of_rb`); the receiver opens
the snapshot backend with it (`dbImageA_open.law`). -/
def dbImageA (γ : ServerRaftNames) (γk : KVNames) (i : w64) (D : backend.Data) : IProp GF :=
  iprop(∃ (A : List EntryModel) (u : Bool), srvRLogLb γ A ∗
    ⌜uint.Z i = uint.Z γ.ai0 + A.length ∧ imageRestAt γk γ.raft.boot i (γ.pre ++ A) D⌝ ∗
    mvccImage D (kvModel γk A) (crevOf γk A) u)

/-- **The sender's image, from the snapshot's** (proved; the step after `mvccImage_snapshot.law`):
the image of the pinned state's history, with the server's parts the client's observation gave. -/
theorem dbImageA_of_send (γ : ServerRaftNames) (γk : KVNames) (i : w64) (D : backend.Data)
    (A : List EntryModel) (u : Bool)
    (hi : uint.Z i = uint.Z γ.ai0 + A.length) (hr : imageRestAt γk γ.raft.boot i (γ.pre ++ A) D) :
    srvRLogLb (GF := GF) γ A ∗
      mvccImage D (kvModel γk A) (crevOf γk A) u ⊢ dbImageA γ γk i D := by
  iintro ⟨#Hlb, Him⟩
  iunfold dbImageA
  iexists A, u
  iframe Hlb Him
  ipureintro; exact ⟨hi, hr⟩

/-- **The merged snapshot's send** (`createMergedSnapshotMessage`'s `s.be.Snapshot()`, after
`s.KV().Commit()`), derived from the API's `mvccImage_snapshot.law` (its `isMvcc` from `kvStoreInv`)
and the server's builders, **in a cluster that never compacts** (`γr.kv.cmp = false`; F1): the
apply thread, at its applied prefix `A` (its half at the model's `(kvModel A, crevOf A)`, `crevOf A =
-1` there, `crevOf_plain`), with the
whole backend share and the client's observation `Q` of the meta keys and the tracked buckets (the
stored-index window's, `srvBeSnapOk_window`, whose `D`-level reading is `imageRestAt`), gets the
snapshot open over `D` and the image certificate `dbImageA` at the snapshot's index `i`. -/
abbrev senderImage.law : Prop :=
  backend.backend.Snapshot.spec (GF := GF) (hG := hG) →
  mvccImage_snapshot.law (GF := GF) (hG := hG) → kvAus.law (GF := GF) →
  ∀ (kv : GoInterface) (γ : MvccName) (γr : ReadNames) (γs : KVSNames) (i : w64)
    (A : List EntryModel) (B : BkRef) (Pk : IProp GF) (qo : Qp) (R : IProp GF)
    (Q : GMap (GoString × GoString) GoString → GMap GoString backend.BktData → Prop),
  γr.kv.cmp = false →
  (∀ D, Q (backend.hkData B.P D) (backend.rbData B.P D) →
    imageRestAt γr.kv γr.raft.raft.boot i (γr.raft.pre ++ A) D) →
  uint.Z i = uint.Z γr.raft.ai0 + A.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      kvStoreInv kv γ γr false γs ∗ wSt γs (kvModel γr.kv A) (crevOf γr.kv A) ∗
      srvRLogLb γr.raft A ∗ mvccBackend γ 1 B Pk ∗ backend.bOpen B.γB qo ∗ backend.wbTok B.γB ∗
      R ∗ □ (∀ (d : GMap (GoString × GoString) GoString) (r : GMap GoString backend.BktData),
        R -∗ Pk -∗ backend.hkOwn B.γB d -∗ backend.rbOwn B.γB r -∗ ⌜Q d r⌝) }}
    (App (Val (B.b @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty
      @!! go!"Snapshot")) (Val #()))
  {{ (sp : Loc) (D : backend.Data),
      RET #(interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.snapshot.ty) #sp);
      backend.snapOpen sp D ∗ backend.bOpen B.γB qo ∗ R ∗ mvccBackend γ 1 B Pk ∗
      wSt γs (kvModel γr.kv A) (crevOf γr.kv A) ∗ dbImageA γr.raft γr.kv i D }}

/-- **The receiver's backend over the image** (from `mvccBackendFor_open.law`, at the snapshot
opener's post `newPostKP` at `K := snapOpenK`, with the store's part of the payment rights): the
store's resources at the image's history. -/
abbrev dbImageA_open.law : Prop :=
  ∀ (γ : ServerRaftNames) (γk : KVNames) (i : w64) (D : backend.Data) (γB : backend.BNames)
    (P : backend.BParams) (Pk K : backend.BNames → IProp GF) (b : Loc) (gx : GName),
  dbImageA (GF := GF) γ γk i D ∗ □ (∀ γ' b', mvcc.keySized γ' P b') ∗
    backend.newPostKP γB P (fun _ => mvccW gx) Pk K b D ∗ mvccWReg gx ∗
    backend.wbTok γB ∗ backend.wbTok γB ∗ □ (⧗ 1 ={⊤}=∗ backend.wbTok γB) ∗
    ([∗list] _x ∈ List.replicate backend.rdStockN (), backend.bOpen γB backend.rdOpen) ={⊤}=∗
  ∃ (A : List EntryModel) (u : Bool), srvRLogLb γ A ∗
    ⌜uint.Z i = uint.Z γ.ai0 + A.length ∧ imageRestAt γk γ.raft.boot i (γ.pre ++ A) D⌝ ∗
    mvccBackendFor ⟨γB, P, b⟩ (Pk γB) (kvModel γk A) (crevOf γk A) u ∗ backendRest γB P K b D

/-- **The boot's backend for the store** (`NewServer`'s step 4-5, F3: `mvccImage_fresh.law` under an
update, which the boot's fupd absorbs): `backend.New`'s pooled post at the store's write invariant
over fresh data (no `Key` entry, no compaction key: a new cluster's data directory, `bootOk`'s
empty bucket), with the store's part of the payment rights, gives `New`'s `mvccBackendFor` at
`mvccStart` and the client's rest. Derived from `mvccImage_fresh.law` and `mvccBackendFor_open.law`. -/
abbrev bootBackend.law : Prop :=
  mvccImage_fresh.law (GF := GF) → mvccBackendFor_open.law (GF := GF) →
  ∀ (γB : backend.BNames) (P : backend.BParams) (Pk K : backend.BNames → IProp GF) (b : Loc)
    (D : backend.Data) (gx : GName),
  (∀ k, backend.dget D mvcc.keyName k = none) →
  backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName mvcc.schedKeyBytes = none →
  backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName mvcc.finKeyBytes = none →
  □ (∀ γ' b', mvcc.keySized (GF := GF) γ' P b') ∗
    backend.newPostKP γB P (fun _ => mvccW gx) Pk K b D ∗ mvccWReg gx ∗
    backend.wbTok γB ∗ backend.wbTok γB ∗ □ (⧗ 1 ={⊤}=∗ backend.wbTok γB) ∗
    ([∗list] _x ∈ List.replicate backend.rdStockN (), backend.bOpen γB backend.rdOpen) ={⊤}=∗
  mvccBackendFor ⟨γB, P, b⟩ (Pk γB) mvccStart.log mvccStart.crev false ∗ backendRest γB P K b D

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
def restorePreA (kv : GoInterface) (γ : MvccName) (B B' : BkRef) (Pk Pk' : IProp GF)
    (σ' : MvccState) (u : Bool) (L : List w64) (dq : DFrac) (f : GoFunc)
    (Pre Q' Post X Y : IProp GF) (Q : MvccState → IProp GF) : IProp GF :=
  iprop(isMvcc kv γ ∗ threadTok ∗ mvccOpen γ ∗ mvccBackend γ 1 B Pk ∗
    mvccBackendFor B' Pk' σ'.log σ'.crev u ∗ ⌜MvccReachable σ' ∧ σ'.pending = none⌝ ∗
    backend.plHookAt B'.γB dq f ∗ Pre ∗ mvcc.api.hookRun Pk' f Pre Q' ∗ (Q' ={⊤}=∗ Pk' ∗ Post) ∗
    X ∗ backend.commitReq B'.γB B'.P Pk' B'.b X Y ∗
    lease.leaseOwn (mvccLeases γ) L ∅ ∗
    ⌜∀ it lid, (mvcc.pendItems σ'.log []).lookup it = some lid →
      lid ∈ L ∧ (it.Key'.length : Int) < 2 ^ 63 - 1⌝ ∗
    auRestore γ σ' Q)

/-- **The Restore builder** (`EtcdServer.applySnapshot`, linked: `Link.lean:2407`): from the apply
thread's state at the applied prefix `A` (its halves, the open token, the old backend's whole share,
its thread token), the snapshot's prefix `A'` extending it (both committed, `A` the shorter: the
snapshot's index is above the applied one), the new backend's store resources at the image's
history (`dbImageA_open.law`), the new backend's unset hook (`plHook B'.γB nil` at `dq = ½`,
`f = nil`: `hookRun`'s view-shift row, the hook set after `Restore`, `server.go:1078`), the apply
protocol's `Pre`/`Q'`/`Post` across the resumed compaction's lock, the commit request `True ⇒ True`
(`commitReq_true`), the lessor recovered over the new backend (`leaseOwn … Ls ∅`, `Recover` before
`Restore`), and the model's facts: the restored state reachable (`kvModel_reachable.law`), its
compaction revision permitted (the committed compaction entries' claims), its leased items' leases
live (the image's lease bucket, `bkRestAt`: the workload has no lease, so `Ls = []` and no item) —
the contract's whole precondition, its update committing the apply thread to the restored state. -/
abbrev restoreArgs.law : Prop :=
  ∀ (kv : GoInterface) (γ : MvccName) (γr : ReadNames) (on : Bool) (γs : KVSNames)
    (log : mvcc.Log) (c : Int) (A A' : List EntryModel) (B B' : BkRef) (Pk : BkRef → IProp GF)
    (u : Bool) (Ls : List w64) (dq : DFrac) (f : GoFunc) (Pre Q' Post : IProp GF),
  let σ' := stAt (kvModelM on γr.kv A') (crevOf γr.kv A')
  log = kvModelM on γr.kv A → c = crevOf γr.kv A → A <+: A' → MvccReachable σ' →
  (∀ it lid, (mvcc.pendItems σ'.log []).lookup it = some lid →
    lid ∈ Ls ∧ (it.Key'.length : Int) < 2 ^ 63 - 1) →
  kvStoreInv (GF := GF) kv γ γr on γs ∗ wSt γs log c ∗ crOwn γs c ∗ srvRLogLb γr.raft A' ∗
    crevOk γr σ'.crev ∗ threadTok ∗ mvccOpen γ ∗ mvccBackend γ 1 B (Pk B) ∗
    mvccBackendFor B' (Pk B') σ'.log σ'.crev u ∗
    backend.plHookAt B'.γB dq f ∗ Pre ∗ mvcc.api.hookRun (Pk B') f Pre Q' ∗
    (Q' ={⊤}=∗ Pk B' ∗ Post) ∗ lease.leaseOwn (mvccLeases γ) Ls ∅ ⊢
  restorePreA kv γ B B' (Pk B) (Pk B') σ' u Ls dq f Pre Q' Post iprop(True) iprop(True)
    (fun σ => iprop(⌜σ = stAt log c⌝ ∗ wSt γs σ'.log σ'.crev ∗ crOwn γs σ'.crev))

end restore

/-! ## 4. The apply chain's environment and resources -/

section apply
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **A chain's environment, restated** (`apply.AEnv`): the store handle `kv` (was the inner
store's location `s`) and its name `γ : MvccName` (was `StoreNames`), the server's state names
`γs`, the raft witness `Nx`, the compaction permit `Cp`, the backend tie `BkTie` (abstract to the
apply package), **the batch lock's invariant per backend `Pk : BkRef → IProp`** (was the fixed
`P`; xreview §2: `Restore` gives `mvccBackend γ 1 B' (Pk B')`, `batchLockInv γA (metaTM B'.γB B'.P)`
depending on the backend) and the hook `f : GoFunc` (was `val`). The rest as today. -/
structure AEnvA (GF : BundledGFunctors) where
  kv : GoInterface
  γ : MvccName
  γs : KVSNames
  Nx : mvcc.Log → IProp GF
  Pk : BkRef → IProp GF
  f : GoFunc
  RD : IProp GF
  γrev : GName
  authMode : auth.AuthMode
  FS : IProp GF
  ciC : IProp GF → w64 → Prop
  RO : apply.RestM → IProp GF
  RW : IProp GF
  γbe : GName
  Cp : Int → IProp GF
  BkTie : BkRef → IProp GF
  cmp : Bool := false
  cret : Nat := 0

/-- **The builders the chain uses** (persistent; in `backendOptsOk`'s KV clause): `kvAus.law`'s
apply-thread conjuncts at `E.Nx`/`E.Cp`. -/
def envAus (E : AEnvA GF) : IProp GF :=
  iprop(□ (∀ log c (X : IProp GF), wSt E.γs log c -∗ (wSt E.γs log c -∗ X) -∗
        auBegin E.γ (stAt log c) X) ∗
    □ (∀ log c (X : IProp GF), wSt E.γs log c -∗ (wSt E.γs log c -∗ X) -∗
        auRead E.γ (fun σ => iprop(⌜σ = stAt log c⌝ ∗ X))) ∗
    □ (∀ log c pend, wSt E.γs log c -∗ E.Nx (mvcc.commitLog log pend) -∗
        auEnd E.γ (stAt log c) pend (wSt E.γs (mvcc.commitLog log pend) c)) ∗
    □ (∀ log c (rev : w64), ⌜sint.Z rev < log.length⌝ → wSt E.γs log c -∗ crOwn E.γs c -∗
        E.Cp (sint.Z rev) -∗ auCompact E.γ rev (fun σ => iprop(⌜σ = stAt log c⌝ ∗
          wSt E.γs log (apply.cmpRevAfter c rev) ∗ crOwn E.γs (apply.cmpRevAfter c rev)))) ∗
    □ (∀ log c, wSt E.γs log c ={⊤}=∗ wSt E.γs log c ∗ E.Nx log ∗ ⧖ (mvcc.logCh log) ∗
        ⌜MvccReachable (stAt log c) ∧ log.length + 3 ≤ 2 ^ 63⌝))

/-- **The store's backend, as the apply thread holds it** (xreview §2): the current backend `B`
at its batch lock's invariant `E.Pk B`, its hook `E.f` frozen, the server's tie. The share is the
whole one (the cross-review's form had `∃ q`): the apply thread is its only holder (it lends a share
to txn, `Revoke` and `Commit` only within a call), and the merged snapshot's pin (§3b) and
`Restore` need it whole. -/
def kvBk (E : AEnvA GF) : IProp GF :=
  iprop(∃ B : BkRef, mvccBackend E.γ 1 B (E.Pk B) ∗ hookIs B E.f ∗ E.BkTie B)

/-- **The live leases of the state `s`** (`apply.leasesLive`), at the store's lessor names. -/
def leasesLiveA (E : AEnvA GF) (s : List EtcdKv) : IProp GF :=
  iprop(∃ L : List w64, txn.leasesKnown L s ∗
    lease.lessorUser (mvccLeases E.γ) L (mvcc.leaseItemsOf s))

/-- **The apply thread's KV resources at the log `log`** (`apply.kvOwn`, restated): its half of the
state, the backend's share and hook, the live leases, the auth store's reader resource. The
thread's token is not in it (xreview §7: the apply goroutine's one token is lent separately to
`applyConfChange`, `restoreAlarms`, `applySnapshot`); the chain's specs take `threadTok` beside it,
as txn's entry specs do. -/
def kvOwnA (E : AEnvA GF) (log : mvcc.Log) : IProp GF :=
  iprop((∃ c : Int, wSt E.γs log c) ∗ kvBk E ∗ leasesLiveA E (mvcc.stateAfter log) ∗ E.RD)

/-- **The apply thread's compaction resources at `c`** (`apply.cmpOwn`, restated). -/
def cmpOwnA (E : AEnvA GF) (c : Int) : IProp GF :=
  iprop(mvccOpen E.γ ∗ crOwn E.γs c)

/-- **The critical-section contract** over the API's `hookRun` (one definition: txn's `csA` is it;
the cross-review's §8: to live beside `hookRun` in the API). -/
def csContractA (P : IProp GF) (f : GoFunc) (Pre Q Post : IProp GF) : IProp GF :=
  iprop(Pre ∗ mvcc.api.hookRun P f Pre Q ∗ (Q ={⊤}=∗ P ∗ Post))

/-- `apply.mPre`, restated: the apply thread's resources without the backend share, the chain's,
and the backend share with the contract at its lock's invariant (`Pre`/`Q`/`Post` the caller's,
at the backend `B` the tie names). -/
def mPreA (E : AEnvA GF) (c : apply.Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    IProp GF :=
  iprop((∃ cr : Int, wSt E.γs log cr) ∗ leasesLiveA E (mvcc.stateAfter log) ∗ E.RD ∗
    apply.chainRes c a info ∗
    ∃ B : BkRef, mvccBackend E.γ 1 B (E.Pk B) ∗ hookIs B E.f ∗ E.BkTie B ∗
      csContractA (E.Pk B) E.f Pre Q Post)

/-- **The witnesses of the logs `rq` may commit** (`apply.certPre`, restated). The arms with no
`chainStep` outcome but an end at `pend = []` (`DeleteRange`'s `ok = false`, `Put`'s
`ErrKeyNotFound`) take `E.Nx log` from the writer's facts (`envAus`'s last conjunct). -/
def certPreA (E : AEnvA GF) (c : apply.Chain) (rq : apply.IRRModel) (log : mvcc.Log) : IProp GF :=
  iprop(□ ∀ oc : apply.Outcome, ⌜apply.chainStep apply.backendStep c rq log oc⌝ -∗
    E.Nx (oc.logAfter log))

/-- The success arm's channel fact for the requester's `<-physc`. -/
def cmpChanA (crev : Int) (rev : w64) (ch : GoChan) : IProp GF :=
  iprop(⌜crev < sint.Z rev⌝ -∗ compactChanOk ch)

/-- **`a.Compaction(cr)`, restated**: as round 14, `threadTok` beside `mPreA` (xreview §7).
(Superseded 2026-11-05, decided by the coordinator: `⌜1 ≤ sint.Z rev⌝` added, matching
`KV.Compact.contract`'s and `EtcdServer.Compact.spec`'s; `crevOk γr (-1)` admitted `rev = -1`.)
`backendIsA E p` is `backendIs` with its KV clause `isMvcc opts.KV' E.γ ∗ ⌜opts.KV' = E.kv⌝ ∗
envAus E`. -/
abbrev applierV3backend.Compaction.specA
    (backendIsA : AEnvA GF → Loc → IProp GF) : Prop :=
  ∀ (E : AEnvA GF) (p cr : Loc) (rev : w64) (log : mvcc.Log) (crev : Int) (Pre Q Post : IProp GF)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      backendIsA E p ∗ apply.compactionIs cr rev ∗ ⌜1 ≤ sint.Z rev ∧ sint.Z rev < log.length⌝ ∗
      E.Cp (sint.Z rev) ∗
      threadTok ∗
      mPreA E .backend
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend.ty) #p)
        info log Pre Q Post ∗ cmpOwnA E crev }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend.ty
      @!! go!"Compaction")) (Val #cr))
  {{ (resp : Loc) (ch : GoChan) (trace : Loc) (err : GoInterface),
      RET (PairV (PairV (PairV #resp #ch) #trace) #err);
      threadTok ∗ kvOwnA E log ∗ (Post ∨ Pre) ∗ cmpOwnA E (apply.cmpRevAfter crev rev) ∗
      apply.cmpAnswerIs .backend crev rev resp ch trace err ∗ cmpChanA crev rev ch }}

end apply

/-! ## 5. The lessor -/

section lease
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`le.Revoke(id)`, restated** (xreview §3): one update, the deleter's `Write`'s begin at `σ₀`
whose payload is the end updates of exactly the lease's deletions (`auBegin γ σ₀ (auEnd γ σ₀ dels
Y)`: the builders' continuation form; the writer's half is exclusive, so the two cannot be built
apart). `rd ≠ nil` is `mvccDeleter`'s (round 15). The sort's premise `(stateAfter σ₀.log).length ≤
2 ^ 62` stays a premise, which the caller now derives from the writer's receipt (`⧖ (logCh σ₀.log)`,
the writer's facts; a live key-value is a change, `receiptBound ≤ 2 ^ 48`; the tester from its keys).
* `id` not live: `ErrLeaseNotFound`, `Pre` back (2026-11-06: no update taken, below);
* `id` live: `Y`, `Post`, the lease's record deleted, `id` out of the live set.
The proof: `rd()` by `mvccDeleter` (its update this one), the deletes by `Txn.DeleteRange`
(`shapes.law`), the record's delete by `mvccTxn_leaseDelete.law` (which gives `End`'s triple, not
`mvccTxn`: the backend's batch session admits only `Unlock` after an `UnsafeDelete`), `End`'s triple
with `P` from the hook's `Q` (`csContractA`) and the nested end update.
**The begin state's reachability** (decided by the coordinator, 2026-11-05; superseding the
draft's premise without it): `MvccReachable σ₀ ∧ σ₀.log.length + 3 ≤ 2 ^ 63`, which the deletes'
`delKeys` need (`txn.delKeys_eq`'s `LogOk`) and the API gives only through `mvccState_reachable.law`
(`isMvcc`, not held here); the server's caller has it from the writer's facts, the tester from
`mvccState_reachable.law`.
**The update only for a live lease** (decided by the coordinator, 2026-11-06; superseding the update
taken always and given back in the not-live arm): `if decide (id ∈ L) then auBegin γ σ₀ (auEnd γ σ₀
dels Y) else True`, and the not-live arm without it. The server builds the update from its writer's
half (`envAus`' begin builder puts `wSt` in the update's private state), which no law recovers from
an unused update; the code returns `ErrLeaseNotFound` before `rd()`, as txn's `Put` for a lease
(`notes/mvcc-migration/server.md`, "Found", third session, (2)). -/
abbrev lessor.Revoke.specA : Prop :=
  ∀ (lp : Loc) (γ : MvccName) (id : w64) (rd : GoFunc) (q : Qp) (B : BkRef) (P : IProp GF)
    (f : GoFunc) (σ₀ : MvccState) (L : List w64) (r : GMap GoString backend.BktData)
    (Pre Q Post Y : IProp GF),
  let γl := mvccLeases γ
  let dels := mvcc.leaseDels (mvcc.stateAfter σ₀.log) id
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      lease.lessorInv lp γl ∗ threadTok ∗ lease.rdOwn γl rd ∗ mvccDeleter rd γ ∗
      mvccBackend γ q B P ∗ hookIs B f ∗ csContractA P f Pre Q Post ∗
      ⌜σ₀.pending = none ∧ (mvcc.stateAfter σ₀.log).length ≤ 2 ^ 62 ∧
        MvccReachable σ₀ ∧ σ₀.log.length + 3 ≤ 2 ^ 63⌝ ∗
      (if decide (id ∈ L) then auBegin γ σ₀ (auEnd γ σ₀ dels Y) else iprop(True)) ∗
      lease.leaseOwn γl L (mvcc.leaseItemsOf (mvcc.stateAfter σ₀.log)) ∗ lease.leaseRevokers γl L ∗
      backend.rbPart B.γB (· = mvcc.leaseName) r ∗ ⌜mvcc.leaseParams B.P⌝ ∗ lease.lessorBeOn lp B.b }}
    (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty
      @!! go!"Revoke")) (Val #id))
  {{ (err : GoInterface), RET #err; threadTok ∗ lease.rdOwn γl rd ∗ mvccBackend γ q B P ∗
      lease.lessorBeOn lp B.b ∗
      ((⌜id ∉ L⌝ ∗
          (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound ↦□
            GoInterface.ok e ∗ ⌜err = GoInterface.ok e⌝) ∗
          Pre ∗
          lease.leaseOwn γl L (mvcc.leaseItemsOf (mvcc.stateAfter σ₀.log)) ∗ lease.leaseRevokers γl L ∗
          backend.rbPart B.γB (· = mvcc.leaseName) r) ∨
       (⌜id ∈ L ∧ err = GoInterface.nil⌝ ∗ Y ∗ Post ∗
          lease.leaseOwn γl (L.filter (· != id))
            (mvcc.leaseItemsOf (mvcc.stateAfter (mvcc.commitLog σ₀.log dels))) ∗
          lease.leaseRevokers γl (L.filter (· != id)) ∗
          backend.rbPart B.γB (· = mvcc.leaseName)
            (mvcc.rbDel r mvcc.leaseName (u64Le id).reverse))) }}

/-- **`le.Grant(id, ttl)`, restated**: only the critical-section contract changes. -/
abbrev lessor.Grant.specA : Prop :=
  ∀ (lp : Loc) (γl : GName) (id ttl : w64) (L : List w64) (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64)
    (P : IProp GF) (f : GoFunc) (T R : IProp GF) (Rb : GMap GoString backend.BktData → IProp GF)
    (rb : GMap GoString backend.BktData) (Pre Q Post : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lease.lessorInv lp γl ∗
      lease.lessorCfg lp ∗ lease.lessorBackend lp P #f T R Rb ∗ lease.leaseOwn γl L I ∗
      lease.leaseRevokers γl L ∗ csContractA P f Pre Q Post ∗ T ∗ R ∗ Rb rb ∗
      lease.leaseGranted γl id }}
    (App (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty
      @!! go!"Grant")) (Val #id)) (Val #ttl))
  {{ (l : Loc) (err : GoInterface), RET (PairV #l #err); R ∗
      ((⌜err ≠ GoInterface.nil ∧ (id = W64 0 ∨ 9000000000 < sint.Z ttl ∨ id ∈ L)⌝ ∗
        lease.lessorErrIs err ∗ lease.leaseOwn γl L I ∗ lease.leaseRevokers γl L ∗ Pre ∗ Rb rb) ∨
      (⌜err = GoInterface.nil ∧ l ≠ null ∧ id ≠ W64 0 ∧ sint.Z ttl ≤ 9000000000 ∧ id ∉ L⌝ ∗
        lease.leaseOwn γl (L ++ [id]) I ∗ lease.leaseRevokers γl (L ++ [id]) ∗ Post ∗
        lease.lsF go!"ID" l ↦□ id ∗ ∃ mt : w64, lease.lF go!"minLeaseTTL" lp ↦□ mt ∗
        lease.lsF go!"ttl" l ↦□ lease.grantTTL mt ttl ∗
        Rb (mvcc.rbSet rb mvcc.leaseName (u64Le id).reverse
          (lease.leaseEnc id (lease.grantTTL mt ttl) (W64 0))))) }}

end lease

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

/-- **The client model's server log** (v3rpc's `srvLog`, restated over `histLb`). -/
def srvLogA (γr : ReadNames) (on : Bool) (γs : KVSNames) (log : mvcc.Log) : IProp GF :=
  iprop(histLb γr on γs log ∗ ⌜txn.LogSmall log ∧ mvcc.LogPutsLe etcdKeyMax log⌝)

/-- `srvAppliedBody`'s changed conjunct: the applied log a floor (was `mvcc.idxCert E.γ.idx L`). -/
def appliedFloorA (E : AEnvA GF) (L : mvcc.Log) : IProp GF := kvLogLb E.γs L

/-- **The claims' floor facts** (`srvFloorFacts`, restated). -/
def srvFloorFactsA (slog : GName) (_id : w64) (_d : List w8) (γf : GName) : IProp GF :=
  iprop(∃ F : mvcc.Log, floorAt γf F ∗ monoListLbOwn slog F)

/-- **A served read's call resources** (`srvRdCall`, restated): the thread's token in place of the
store's reader slot. -/
def srvRdCallA (s : Loc) (E : AEnvA GF) (γr : ReadNames) (c : w64) : IProp GF :=
  iprop(threadTok ∗ srvLgReader s ∗ committedAtLeast γr c ∗ srvReadReader s γr ∗ E.RD)

/-- **A successful `Range`'s outcome, restated** (`rangeReadOkM`; xreview §5): the log read is a
floor, the model of a committed raft log, well formed, with its receipt (from `kvReadAt`), read
after the read index unless serializable, the caller's result as today. -/
def rangeReadOkA (on : Bool) (E : AEnvA GF) (γr : ReadNames) (c : w64) (F : mvcc.Log)
    (o : OpFull) (resp : Loc) (Q : List EntryModel → IProp GF) : IProp GF :=
  iprop(∃ (log : mvcc.Log) (crev : Int), kvLogLb E.γs log ∗ kvNx γr on log ∗
    ⧖ (mvcc.logCh log) ∗ ⌜mvcc.LogWf' log ∧ 2 ≤ log.length ∧ log.length + 3 ≤ 2 ^ 63 ∧ F <+: log⌝ ∗
    (if o.base.serializable then iprop(True) else readLogOk γr c log) ∗
    (if o.base.serializable then iprop(True) else
      ∃ L : List EntryModel, srvRLogLb γr.raft L ∗ ⌜kvModelM on γr.kv L = log⌝ ∗ □ Q L) ∗
    txn.rangeResult resp GoInterface.nil log (W64 ((log.length : Int) - 1)) crev o true ∗
    txn.respHdrOwn (structFieldRef go_etcd_io.etcd.api.v3.etcdserverpb.RangeResponse go!"Header" resp))

/-- `newHeader`'s post, restated (xreview §5): a floor, the model's, well formed, its receipt. -/
def newHeaderPostA (E : AEnvA GF) (γr : ReadNames) (on : Bool) (log : mvcc.Log) (rev : w64) :
    IProp GF :=
  iprop(kvLogLb E.γs log ∗ kvNx γr on log ∗ ⧖ (mvcc.logCh log) ∗
    ⌜mvcc.LogWf' log ∧ log ≠ [] ∧ rev = W64 ((log.length : Int) - 1)⌝)

/-- **client/v3's `idxCert_logOk` (`KVService.lean:1515`), restated** over what `rangeReadOkA` and
`newHeaderPostA` give: proved (as today's, by `preceipt_lt`). -/
theorem logOk_of_receipt (log : mvcc.Log) (hrb : receiptBound GF ≤ 2 ^ 62) :
    ⧖ (mvcc.logCh log) ∗ ⌜mvcc.LogWf' log ∧ log.length + 3 ≤ 2 ^ 63⌝ ⊢
      (⌜mvcc.LogWf' log ∧ log.length < 2 ^ 63 ∧ txn.LogSmall log⌝ : IProp GF) := by
  iintro ⟨Hr, %Hp⟩
  ihave %Hm := preceipt_lt _ $$ Hr
  ipureintro
  refine ⟨Hp.1, by omega, ?_⟩
  unfold txn.LogSmall txn.logChanges; unfold mvcc.logCh at Hm; omega

/-- **The compactor's revision lower bound** (`srvRevLb`, restated): raft-only. -/
def srvRevLbA (γr : ReadNames) (on : Bool) (n : Int) : IProp GF :=
  iprop(∃ A : List EntryModel, srvRLogLb γr.raft A ∗ ⌜n < (kvModelM on γr.kv A).length⌝)

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
