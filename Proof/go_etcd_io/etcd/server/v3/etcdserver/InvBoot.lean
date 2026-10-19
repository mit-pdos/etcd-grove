/-
**What `NewServer` is proved over: `bootstrap`'s result and the names-only constructors'
contracts** (the server-construction unit's stage N0, 2026-10-16; D13b, D13d,
`notes/decisions.md`). Lean-first (no Rocq counterpart). Unit N1's file: the contracts here are
used by `NewServer`'s proof alone (unit N2 does not read them), and N1 refines them.

* **`bootstrap`'s contract** (`bootstrapContract`, D13b) is a premise of `NewServer.spec`, a triple
  in its precondition, not an axiom. Its raft configuration is `raftConfig`'s (`bootstrap.go:572`)
  (`CheckQuorum: true` and `PreVote` as `cfg` sets it, both covered by the raft start result since
  2026-10-17; until then `NewServer.spec` required `cfg.PreVote` off). On success the bootstrapped record carries `bootOk`:
  - the records `NewServer` reads (`b`, `b.storage`, `b.storage.backend`, `b.storage.wal`,
    `b.cluster`, `b.raft`);
  - `b.raft` with `NodeStartSpec`'s premises on it (the raft config valid, `CheckQuorum`/
    `PreVote` either way, the fresh registered `MemoryStorage`, the peers and the bootstrap log, the
    `InitialState` closure, `Marshal` at the peers' conf changes) and the cluster's
    `IsIDRemoved` contract;
  - the cluster (`isRaftCluster`, its id, this node's id, the remote members, read-only; its
    `Version()` monotone, `clusterVersionMono`, D17);
  - the consistent index at `0` (`isCI`, `ciOwner` of the backend, the applying index at `0`)
    and the apply protocol's names and invariant (`consInv`, the apply thread's half at the start:
    the backend's batch lock's resource names them, so they exist before the backend; the
    protocol's allocation is `consInv_alloc`, `BuildAlloc.lean`), the backend's meta keys at
    `(0, 0)` (a new cluster's fresh backend);
  - the backend of the real instance `d` with the server's hooks (`server_kv_backend_hooks`'s
    premises but the post-lock hook's, which `NewServer` sets: the hook's half, its open fraction,
    the write budget);
  - `b.Close()` returns (the error paths' deferred close).
* **`transportStarted γn t`**: the `rafthttp.Transport` after `Start` (names-only): its `Send` of
  messages with their bundles into the network `γn` (`netBundle`, D21 M2), its `Stop` and its
  `ActiveSince` (`rafthttp.isTransporter`); `isRNTransport` for every environment whose messages
  carry the bundle (`isRNTransport_of_net`).
* The pending constructors' contracts (`lease.NewLessor`, `auth.NewTokenProvider`,
  `auth.NewAuthStore`, `v3compactor.New`, `rafthttp.Transport.Start`/`AddRemote`/`AddPeer`,
  `v3alarm.NewAlarmStore`) are their `Spec/` files, listed `?` in the server's link: hypotheses
  of `NewServer`'s linked result until N1 settles them (then axioms at the trust boundary).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NodeStart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBuild
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.CindexBackend
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BootBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.HooksBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendBridge
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.HooksLoeb
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Snapshot
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Net

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [MemStorReg GF]

/-- A cluster member (`*membership.Member`), read-only, its peer URLs parsing (unit N4,
2026-10-17: `membership.peerURLsOk`, the transport's `AddRemote` panics otherwise) and (D21 M2,
2026-10-19) the directory's for its id (`dir`: the URLs serve that member). -/
def memberRO (dir : w64 → List GoString) (m : Loc) : IProp GF :=
  iprop(⌜m ≠ null⌝ ∗ ∃ (v : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member)
      (us : List GoString), m ↦□ v ∗ v.RaftAttributes'.PeerURLs' ↦*□ us ∗
    ⌜membership.peerURLsOk us ∧ us = dir v.ID'⌝)

instance memberRO_persistent (dir : w64 → List GoString) (m : Loc) :
    Persistent (memberRO (GF := GF) dir m) := by
  unfold memberRO; infer_instance

/-- **A member returned by `Members()`, its URLs the directory's** (D21 M2, 2026-10-19): owned
(`membership.memberIs`'s fields), with id `id`, its peer URLs `dir id`. -/
def memberDirIs (dir : w64 → List GoString) (m : Loc) (id : w64) : IProp GF :=
  iprop(⌜m ≠ null⌝ ∗ ∃ (pu cu : GoSlice) (il : Bool) (nm : GoString) (pus cus : List GoString),
    membership.mIDAddr m ↦ id ∗ membership.mPeerURLsAddr m ↦ pu ∗
    membership.mIsLearnerAddr m ↦ il ∗ membership.mNameAddr m ↦ nm ∗
    membership.mClientURLsAddr m ↦ cu ∗ pu ↦* pus ∗ cu ↦* cus ∗
    ⌜membership.peerURLsOk pus ∧ pus = dir id⌝)

/-- **A bucket of the backend fresh** (opaque, D14g, 2026-10-17): the bbolt file of the backend
`γB` was created empty by `bootstrap` (a new cluster's data directory), so its bucket `name` holds
no data, and only the store that owns it (the lessor `"lease"`, the auth store `"auth"`) writes it:
the owner's token, which its constructor consumes. The model cannot state a bucket's contents to
its clients (the readers' view leaves out every bucket but `Key`: `mvcc.bridgeParams`), so this
is a name for what `bootstrap`'s contract promises and the constructors' axioms
(`lease.NewLessor`, `auth.NewAuthStore`) rely on: their recovery decodes the bucket (a panic on
undecodable data) and the auth store reads its enabled flag (unset). -/
opaque bkFresh (γB : backend.BNames) (name : GoString) : IProp GF

/-- **A fresh alarm store** `a` (opaque, exclusive; D14i, 2026-10-17): made by
`v3alarm.NewAlarmStore` over a fresh alarm bucket and not yet handed to an applier, it has no
alarm (`Activate`, the only writer of its map, is in its apply contract, which taking this token
gives: the axiom's postcondition). -/
opaque alarmFresh (a : Loc) : IProp GF

/-- **The lessor's checkpointer's effects** (opaque, the named premise of D14g, 2026-10-17): the
lessor's loop, once its lessor is promoted, calls the server's checkpointer (`NewServer`'s closure
over `raftRequest`, installed when the `LeaseCheckpoint` feature is on), which proposes outside the
request path's model. A premise of `lease.NewLessor`'s axiom and so of `NewServer.spec`; nothing in
the model proves or refutes it. (Until D21 M2, 2026-10-19, it had a sibling, `transportEffectsOk`,
the transport's goroutines' effects, now the network contract: `rafthttp/Net.lean`.) -/
opaque ckptEffectsOk : Prop

/-- **The auth store's records fit bbolt's value bound** (opaque, a workload premise; unit N4,
2026-10-17): a user's record grows with its roles and a role's with its permissions, each grant
within the request size bound; a record above bbolt's `MaxValueSize` (`2 ^ 31 - 2` bytes) makes
the backend's put fatal (`issues/etcd-backend-put-value-too-large-fatal.md`). The model does not
keep the auth store's contents, so the bound is named, a premise of `auth.NewAuthStore`'s axiom
and of `NewServer.spec`. -/
opaque authRecordsFit : Prop

/-- **The bootstrapped record `b`** (see the file header) of the configuration `cfg` for this node `id` of the cluster with
raft's names `γ` and the bootstrap log `bootLog`, the backend's write-back budget `N + 7` (D14g,
2026-10-17: what the backend has, within its `2 ^ 40` bound, `backend.bgOk`: `N` for the applied
entries, `NewServer.spec`'s lifetime bound, and seven for the construction: `mvcc.New` two,
`NewLessor` one, `NewAuthStore` two, `NewAlarmStore` one, `SetTxPostLockInsideApplyHook` one;
until then `2 ^ 64 + 3`, which no backend has); the post-lock hook unset (nil). -/
def bootOk (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (γ : RaftNames) (id : w64)
    (bootLog : List EntryM) (N : Nat) (dir : w64 → List GoString) (b : Loc) : IProp GF :=
  iprop(∃ (bs : bootstrappedServer) (sto : bootstrappedStorage) (bk : bootstrappedBackend)
      (bw : bootstrappedWAL) (bc : bootstrappedCluster) (bv : bootstrappedRaft) (cv : Config)
      (lok : GoInterfaceOk) (γs : MemStorNames) (pv : List Peer) (ps : List w64)
      (ctxs : List (List w8)) (rms : List Loc) (cid : w64) (cil : Loc) (γA : ApplyNames)
      (d : mvcc.KBReal) (D : backend.Data),
    -- the records
    "Hb" ∷ b ↦ bs ∗ "Hsto" ∷ bs.storage' ↦ sto ∗ "Hbk" ∷ sto.backend' ↦ bk ∗
    "Hbw" ∷ sto.wal' ↦ bw ∗ "Hbc" ∷ bs.cluster' ↦ bc ∗ "Hbv" ∷ bs.raft' ↦ bv ∗
    -- `b.raft`: `NodeStartSpec`'s premises
    "%Hraft" ∷ ⌜bv.lg' ≠ null ∧ bv.heartbeat' ≠ W64 0 ∧
      ConfigValid cv ∧ cv.Logger' = interface.ok lok ∧
      cv.Storage' = memStorIface bv.storage' ∧
      sint.Z cv.MaxInflightMsgs' < 2 ^ 62 ∧
      cv.DisableProposalForwarding' = false ∧ cv.ReadOnlyOption' = W64 0 ∧
      cv.DisableConfChangeValidation' = false ∧
      (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) ∧
      cv.AsyncStorageWrites' = false ∧ cv.Applied' = W64 0 ∧
      cv.ID' = id ∧
      ps = pv.map Peer.ID' ∧ ps ≠ [] ∧ ps.Nodup ∧ W64 0 ∉ ps ∧ (ps.length : Int) ≤ 2 ^ 62 ∧
      cv.ID' ∈ ps ∧ γ.reCfg = GMap.listToSet ps ∧ γ.reBoot = bootLog ∧
      BootLogOk γ.reCCOk ps bootLog ∧
      -- (2026-10-19, raft#168) no peer a witness: etcd's `bootstrap` never sets `IsWitness`
      (∀ p ∈ pv, p.IsWitness' = false)⌝ ∗
    -- (D21 M3, 2026-10-19) raft's no-snapshot mode (`RaftNames.reNoSnap`, what
    -- `ownRaftGhost_alloc_boot` gives the servers), so raft sends no snapshot, and the fresh
    -- `MemoryStorage` at the cap `1` (`MemStorNames.cap`, `NewMemoryStorage`'s choice): never
    -- compacted past index `1`, which the mode needs (`StartNode`'s `NsCap`). (D19p to D21 M3: a
    -- one-member cluster, `"%Hone"`, raft's tracked bound this node alone.)
    "%Hnosnap" ∷ ⌜γ.reNoSnap = true ∧ γs.cap = 1⌝ ∗
    "Hc" ∷ bv.config' ↦ cv ∗ "#Hlok" ∷ isLogger lok ∗
    "#Hreg" ∷ memStorReg bv.storage' γs ∗
    -- (D19r (B), 2026-10-18) the registry's authority, given empty, back with the new storage
    "Hrauth" ∷ memStorRegAuth (GMap.insert bv.storage' γs.tuple (∅ : GMap Loc MemStorNamesRec)) ∗
    "#Hsi" ∷ isStorage (memStorIface bv.storage') ∗
    "Hstor" ∷ ownStorage (memStorIface bv.storage') memStorEmpty ∗
    "#Hinit" ∷ □ (∀ (Φ : val → IProp GF) (ss' : entryID),
       ownStorage (memStorIface bv.storage') { memStorEmpty with ss := ss' } -∗
       memSnapTok bv.storage' γs memStorEmpty -∗
       (∀ (hp cs : Loc) (al : Bool),
        ownStorage (memStorIface bv.storage') { memStorEmpty with ss := ss' } -∗
        memSnapTok bv.storage' γs memStorEmpty -∗
        hsOpt hp (HardStateM.mk (W64 0) (W64 0) (W64 0)) -∗
        csPts cs DFrac.discard (ConfStateM.mk [] [] [] [] false) al -∗
        Φ (PairV (PairV #hp #cs) #interface.nil)) -∗
       WP (App (Val #(methods (go.GoType.PointerType MemoryStorage.ty) go!"InitialState" #bv.storage'))
         (Val #())) {{ Φ }}) ∗
    -- (D17d, 2026-10-18) the application's snapshot token of the fresh storage (`NewMemoryStorage`
    -- gives it), which `InitialState` borrows and `run`'s `Snapshot()` reads
    "Htok" ∷ memSnapTok bv.storage' γs memStorEmpty ∗
    "Hpeers" ∷ bv.peers' ↦* pv ∗ "#Hctx" ∷ peersCtx pv ctxs ∗
    "#Hmarshal" ∷ bootMarshal ps ctxs bootLog ∗
    -- the cluster
    "#Hcl" ∷ rnClusterOk bc.cl' ∗ "#Hrc" ∷ membership.isRaftCluster bc.cl' ∗
    "#Hcid" ∷ membership.clusterCid bc.cl' cid ∗ "%Hid" ∷ ⌜bc.nodeID' = id⌝ ∗
    -- (audit B4a, 2026-10-18) its `versionChanged` field, owned (the cluster not yet shared):
    -- `NewServer`'s `SetVersionChangedNotifier` writes it without the lock, and the cluster's
    -- apply contract `Hisc` (whose `SetVersion` reads it) is for after, the field read-only
    "Hvcn" ∷ (∃ v : Loc, membership.rcVersionChangedAddr bc.cl' ↦ v) ∗
    "#Hrms" ∷ bc.remotes' ↦*□ rms ∗ "#Hrmsi" ∷ ([∗list] m ∈ rms, memberRO dir m) ∗
    -- (D21 M2, 2026-10-19) the members' records name each member's own URLs (`dir`, D21b's
    -- deployment fact): `Members()` returns members whose peer URLs are the directory's
    "#Hmembers" ∷ □ (∀ Φ : val → IProp GF,
      (∀ (sl : GoSlice) (ms : List (Loc × w64)), sl ↦* ms.map Prod.fst -∗
        ([∗list] p ∈ ms, memberDirIs dir p.1 p.2) -∗ Φ #sl) -∗
      WP (App (Val (bc.cl' @!! go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"Members"))
        (Val #())) {{ Φ }}) ∗
    -- the cluster's contracts (unit N4, 2026-10-17): the lessor's (`Version()`), and the apply
    -- package's at the backend's batch lock and any frozen hook (its writes: one write-back
    -- each, `membershipBackend`'s `LockInsideApply`/`Unlock`, as the stores', D14f)
    "#Hclok" ∷ lease.clusterOk (interface.mkOk (go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty) #bc.cl') ∗
    -- (srvBuildGap's rows, 2026-10-17) its `Version()` monotone, for `start`'s
    -- `clusterVersionOk`
    "#Hcvm" ∷ (∃ γcv : GName, clusterVersionMono bc.cl' γcv) ∗
    "#Hisc" ∷ □ (∀ (γ' : mvcc.StoreNames) (f : GoFunc), ⌜γ'.kb = some d⌝ -∗
      backend.plHookRO d.γB f -∗ ⌜f ≠ func.nil⌝ -∗
      (∃ n : Loc, membership.rcVersionChangedAddr bc.cl' ↦□ n) -∗
      apply.isCluster bc.cl' γ' (batchLockInv γA (metaTM d.γB d.P)) #f) ∗
    -- the consistent index and the apply protocol
    "%Hci" ∷ ⌜bk.ci' = ciIface cil ∧ γA.m0 = (W64 0, W64 0)⌝ ∗
    "#HisCI" ∷ isCI cil γA.ci ∗ "#Hcons" ∷ inv applyN (consInv γA) ∗
    "Hthr" ∷ applyThread γA ⟨W64 0, W64 0, W64 0, false⟩ ∗
    "Happ" ∷ ciApplying cil (W64 0) (W64 0) ∗ "Hown" ∷ ciOwner cil bk.be' ∗
    "#Hmeta" ∷ isMetaBackend bk.be' (⊤ \ ↑applyN) (readView γA) ∗
    -- the backend of the real instance, with the server's hooks
    "%Hbe" ∷ ⌜bk.be' = interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be ∧
      mvcc.bridgeParams d.P ∧ ciKeys d.P ∧ storage.hooksParams d.P⌝ ∗
    -- (the integration with `construct`, 2026-10-17) what `backend.New` gives (item 6's
    -- `newPost`, at the server's batch-lock resources: its hooks the server's, so its
    -- `isBackend` names the apply protocol's batch lock), over bbolt's data `D` with an empty
    -- key bucket (a new cluster's), the budget within its `wbInit` write-backs (`N` for the
    -- entries, seven for the construction); and what `bootstrap` adds: the store's registration
    -- right, `keySized`, the fresh buckets' tokens (`bootBackend_of_newPost` turns `newPost` into
    -- the resources `NewServer` uses)
    "Hnew" ∷ backend.newPost d.γB d.P (fun _ => mvcc.lateW d.gx)
      (fun γB => batchLockInv γA (metaTM γB d.P)) d.be D ∗
    "%HD" ∷ ⌜mvcc.keyView (backend.vData d.P (D, ⟨∅, W64 0⟩)) ∅⌝ ∗
    "%HN" ∷ ⌜N + 7 ≤ backend.wbInit⌝ ∗
    "#Hsz" ∷ mvcc.keySized d.γB d.P d.be ∗ "Hlate" ∷ mvcc.lateReg d.gx ∗
    "Hfl" ∷ bkFresh d.γB go!"lease" ∗ "Hfa" ∷ bkFresh d.γB go!"auth" ∗
    "Hfal" ∷ bkFresh d.γB go!"alarm" ∗
    -- the error paths' close
    "#Hclose" ∷ □ ({{ True }}
      (App (Val (b @!! go.GoType.PointerType bootstrappedServer.ty @!! go!"Close")) (Val #()))
      {{ RET #(); True }}))

/-- **The configuration's URLs, as `bootstrap` reads them** (D19r (F), 2026-10-18): the peer and
client URL slices and the initial cluster's map (member name to its peer URLs' slice), with their
contents. -/
structure BootURLs [FfiSyntax] where
  peer : List _root_.Perennial.net.url.URL
  client : List _root_.Perennial.net.url.URL
  initMap : GMap GoString GoSlice
  initURLs : GoString → List _root_.Perennial.net.url.URL

/-- **The configuration's URLs, read-only** (persistent; D19r (F)): what `bootstrap` reads of the
configuration beyond its scalar fields (`VerifyBootstrap`, `NewClusterFromURLsMap`, the member's
id from its peer URLs and the cluster token). -/
def bootCfgRO (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) : IProp GF :=
  iprop(cfg.PeerURLs' ↦*□ U.peer ∗ cfg.ClientURLs' ↦*□ U.client ∗
    cfg.InitialPeerURLsMap' ↦$□ U.initMap ∗ [∗map] k ↦ sl ∈ U.initMap, sl ↦*□ U.initURLs k)

instance bootCfgRO_persistent (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (U : BootURLs) : Persistent (bootCfgRO (GF := GF) cfg U) := by
  unfold bootCfgRO; infer_instance

/-- **`bootstrap`'s contract** (D13b: a premise of `NewServer.spec`, see the file header): on the
configuration `cfg` with its URLs `U` read-only (D19r (F): the member id `id` and the bootstrap
log are what Go computes from them) and the storage registry's authority, empty (D19r (B): the
new `MemoryStorage` joins it; until then the contract gave its registration with no authority,
which no update can), an error, or the record with `bootOk` (at the write-back budget
`N + 7`). -/
def bootstrapContract (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
    (γ : RaftNames) (id : w64) (bootLog : List EntryM) (N : Nat) (dir : w64 → List GoString) :
    IProp GF :=
  iprop(□ ({{ bootCfgRO cfg U ∗ memStorRegAuth (∅ : GMap Loc MemStorNamesRec) }}
      (App (Val (@! bootstrap)) (Val #cfg))
    {{ (b : Loc) (err : GoInterface), RET (PairV #b #err);
        ⌜err ≠ GoInterface.nil⌝ ∨ ⌜err = GoInterface.nil⌝ ∗ bootOk cfg γ id bootLog N dir b }}))

instance bootstrapContract_persistent (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (U : BootURLs) (γ : RaftNames) (id : w64) (bootLog : List EntryM) (N : Nat)
    (dir : w64 → List GoString) :
    Persistent (bootstrapContract (GF := GF) cfg U γ id bootLog N dir) := by
  unfold bootstrapContract; infer_instance

end defs

section snap
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [MemStorReg GF]

/-- **`run`'s snapshot contract from the application's token** (D17d, 2026-10-18; until then the
construction's residual `srvBuildGap`): the wrapper's `raftStorage` field holds the storage `ms`,
and `ms.Snapshot()` -- the application's triple of `MemoryStorage.Snapshot.spec`, with the token of
the fresh storage -- returns the empty snapshot (index and term `0`), whole (`ownSnapW`: metadata
and conf state set), frozen. -/
theorem rnSnapOnce_of_tok (wp_Snapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
    (E : RNEnv GF) (γ : RNNames) (r ms0 : Loc) (γs : MemStorNames) (Hms0 : γ.ms = ms0) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver -∗
      isRaftNode E γ r -∗ memSnapTok ms0 γs memStorEmpty -∗
      ∃ ms : Loc, rnRaftStorageAddr r ↦□ ms ∗ rnSnapOnce ms γs (W64 0) (W64 0) := by
  subst Hms0
  iintro #Hpkg #Hrn Htok
  ihave #Hrn' := Hrn
  iunfold isRaftNode at Hrn'
  iNamed Hrn'
  subst Hmsγ
  iexists γ.ms
  iframe Hms
  iunfold rnSnapOnce
  iintro %Φ HΦ
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  iapply wp_fupd
  wp_apply wp_Snapshot.2 γ.ms γs memStorEmpty $$ [$Htok] as %snap ⟨Htok, %sv, Hw, %Hid⟩
  imod ownSnapW_persist $$ Hw with ⟨%pm, %pc, %Hnn, #Hsn, #Hpm, #Hpc, #Hcs⟩
  imodintro
  obtain ⟨Hid, -, -⟩ := Hid
  simp only [snapId, memStorEmpty, entryID.mk.injEq] at Hid
  iapply HΦ $$ %snap %pm %pc %sv [] Hsn Hpm Hpc [] [Htok]
  · ipureintro
    exact ⟨Hid.2, Hid.1, Hnn.1, Hnn.2⟩
  · iapply epCsOk_of_csOptA $$ Hcs
  · iexists memStorEmpty
    iframe Htok
    ipureintro; simp [memStorEmpty]

end snap

section transport
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The `*rafthttp.Transport` `t` as an interface. -/
abbrev transportIface (t : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType
    go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty) #t

/-- **The transport `t` live, in the network `γn`** (opaque, exclusive; unit N4, 2026-10-17;
the network since D21 M2, 2026-10-19): started and not stopped. `Start` gives it; `AddRemote`/
`AddPeer` take it and give it back (`AddPeer` panics after `Stop`); it is given up for
`transportStarted` (whose `Stop` there is). -/
opaque transportLive (γn : NetNames GF) (t : Loc) : IProp GF

/-- **The transport `t` after `Start`, in the network `γn`** (persistent; names-only, see the file
header): `Send` puts each message, with its bundle, into the network (D21 M2, 2026-10-19; until
then it took the messages of any environment and promised nothing of them); `Stop` returns;
`ActiveSince` (`rafthttp.isTransporter`). -/
def transportStarted (γn : NetNames GF) (t : Loc) : IProp GF :=
  iprop(netTransport γn (transportIface t) ∗ rafthttp.isTransporter (transportIface t))

instance transportStarted_persistent (γn : NetNames GF) (t : Loc) :
    Persistent (transportStarted (GF := GF) γn t) := by
  unfold transportStarted; infer_instance

/-- **The raft wrapper's transport from the network's** (D21 M2): an environment whose messages
carry their bundle (`E.M m` gives `netBundle`) can send them through it. -/
theorem isRNTransport_of_net (γn : NetNames GF) (E : RNEnv GF) (tr : GoInterface) :
    ⊢ □ (∀ m : Loc, E.M m -∗ netBundle γn.N m) -∗ netTransport γn tr -∗ isRNTransport E tr := by
  iintro #HM #Htr
  iunfold netTransport at Htr
  icases Htr with ⟨%ti, %Hti, #Hsend, #Hstop⟩
  iunfold isRNTransport
  iexists ti
  isplitr
  · ipureintro; exact Hti
  isplitr
  · imodintro
    iintro %sl %msL %Φ !> ⟨Hsl, Hms⟩ HΦ
    wp_apply Hsend $$ [Hsl Hms]
    · iframe Hsl
      iapply BigSepL.bigSepL_impl $$ Hms
      imodintro
      iintro %k %m %_ Hm
      iunfold rnMsgOk at Hm
      icases Hm with ⟨%to, %ty, -, HEM⟩
      iapply HM $$ HEM
    iapply HΦ
    itrivial
  · iexact Hstop

/-- **The lessor's `SetCheckpointer`** (names-only, a contract of `lease.NewLessor`): it returns, the
checkpointer an opaque value (the lessor calls it later, outside the model: `NewServer`'s
closure over `raftRequest`). -/
def lessorCkptOk (l : GoInterface) : IProp GF :=
  iprop(∃ li : GoInterfaceOk, ⌜l = GoInterface.ok li⌝ ∗
    □ (∀ cp : GoFunc,
      {{ True }} (App (Val #(methods li.ty go!"SetCheckpointer" li.v)) (Val #cp)) {{ RET #(); True }}))

instance lessorCkptOk_persistent (l : GoInterface) : Persistent (lessorCkptOk (GF := GF) l) := by
  unfold lessorCkptOk; infer_instance

/-- **The compactor's `Run`** (names-only, a contract of `v3compactor.New`): it returns (it starts
the compactor's goroutine). -/
def compactorRunOk (c : GoInterface) : IProp GF :=
  iprop(∃ ci : GoInterfaceOk, ⌜c = GoInterface.ok ci⌝ ∗
    □ ({{ True }} (App (Val #(methods ci.ty go!"Run" ci.v)) (Val #())) {{ RET #(); True }}))

instance compactorRunOk_persistent (c : GoInterface) : Persistent (compactorRunOk (GF := GF) c) := by
  unfold compactorRunOk; infer_instance

end transport

end EtcdGrove
end Perennial
