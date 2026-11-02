/-
**A member's stop and restart: the server's vocabulary, drafted** (the restart plan's R2a,
2026-11-02, `notes/restart-plan.md`). Lean-first (no Rocq counterpart).

R2a states what the example (`examples/restart3`) needs of the server at a stop and a restart, over
the predicates named here. Their content is the later sub-steps': each is an `opaque` placeholder
until then, so that no statement over them can be proved by unfolding them.

* `srvStopRight s γ id` (exclusive): the right to stop the server `s` of member `id` of the cluster
  `γ` once started (`HardStop`). R2b (the stopping server, the membership plan's M6): what
  `NewServer` gives its caller, with the "server open" token the request paths share.
* `srvDiskImage γ ρ id` (exclusive): member `id`'s data directory, as its last incarnation's stop
  left it, that incarnation's request names `ρ` recorded: raft's hard state, log and last snapshot
  record (the WAL), the backend's buckets at its consistent index, the member and cluster ids. R2c
  (L2): the ghost image handed from one incarnation to the next; graceful stops only (the plan's
  Q4). It holds what the restarted member's `NewServer` takes of the ghost state in place of a
  first start's `memberBoot` (`examples/common/Defs.lean`): the node API's restart token in place
  of `nodeBoot` (R2e, raft's restart from a durable state), the cluster's invariants at the
  recorded names. (R2c, 2026-11-02: no id state. A restart makes its incarnation's id share anew,
  at a fresh incarnation key, `idutil/Incarnations.lean`'s `idIncarnation_alloc`, with its new
  store's floor `srvFloorFact E₀'` as the key's claim facts; the ids' freshness across incarnations
  is the trusted `Next`'s assumption, `issues/etcd-request-id-restart-reuse.md`.) R2c and R2d split it between the image and
  `NewServer`'s restart premise. (2026-11-02, `Run`'s glue: until then a separate `srvRestartBoot`
  bundle the example supplied; the restarted member's own names, its wait registry and its store's
  index, are new, so the server allocates them, not the example.)
* `restartNames ρ ρ'` (pure, defined): the restarted incarnation's names `ρ'` agree with the stopped
  one's `ρ` on what the rest of the cluster and its clients see: raft's names, the KV state's ghost
  variable (`etcdKV`, the clients' invariants), the KV model of the committed log, the cluster's
  map of issued request ids and the member's id prefix. Its other names are its own. (Once the
  id state is keyed by incarnation, R2c, the agreement is on the cluster's id maps and the prefix,
  and the key is the one `idIncarnation_alloc` gives.)
* `bootstrapRestartContract cfg U γ id ctxs N dir`: `bootstrap`'s contract on a data directory that
  holds member `id`'s image (`bootstrapContract`'s restart case, L3): with the image, an error or
  the record of a restart (`bootOk`'s restart case). R2c.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvStart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvImage
public import Spec.go_etcd_io.raft.v3.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The right to stop the started server `s`** (DRAFT, R2b; see the file header). -/
opaque srvStopRight (s : Loc) (γ : SrvRaft) (id : w64) : IProp GF

/-- **The files of a stopped member's data directory hold `σ` and `D`** (opaque, exclusive; a
trust-boundary token, DRAFT R2c): the WAL in `<dd>/member/wal` reads back (`ReadAll` from its last
snapshot record) as the records `σ` -- the snapshot record at `σ.b`, the hard state `σ.hs`, the
entries `σ.ents` -- and the bbolt file at `<dd>/member/snap/db` holds `D`. Made by the stop's
closes (R2b: `wal.Close`, `backend.Close`, axioms at the trust boundary, from what the server's
`Save`s and the backend's commits wrote), consumed by `bootstrap`'s restart contract. A graceful
stop in the same process: every write is visible to the next open, synced or not (the plan's
Q4). -/
opaque srvFiles (dd : GoString) (σ : StorContents) (D : backend.Data) : IProp GF

/-- **`buildConfStateFromV3store`** (opaque, DRAFT R2c, R2d's to define): the conf state etcd
builds from the backend's members (voters the non-learners, learners the learners, by id). -/
opaque v3ConfState (mem : GMap w64 apply.MemberM) : ConfStateM := memSnapEmpty.Metadata'.ConfState'

/-- **Member `id`'s data directory as its last stop left it, at that incarnation's request names
`ρ`** (DRAFT, R2c; see the file header and `notes/restart-plan.md`, "R2c: the image's content"):
- raft's part (the WAL): the id vacant (`node.Stop`'s `nodeVacant`), the node's durable state
  `S` (`raftState`, which the stopped raft loop held), and the WAL's records `σ` holding it
  (`StorageHolds`, what `RestartNode`'s update checks);
- the backend's part (the bbolt file): `D` is the image of a committed prefix `A` of the server's
  log through the consistent index `i` (`imageAt`, the snapshot path's certificate, `dbImage`'s
  content at the stopped incarnation's names), its stored term `t` (`metaIs`);
- between them: the WAL's snapshot at or below the backend's index, the backend's index at or
  below the WAL's commit (etcd's order: a snapshot is of the applied state, an entry is applied
  after the `Save` of its commit), so that `bootstrap` keeps the file (`recoverSnapshot` opens a
  `.snap.db` only when the file's index is below the snapshot's);
- the configuration point raft restarts with: `bootstrap` replaces the WAL snapshot's `ConfState`
  by the backend's (`buildConfStateFromV3store`), so the membership at `i`, the backend's members
  at `A`; `RestartNode` takes any point from the storage's base to its commit;
- the files holding `σ` and `D` (`srvFiles`) and the backend file's directory entry (`pathOwn`,
  which a first start's `bootOk` gives and the stop returns). -/
def srvDiskImage (γ : SrvRaft) (ρ : ReqNames) (id : w64) : IProp GF :=
  iprop(∃ (S : RaftState) (σ : StorContents) (i t : w64) (A : List EntryModel)
      (D : backend.Data) (m : Membership) (dd : GoString),
    nodeVacant γ.cl id ∗ raftState γ.cl id S ∗ ⌜StorageHolds S σ⌝ ∗
    ⌜ρ.rd.raft.raft = γ⌝ ∗ srvRLogLb ρ.rd.raft A ∗
    ⌜uint.Z i = uint.Z ρ.rd.raft.ai0 + A.length ∧
      imageAt ρ.rd.kv γ.boot i (ρ.rd.raft.pre ++ A) A D ∧ metaIs D (i, t)⌝ ∗
    ⌜σ.b ≤ uint.nat i ∧ uint.nat i ≤ σ.commit⌝ ∗
    confAt γ.cl (uint.nat i) m ∗
    ⌜confStateIs (v3ConfState (restModel (W64 0) γ.boot (ρ.rd.raft.pre ++ A)).mem) m⌝ ∗
    srvFiles dd σ D ∗ backend.pathOwn (config.backendPathOf dd))

end defs

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [MemStorReg GF]

/-- **The `MemoryStorage` `bootstrappedWAL.MemoryStorage` rebuilds** (opaque, DRAFT R2c, R2d's to
define): `NewMemoryStorage`, then `ApplySnapshot` of the WAL's snapshot record at `σ.b` with the
conf state `cs`, `SetHardState(σ.hs)`, `Append(σ.ents)`. R2d defines it in raft's storage
vocabulary (`memLog`, `memEnd`, `memStorMeta`, `memStorFresh` at the snapshot) and proves from it
`RestartNode`'s `restartStorage`, as kvdurable's `kd_restartStorage`. -/
opaque memStorRestarted (ms : Loc) (γs : MemStorNames) (σ : StorContents) (cs : ConfStateM) :
    IProp GF

/-- **The bootstrapped record of a restart** (DRAFT, R2c; `bootOk`'s restart case, L3): `bootOk`
with the changes marked `[R2c]`: no peers (so `RestartNode`), the storage rebuilt from the WAL's
records `σ` (`memStorRestarted`), the cluster's members recovered from the image's buckets at its
committed log `L`, the consistent index loaded at the image's `i` (`γA.m0`, `ciApplying`), the
backend file's data the image `D` (no fresh file's facts: `HD`, `HDr`, `HmEmpty` gone). Kept as a
first start's: the remotes (`Hrms0`: `bootstrapClusterWithWAL` sets none either), the directory's
members (a static cluster, the plan's scope). -/
def bootOkR (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (γ : SrvRaft) (id : w64)
    (N : Nat) (dir : w64 → List GoString) (σ : StorContents) (i : w64) (L : List EntryModel)
    (D : backend.Data) (b : Loc) : IProp GF :=
  iprop(∃ (bs : bootstrappedServer) (sto : bootstrappedStorage) (bk : bootstrappedBackend)
      (bw : bootstrappedWAL) (bc : bootstrappedCluster) (bv : bootstrappedRaft) (cv : Config)
      (lok : GoInterfaceOk) (γs : MemStorNames) (pv : List Peer) (ps : List w64)
      (rms : List Loc) (cid : w64) (cil : Loc) (γA : ApplyNames)
      (d : mvcc.KBReal),
    -- the records
    "Hb" ∷ b ↦ bs ∗ "Hsto" ∷ bs.storage' ↦ sto ∗ "Hbk" ∷ sto.backend' ↦ bk ∗
    "Hbw" ∷ sto.wal' ↦ bw ∗ "Hbc" ∷ bs.cluster' ↦ bc ∗ "Hbv" ∷ bs.raft' ↦ bv ∗
    -- (the keep-alive stage's K7, 2026-11-01, the user's decision) the peers' round tripper a
    -- `*http.Transport` (`bootstrap`'s `prt`, from `rafthttp.NewRoundTripper`, `bootstrap.go:72`:
    -- `transport.NewTimeoutTransport`'s), which `NewServer` stores in `peerRt` and `LeaseRenew`
    -- forwards a follower's renewal through (`srvPeerRt`)
    "%Hprt" ∷ ⌜∃ t : Loc, bs.prt' =
      GoInterface.ok ⟨go.GoType.PointerType _root_.Perennial.net.http.Transport.ty, #t⟩⌝ ∗
    -- (2026-10-31, `notes/axiom-review/savesnap.md`) the WAL read (`bootstrapWAL`'s `ReadAll`),
    -- which `NewStorage`'s contract takes
    "%HwalR" ∷ ⌜storage.walReady bw.w'⌝ ∗
    -- (2026-10-31, the user's decision) and its open token, whole: the WAL `bootstrap` opened is the
    -- server's (`storage.walOpen`; the raft loop's `Save`s and `Close`, the apply thread's `SaveSnap`)
    "Hwalo" ∷ storage.walOpen bw.w' 1 ∗
    -- (D22 S-i, 2026-10-19) the snapshotter (`bootstrapSnapshot`'s `snap.New(lg, cfg.SnapDir())`,
    -- its fields set once), which the transport's snapshot handler and `applySnapshot` use
    "#Hss" ∷ snap.isSnapshotter bs.ss' ∗
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
      -- [R2c] no peers: `bootstrapRaftFromWAL` sets none, so `newRaftNode` calls `RestartNode`
      -- (`len(b.peers) == 0`); `ps` is the cluster's members (`Hdirps`, `Hmembers`), not peers
      pv = [] ∧ ps ≠ [] ∧ ps.Nodup ∧ W64 0 ∉ ps ∧ (ps.length : Int) < 2 ^ 62 ∧
      cv.ID' ∈ ps ∧ γ.vs = ps ∧ srvBootLogOk ps γ.boot⌝ ∗
    "Hc" ∷ bv.config' ↦ cv ∗ "#Hlok" ∷ isLogger lok ∗
    "#Hreg" ∷ memStorReg bv.storage' γs ∗
    -- (D19r (B), 2026-10-18) the registry's authority, given empty, back with the new storage
    "Hrauth" ∷ memStorRegAuth (GMap.insert bv.storage' γs.tuple (∅ : GMap Loc MemStorNamesRec)) ∗
    -- (2026-10-30, the repair: raft's two-writer `MemoryStorage` specs) the fresh storage as
    -- `NewMemoryStorage` leaves it: its lock, dummy entry and end, the "no snapshot taken yet"
    -- token (which `run`'s `Snapshot()` reads), its hard state and fresh state (which
    -- `StartNode`'s `bootStorage` takes, `srvMem_bootStorage`). Until then the storage's
    -- `isStorage`/`ownStorage`, the trusted `InitialState` closure, the snapshot token, the
    -- certificate registry's authority and the cap `1`.
    "#Hmlock" ∷ memStorLock bv.storage' γs ∗
    -- [R2c] the storage `bootstrappedWAL.MemoryStorage` rebuilds from the WAL's records `σ`
    -- (`ApplySnapshot` of the WAL snapshot with the backend's `ConfState`, `SetHardState`,
    -- `Append`), in place of the fresh storage's tokens; R2d derives `RestartNode`'s
    -- `restartStorage` from it, as kvdurable's `kd_restartStorage`
    "Hrest" ∷ memStorRestarted bv.storage' γs σ (v3ConfState (restModel (W64 0) γ.boot L).mem) ∗
    "Hpeers" ∷ bv.peers' ↦* pv ∗
    -- the cluster
    "#Hcl" ∷ rnClusterOk bc.cl' ∗ "#Hrc" ∷ membership.isRaftCluster bc.cl' ∗
    "#Hcid" ∷ membership.clusterCid bc.cl' cid ∗ "%Hid" ∷ ⌜bc.nodeID' = id⌝ ∗
    -- (D43 M5e, 2026-10-26, the user's decision) its logger, read-only, not nil
    -- (`NewClusterFromURLsMap` sets `lg` from the configuration's logger): what `AddMember` and
    -- `RemoveMember` log through, `applyConfChange`'s
    "#Hclg" ∷ (∃ lgc : Loc, membership.rcLgAddr bc.cl' ↦□ lgc ∗ ⌜lgc ≠ null⌝) ∗
    -- (audit B4a, 2026-10-18) its `versionChanged` field, owned (the cluster not yet shared):
    -- `NewServer`'s `SetVersionChangedNotifier` writes it without the lock, and the cluster's
    -- apply contract `Hisc` (whose `SetVersion` reads it) is for after, the field read-only
    "Hvcn" ∷ (∃ v : Loc, membership.rcVersionChangedAddr bc.cl' ↦ v) ∗
    "#Hrms" ∷ bc.remotes' ↦*□ rms ∗ "#Hrmsi" ∷ ([∗list] m ∈ rms, memberRO dir m) ∗
    -- (the partition plan's S1, 2026-10-20) no remotes: the contract describes a new cluster's
    -- bootstrap (`Hnosnap`: raft started by `StartNode` with the members as peers, which
    -- `bootstrapRaft` does only for `!haveWAL && cfg.NewCluster`, where `bootstrapCluster` is
    -- `bootstrapNewClusterNoWAL`, whose `remotes` is nil; `remotes` is set only for a member
    -- joining an existing cluster). So `NewServer` calls `AddRemote` never, and the member's
    -- transport has no remote (`transportRemotes t []`, `srvNetMember`), which `CutPeer` needs.
    "%Hrms0" ∷ ⌜rms = []⌝ ∗
    -- (2026-10-24, rafthttp stage 6d; D21b's deployment fact) the directory's members are raft's
    -- peers (a member's transport adds every other as a peer, so its handler finds the sender of
    -- any request), at most `2 ^ 20` of them (each peer's goroutines borrow eight of `lgMu`'s
    -- reader slots)
    "%Hdirps" ∷ ⌜(∀ f, dir f ≠ [] ↔ f ∈ ps) ∧ ps.length ≤ 2 ^ 20⌝ ∗
    -- (D21 M2, 2026-10-19) the members' records name each member's own URLs (`dir`, D21b's
    -- deployment fact): `Members()` returns members whose peer URLs are the directory's;
    -- (2026-10-24, rafthttp stage 6d) raft's peers, in order (both sorted by id: `Members()`'s
    -- `MembersByID`, `bootstrapRaftFromCluster`'s peers from `MemberIDs()`)
    "#Hmembers" ∷ □ (∀ Φ : val → IProp GF,
      (∀ (sl : GoSlice) (ms : List (Loc × w64)), ⌜ms.map Prod.snd = ps⌝ -∗
        sl ↦* ms.map Prod.fst -∗ ([∗list] p ∈ ms, memberDirIs dir p.1 p.2) -∗ Φ #sl) -∗
      WP (App (Val (bc.cl' @!! go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"Members"))
        (Val #())) {{ Φ }}) ∗
    -- the cluster's contracts (unit N4, 2026-10-17): the lessor's (`Version()`), and the apply
    -- package's at the backend's batch lock and any frozen hook (its writes: one write-back
    -- each, `membershipBackend`'s `LockInsideApply`/`Unlock`, as the stores', D14f); (D22,
    -- 2026-10-23: the backend over every bucket) its writes' effect on the tracked buckets and
    -- its in-memory members (`srvRestOwn`), `SetDowngradeInfo` with the write right
    -- (`srvRestRW`)
    "#Hclok" ∷ lease.clusterOk (interface.mkOk (go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty) #bc.cl') ∗
    -- (srvBuildGap's rows, 2026-10-17) its `Version()` monotone, for `start`'s
    -- `clusterVersionOk`
    "#Hcvm" ∷ (∃ γcv : GName, clusterVersionMono bc.cl' γcv) ∗
    -- (D22 receiver epochs, S7e, 2026-10-23) on whichever backend its `be` field names, which
    -- `bootstrap` set to the boot backend and gives owned (`clusterBeOn`: no lock guards it, the
    -- apply thread is its only user); until then for the boot backend's batch lock only
    "#Hisc" ∷ clusterApplyOk bc.cl' ∗
    "HclBe" ∷ clusterBeOn bc.cl' d.be ∗
    -- [R2c] the cluster's in-memory members, recovered from the backend's buckets (`Finalize`'s `cl.Recover`), the image's
    -- members at its committed log `L` (`bkRestAt`), in place of the boot log's
    "Hmem" ∷ membership.clusterMem bc.cl' (restModel (W64 0) γ.boot L).mem ∗
    -- the consistent index and the apply protocol
    "%Hci" ∷ ⌜bk.ci' = ciIface cil⌝ ∗
    "#HisCI" ∷ isCI cil γA.ci ∗ "#Hcons" ∷ inv applyN (consInv γA) ∗
    -- (D43 M5e, 2026-10-26, the user's decision) the backend's hooks, as `NewBackendHooks(cfg.Logger,
    -- ci)` makes them (`bootstrapBackend`, `bootstrap.go:258`): the server's `s.beHooks`, whose
    -- `SetConfState` `applyConfChange` calls
    "#Hbh" ∷ (∃ lgh : Loc, storage.isBackendHooks bk.beHooks'
      ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty, #cil⟩
      lgh) ∗
    -- (2026-11-01: `consInv_alloc`'s state, processed through the stored index `γA.m0.1`; until
    -- then `⟨0, 0, 0, false⟩`, a hidden copy of the literal)
    "Hthr" ∷ applyThread γA ⟨W64 0, γA.m0.1, W64 0, false⟩ ∗
    -- [R2c] the index loaded from the image (`metaIs D γA.m0`, `γA.m0.1 = i`)
    "Happ" ∷ ciApplying cil γA.m0.1 γA.m0.2 ∗ "Hown" ∷ ciOwner cil bk.be' ∗
    -- the boot backend's meta reads: `#HmetaSnap`'s output at the boot open (`boot_create`,
    -- `SnapApplyOpen.lean`: from the fresh keys and payment rights inside `OpenBackend`'s `openPre`,
    -- with `Hm0`), which `bootstrap`, names-only, does not let `NewServer` derive
    "#Hmeta" ∷ isMetaBackend bk.be' (⊤ \ ↑applyN) (readView γA) ∗
    -- (J8a-4, 2026-11-01, the user's decision: `notes/decisions.md`, "J8a-4") the meta reads of a
    -- backend the apply thread opens (`applySnapshot`'s `OpenSnapshotBackend`) at the protocol's
    -- names `π`, over an image whose meta keys are `π.m0`, at its fresh keys and payment rights
    -- (they come back): what `applySnapshot.specSnap` takes
    "#HmetaSnap" ∷ □ (∀ (π : ApplyPhys) (γB : backend.BNames) (P : backend.BParams) (D : backend.Data),
        ⌜ciKeys P ∧ metaIs D π.m0 ∧ π.bwb = γB.wb ∧ π.bopn = γB.opn⌝ -∗
        backend.hkOwn γB (backend.hkData P D) -∗ backend.bFresh γB -∗
        backend.hkOwn γB (backend.hkData P D) ∗ backend.bFresh γB ∗
        □ ∀ (W : IProp GF) (b : Loc),
          backend.isBackend γB P W (batchLockInv (γA.withPh π) (metaTM γB P)) b -∗
          isMetaBackend (interface.mkOk (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #b) (⊤ \ ↑applyN)
            (readView (γA.withPh π))) ∗
    -- (D22 J1a, 2026-10-26) the backend's hooks over the consistent index (`bootstrapBackend`'s
    -- `serverstorage.NewBackendHooks(cfg.Logger, ci)`), which the snapshot path's
    -- `OpenSnapshotBackend` installs on each new backend
    "#Hbh" ∷ (∃ lgh : Loc, storage.isBackendHooks bk.beHooks'
      ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty, #cil⟩
      lgh) ∗
    -- the backend of the real instance, with the server's hooks (2026-11-01, J8a-1, approved: and
    -- its parameters `newBackend` configures, well-formed with the batch limit `openLimit cfg`, as
    -- `OpenSnapshotBackend`'s `openPre` requires of a snapshot's backend)
    "%Hbe" ∷ ⌜bk.be' = interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be ∧
      mvcc.bridgeParams d.P ∧ ciKeys d.P ∧ storage.hooksParams d.P ∧
      d.P.Wf ∧ d.P.limit = storage.openLimit cfg ∧
      -- (the lease-revoke plan, 2026-10-31) the `Lease` bucket in the table, tracked, no hook
      -- keys: what a revocation's deletions from it take (`mvcc.storeRb`)
      mvcc.leaseParams d.P ∧
      -- (2026-11-02, the backend-auth-split stage, item E of the approved restatements) the alarm
      -- and auth buckets in the table (schema's `Alarm`, `Auth`, `AuthUsers`, `AuthRoles`, of
      -- `MustCreateBackendBuckets`' `AllBuckets`): what `NewAlarmStore` and `NewAuthStore` take of
      -- the buckets they create, so that they are among the backend's ghost names
      d.P.has mvcc.alarmBI ∧ d.P.has mvcc.authBI ∧ d.P.has mvcc.authUsersBI ∧
      d.P.has mvcc.authRolesBI⌝ ∗
    -- (2026-11-02, the user's approval, branch `snap-window`) the backend's hooks are the server's
    -- `s.beHooks` (`bootstrapBackend`'s `OpenBackend(cfg, beHooks)`: `bcfg.Hooks = hooks`, which
    -- `New` stores in `b.hooks`): what the merged snapshot's window needs of its commit
    "#HhkAt" ∷ backend.hooksAt d.be (storage.hooksIface bk.beHooks') ∗

    -- (the integration with `construct`, 2026-10-17) what `backend.New` gives (item 6's
    -- `newPost`, at the server's batch-lock resources: its hooks the server's, so its
    -- `isBackend` names the apply protocol's batch lock), over bbolt's data `D` with an empty
    -- key bucket (a new cluster's), the budget within its `wbInit` write-backs (`N` for the
    -- entries, seven for the construction); and what `bootstrap` adds: the store's registration
    -- right, `keySized` (`bootBackend_of_newPost` turns `newPost` into the resources `NewServer`
    -- uses)
    "Hnew" ∷ backend.newPost d.γB d.P (fun _ => mvcc.lateW d.gx)
      (fun γB => batchLockInv γA (metaTM γB d.P)) d.be D ∗
    -- [R2c] the file is the image (`srvDiskImage`), at the consistent index `i`
    -- (2026-11-01, the user's decision, "bootOk's boot metadata") the boot data's meta keys are the
    -- protocol's initial ones: the consistent index and term stored in `D`'s `Meta` bucket are
    -- `γA.m0` (what `#Hmeta`'s reads return and `batchLockInv γA`'s mirror starts at; a restart's
    -- `D` holds the last commit's)
    "%Hm0" ∷ ⌜metaIs D γA.m0 ∧ γA.m0.1 = i⌝ ∗
    "%HN" ∷ ⌜N + 7 ≤ backend.wbInit⌝ ∗
    -- (D22 J1a, 2026-10-26: of every backend at these parameters, for the snapshot path's backends;
    -- until then of `d` only) the Key bucket's size bound (no bbolt file holds `2 ^ 62` keys)
    "#Hsz" ∷ □ (∀ (γB : backend.BNames) (b : Loc), mvcc.keySized γB d.P b) ∗
    "Hlate" ∷ mvcc.lateReg d.gx ∗
    -- (D22 S-j2, 2026-10-20; an environment assumption the user approved, "D22's environment
    -- assumptions approved") the backend file's directory entry is the server's: nothing else
    -- creates, renames or deletes a file at `<DataDir>/member/snap/db`. `applySnapshot`'s
    -- `storage.OpenSnapshotBackend` renames a received image onto it (`os.Rename`'s axiom takes it)
    "Hpath" ∷ backend.pathOwn (config.backendPathOf cfg.DataDir') ∗
    -- the error paths' close
    "#Hclose" ∷ □ ({{ True }}
      (App (Val (b @!! go.GoType.PointerType bootstrappedServer.ty @!! go!"Close")) (Val #()))
      {{ RET #(); True }}))


/-- **`bootstrap`'s contract on a stopped member's data directory** (DRAFT, R2c; L3; a premise, as
`bootstrapContract`): with the configuration's URLs, the storage registry's authority, and the
directory's files holding the WAL's records `σ` and the backend's data `D` (`srvFiles`, its path's
entry `pathOwn`) of an image (`imageAt` at `L`, the index `i` between the WAL's snapshot and
commit), `bootstrap` returns an error, or the record of a restart (`bootOkR`). -/
def bootstrapRestartContract (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
    (γ : SrvRaft) (id : w64) (ctxs : List (List w8)) (N : Nat) (dir : w64 → List GoString) :
    IProp GF :=
  iprop(□ ∀ (σ : StorContents) (i : w64) (γk : KVNames) (L A : List EntryModel)
      (D : backend.Data),
    ⌜imageAt γk γ.boot i L A D ∧ σ.b ≤ uint.nat i ∧ uint.nat i ≤ σ.commit⌝ -∗
    {{ bootCfgRO cfg U ∗ memStorRegAuth (∅ : GMap Loc MemStorNamesRec) ∗
        srvFiles cfg.DataDir' σ D ∗ backend.pathOwn (config.backendPathOf cfg.DataDir') }}
      (App (Val (@! bootstrap)) (Val #cfg))
    {{ (b : Loc) (err : GoInterface), RET (PairV #b #err);
        ⌜err ≠ GoInterface.nil⌝ ∨ ⌜err = GoInterface.nil⌝ ∗ bootOkR cfg γ id N dir σ i L D b }})

end boot

/-- **A restarted incarnation's names agree with the stopped one's where the cluster sees them**
(see the file header). -/
def restartNames [GooseExts] (ρ ρ' : ReqNames) : Prop :=
  ρ'.rd.raft = ρ.rd.raft ∧ ρ'.rd.kv.st = ρ.rd.kv.st ∧ kvModel ρ'.rd.kv = kvModel ρ.rd.kv ∧
    ρ'.ids.issued = ρ.ids.issued ∧ ρ'.ids.pfx = ρ.ids.pfx

end EtcdGrove
end Perennial
