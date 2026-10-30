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
    `b.cluster`, `b.raft`) and (D22 S-i) the snapshotter `b.ss` (`snap.isSnapshotter`);
  - `b.raft` with `NodeStartSpec`'s premises on it (the raft config valid, `CheckQuorum`/
    `PreVote` either way, the fresh registered `MemoryStorage`, the peers and the bootstrap log, the
    `InitialState` closure, `Marshal` at the peers' conf changes) and the cluster's
    `IsIDRemoved` contract;
  - the cluster (`isRaftCluster`, its id, this node's id, the remote members, read-only; its
    `Version()` monotone, `clusterVersionMono`, D17);
  - the consistent index at `0` (`isCI`, `ciOwner` of the backend, the applying index at `0`)
    and the apply protocol's names and invariant (`consInv`, the apply thread's half at the start:
    the backend's batch lock's resource names them, so they exist before the backend; the
    protocol's allocation is `consInv_alloc`, `InvApply.lean`: since S7f its registry holds the boot
    backend's physical names, `batchLockInv`'s `applyRegd`), the backend's meta keys at
    `(0, 0)` (a new cluster's fresh backend);
  - the backend of the real instance `d` with the server's hooks (`server_kv_backend_hooks`'s
    premises but the post-lock hook's, which `NewServer` sets: the hook's half, its open fraction,
    the write budget);
  - `b.Close()` returns (the error paths' deferred close).
* **The transport** (rafthttp stage 6d, 2026-10-24): rafthttp's own predicates (`trLive`,
  `trFrozen`, `trTok`, `TransportState.lean`); the raft loop's key to its `Send` (`srvTrKey`,
  exchanged for a reader's token of the transport, `netTransport_of_key`); `isRNTransport` for
  every environment whose messages carry the bundle (`isRNTransport_of_net`). (From D21 M2 to
  stage 6d the opaque `transportLive`, `transportStarted` and `transportRemotes` of the
  names-only transport.)
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
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.TransportState
public import Perennial.Ghost.GhostMap
public import Proof.go_etcd_io.etcd.client.pkg.v3.types.URLs
public import Proof.go_etcd_io.etcd.server.v3.storage.InvOpen
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRest
public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [MemStorReg GF]

/-- **The network's directory, well formed** (rafthttp stage 6d, 2026-10-24; a premise of
`NewServer.spec`, of the caller's directory): no member `0` (raft's ids are not `0`; the directory
gives an unknown host the owner `0`, `netOwner`), each host of one member's URLs only
(`dirHostsDistinct`), every peer URL a plain `http://` URL (`types.plainPeerURL`: what the
transport's `AddPeer` parses). -/
def netDirOk (dir : w64 → List GoString) : Prop :=
  dir 0 = [] ∧ dirHostsDistinct dir ∧ ∀ (id : w64) (s : GoString), s ∈ dir id → types.plainPeerURL s

/-- **The member's configured peer URLs are its directory URLs** (2026-10-27, D22 J-T, W8; a
premise of `NewServer.spec`, of the caller's configuration): non-empty, each of only the scheme
`http` and a plain host (`http.urlRootPlain`), `http://` and the host one of the member's peer
URLs in the directory. The transport sends them in `X-PeerURLs` (`setPeerURLsHeader`), which a
peer's handler may add a remote for. -/
def peerURLsDir (dir : w64 → List GoString) (id : w64) (uvs : List _root_.Perennial.net.url.URL) :
    Prop :=
  uvs ≠ [] ∧ ∀ u ∈ uvs, http.urlRootPlain u ∧ go!"http://" ++ u.Host' ∈ dir id

/-- **A one-member directory** (rafthttp stage 6d; the one-member examples'): the member `id`'s one
peer URL `url`, no other member. -/
def dirOne (id : w64) (url : GoString) (i : w64) : List GoString := if i = id then [url] else []

/-- A one-member directory is well formed, of a member other than `0` with a plain URL. -/
theorem dirOne_ok (id : w64) (url : GoString) (hid : id ≠ W64 0) (hpl : types.plainPeerURL url) :
    netDirOk (dirOne id url) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold dirOne; rw [if_neg (fun e => hid (by rw [← e]; rfl))]
  · intro i j h hi hj
    unfold dirOne at hi hj
    split at hi <;> split at hj <;> simp_all
  · intro i s hs
    unfold dirOne at hs
    split at hs
    · simp at hs; subst hs; exact hpl
    · simp at hs

/-- A one-member directory's only member. -/
theorem dirOne_member (id : w64) (url : GoString) (f : w64) (hf : dirOne id url f ≠ []) : f = id := by
  unfold dirOne at hf
  by_cases h : f = id
  · exact h
  · simp [h] at hf

omit [MemStorReg GF] in
/-- **A member's URLs, as the transport's `AddPeer` takes them** (rafthttp stage 6d): of a
well-formed directory's member `pid` (one of raft's peers, the directory's members), non-empty,
plain, of hosts the directory gives `pid`. -/
theorem addPeer_dir (γn : NetNames GF) (dir : w64 → List GoString) (hγ : γn.dir = dir)
    (hd : netDirOk dir) (ps : List w64) (hps : ∀ f, dir f ≠ [] ↔ f ∈ ps) (pid : w64)
    (hp : pid ∈ ps) (ss : List GoString) (hss : ss = dir pid) :
    ss ≠ [] ∧ (∀ s ∈ ss, types.plainPeerURL s) ∧
      (∀ h, go!"http://" ++ h ∈ ss → (netRh γn).owner h = pid) ∧ (netRh γn).member pid := by
  subst hss hγ
  refine ⟨(hps pid).2 hp, fun s hs => hd.2.2 pid s hs, fun h hm => ?_,
    (netRh_member γn pid).2 ((hps pid).2 hp)⟩
  rw [netRh_owner]
  exact netOwner_of_mem γn.dir hd.2.1 pid h hm

omit [MemStorReg GF] in
/-- Four of `n` copies of `P` for each id of `l` (D22 J-T: the transport's pool). -/
theorem replicate_list4 (P : IProp GF) : ∀ (l : List w64) (n : Nat), 4 * l.length ≤ n →
    ([∗list] _x ∈ List.replicate n (), P) ⊢ [∗list] _x ∈ l, P ∗ P ∗ P ∗ P
  | [], _, _ => by
    iintro -
    iapply BigSepL.bigSepL_nil.2; itrivial
  | x :: l, n, h => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by simp only [List.length_cons] at h; omega⟩
    rw [show List.replicate (m + 4) () = () :: () :: () :: () :: List.replicate m () by
      simp [List.replicate_succ]]
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H2, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H3, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H4, H⟩
    iapply BigSepL.bigSepL_cons.2
    iframe H1 H2 H3 H4
    iapply replicate_list4 P l m (by simp only [List.length_cons] at h; omega) $$ H

omit [MemStorReg GF] in
/-- **The transport's configured peer URLs are its member's** (D22 J-T, W8): from the directory. -/
theorem trURLsOk_of_dir (γn : NetNames GF) (dir : w64 → List GoString) (hγ : γn.dir = dir)
    (hd : netDirOk dir) (ps : List w64) (hps : ∀ f, dir f ≠ [] ↔ f ∈ ps) (id : w64)
    (hid : id ∈ ps) (uvs : List _root_.Perennial.net.url.URL) (hu : peerURLsDir dir id uvs) :
    trURLsOk (netRh γn) id uvs := by
  obtain ⟨-, hpl, hown, -⟩ := addPeer_dir γn dir hγ hd ps hps id hid (dir id) rfl
  exact ⟨hu.1, fun u hu' => ⟨(hu.2 u hu').1, hpl _ (hu.2 u hu').2, hown _ (hu.2 u hu').2⟩⟩

omit [MemStorReg GF] in
/-- The members' loop's coverage, a step further: the ids added so far (`L`, within `L'`), and
the next member's if it is another. -/
theorem membersCov_step (mps : List (Loc × w64)) (id : w64) (L L' : List w64) (n : Nat)
    (px : Loc × w64) (hpx : mps[n]? = some px)
    (hcov : ∀ (k : Nat) (p : Loc × w64), k < n → mps[k]? = some p → p.2 ≠ id → p.2 ∈ L)
    (hL : ∀ x ∈ L, x ∈ L') (hx : px.2 ≠ id → px.2 ∈ L') :
    ∀ (k : Nat) (p : Loc × w64), k < n + 1 → mps[k]? = some p → p.2 ≠ id → p.2 ∈ L' := by
  intro k p hk hp hne
  by_cases hkn : k < n
  · exact hL _ (hcov k p hkn hp hne)
  · have : k = n := by omega
    subst this
    rw [hpx] at hp
    cases hp
    exact hx hne

omit [MemStorReg GF] in
/-- The members' loop done: every other member of the network (a directory member, so one of
raft's peers, `Members()`'s) is among the ids added. -/
theorem membersCov_done (γn : NetNames GF) (dir : w64 → List GoString) (hγ : γn.dir = dir)
    (ps : List w64) (hps : ∀ f, dir f ≠ [] ↔ f ∈ ps) (mps : List (Loc × w64))
    (hmps : mps.map Prod.snd = ps) (id : w64) (L : List w64) (n : Nat) (hn : mps.length ≤ n)
    (hcov : ∀ (k : Nat) (p : Loc × w64), k < n → mps[k]? = some p → p.2 ≠ id → p.2 ∈ L) :
    ∀ f, (netRh γn).member f → f ≠ id → f ∈ L := by
  intro f hf hne
  have hfp : f ∈ ps := (hps f).1 (by rw [← hγ]; exact (netRh_member γn f).1 hf)
  rw [← hmps] at hfp
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hfp
  obtain ⟨k, hk, hkp⟩ := List.getElem_of_mem hp
  exact hcov k p (by omega) (by rw [List.getElem?_eq_getElem hk, hkp]) hne

/-- `n` copies of `P` and `n` of `Q` are `n` of `P ∗ Q`. -/
theorem replicate_sep (P Q : IProp GF) (n : Nat) :
    ([∗list] _x ∈ List.replicate n (), P) ∗ ([∗list] _x ∈ List.replicate n (), Q) ⊢
      [∗list] _x ∈ List.replicate n (), iprop(P ∗ Q) :=
  BigSepL.bigSepL_sep_eqv.2

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

-- (D22 J1a, 2026-10-26) `memberDirIs` moved to `SnapRO.lean`.

/-- **A fresh alarm store** `a` (opaque, exclusive; D14i, 2026-10-17): made by
`v3alarm.NewAlarmStore` over a fresh alarm bucket and not yet handed to an applier, it has no
alarm (`Activate`, the only writer of its map, is in its apply contract, which taking this token
gives: the axiom's postcondition). -/
opaque alarmFresh (a : Loc) : IProp GF

-- (D22 J1a) the stores' apply contracts (`alarmApplyOk`, `authApplyOkM`, `authApplyOk`,
-- `lessorApplyOk`, `clusterApplyOk`) moved to `SnapRO.lean`.

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
def bootOk (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (γ : SrvRaft) (id : w64)
    (ctxs : List (List w8)) (N : Nat) (dir : w64 → List GoString) (b : Loc) : IProp GF :=
  iprop(∃ (bs : bootstrappedServer) (sto : bootstrappedStorage) (bk : bootstrappedBackend)
      (bw : bootstrappedWAL) (bc : bootstrappedCluster) (bv : bootstrappedRaft) (cv : Config)
      (lok : GoInterfaceOk) (γs : MemStorNames) (pv : List Peer) (ps : List w64)
      (rms : List Loc) (cid : w64) (cil : Loc) (γA : ApplyNames)
      (d : mvcc.KBReal) (D : backend.Data),
    -- the records
    "Hb" ∷ b ↦ bs ∗ "Hsto" ∷ bs.storage' ↦ sto ∗ "Hbk" ∷ sto.backend' ↦ bk ∗
    "Hbw" ∷ sto.wal' ↦ bw ∗ "Hbc" ∷ bs.cluster' ↦ bc ∗ "Hbv" ∷ bs.raft' ↦ bv ∗
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
      ps = pv.map Peer.ID' ∧ ps ≠ [] ∧ ps.Nodup ∧ W64 0 ∉ ps ∧ (ps.length : Int) < 2 ^ 62 ∧
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
    "#Hlog0" ∷ memLog γs 0 DFrac.discard [(zero_val EntryM : EntryM)] ∗ "Hend" ∷ memEnd γs 1 ∗
    "Hsnone" ∷ memSnapNone γs ∗
    "Hmeta" ∷ memStorMeta bv.storage' γs (HardStateM.mk (W64 0) (W64 0) (W64 0)) ∗
    "Hfresh" ∷ memStorFresh bv.storage' γs ∗
    "Hpeers" ∷ bv.peers' ↦* pv ∗ "#Hctx" ∷ peersCtx pv ctxs ∗
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
    -- (D22, 2026-10-23; option (i) of "D22c decided") the cluster's in-memory members, as
    -- `bootstrap` made them: the boot log's (`memBoot`, the members whose JSON the bootstrap
    -- entries' contexts are)
    "Hmem" ∷ membership.clusterMem bc.cl' (memBoot γ.boot) ∗
    -- the consistent index and the apply protocol
    "%Hci" ∷ ⌜bk.ci' = ciIface cil ∧ γA.m0 = (W64 0, W64 0)⌝ ∗
    "#HisCI" ∷ isCI cil γA.ci ∗ "#Hcons" ∷ inv applyN (consInv γA) ∗
    -- (D43 M5e, 2026-10-26, the user's decision) the backend's hooks, as `NewBackendHooks(cfg.Logger,
    -- ci)` makes them (`bootstrapBackend`, `bootstrap.go:258`): the server's `s.beHooks`, whose
    -- `SetConfState` `applyConfChange` calls
    "#Hbh" ∷ (∃ lgh : Loc, storage.isBackendHooks bk.beHooks'
      ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty, #cil⟩
      lgh) ∗
    "Hthr" ∷ applyThread γA ⟨W64 0, W64 0, W64 0, false⟩ ∗
    "Happ" ∷ ciApplying cil (W64 0) (W64 0) ∗ "Hown" ∷ ciOwner cil bk.be' ∗
    "#Hmeta" ∷ isMetaBackend bk.be' (⊤ \ ↑applyN) (readView γA) ∗
    -- (D22 J1a, 2026-10-26) the backend's hooks over the consistent index (`bootstrapBackend`'s
    -- `serverstorage.NewBackendHooks(cfg.Logger, ci)`), which the snapshot path's
    -- `OpenSnapshotBackend` installs on each new backend
    "#Hbh" ∷ (∃ lgh : Loc, storage.isBackendHooks bk.beHooks'
      ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty, #cil⟩
      lgh) ∗
    -- the backend of the real instance, with the server's hooks
    "%Hbe" ∷ ⌜bk.be' = interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be ∧
      mvcc.bridgeParams d.P ∧ ciKeys d.P ∧ storage.hooksParams d.P⌝ ∗
    -- (the integration with `construct`, 2026-10-17) what `backend.New` gives (item 6's
    -- `newPost`, at the server's batch-lock resources: its hooks the server's, so its
    -- `isBackend` names the apply protocol's batch lock), over bbolt's data `D` with an empty
    -- key bucket (a new cluster's), the budget within its `wbInit` write-backs (`N` for the
    -- entries, seven for the construction); and what `bootstrap` adds: the store's registration
    -- right, `keySized` (`bootBackend_of_newPost` turns `newPost` into the resources `NewServer`
    -- uses)
    "Hnew" ∷ backend.newPost d.γB d.P (fun _ => mvcc.lateW d.gx)
      (fun γB => batchLockInv γA (metaTM γB d.P)) d.be D ∗
    "%HD" ∷ ⌜mvcc.keyView (backend.vData d.P (D, ⟨∅, W64 0⟩)) ∅⌝ ∗
    "%HN" ∷ ⌜N + 7 ≤ backend.wbInit⌝ ∗
    -- (D22 J1a, 2026-10-26: of every backend at these parameters, for the snapshot path's backends;
    -- until then of `d` only) the Key bucket's size bound (no bbolt file holds `2 ^ 62` keys)
    "#Hsz" ∷ □ (∀ (γB : backend.BNames) (b : Loc), mvcc.keySized γB d.P b) ∗
    "Hlate" ∷ mvcc.lateReg d.gx ∗
    -- (D22, 2026-10-23: the backend over every bucket; a widening of the fresh data directory's
    -- facts, until then the opaque tokens `bkFresh d.γB "lease"`, `"auth"`, `"alarm"`) every rest
    -- bucket of the fresh file empty (absent or empty), the membership's three present
    -- (`bootstrap`'s `cluster.SetBackend` creates them: `MustCreateBackendBuckets`)
    "%HDr" ∷ ⌜(∀ n ∈ mvcc.restBuckets, (D.lookup n).getD ∅ = ∅) ∧
      D.lookup go!"members" = some ∅ ∧ D.lookup go!"members_removed" = some ∅ ∧
      D.lookup go!"cluster" = some ∅⌝ ∗
    -- (D22 S-g, D19l (v) (A); until then the opaque premise `mvcc.backendNoCompaction` of
    -- `NewServer.spec`) the fresh bbolt file records no compaction (`mvcc.store.restore`'s); (the
    -- backend-compaction stage, 2026-10-29, the user's decision: until then the token
    -- `mvcc.bkNoCmp d.γB` beside `Hnew`, which now holds it: `bootBackend_of_newPost`) a fact of `D`
    "%HnoCmp" ∷ ⌜mvcc.noCmpData D⌝ ∗
    -- (D22 S-j2, 2026-10-20; an environment assumption the user approved, "D22's environment
    -- assumptions approved") the backend file's directory entry is the server's: nothing else
    -- creates, renames or deletes a file at `<DataDir>/member/snap/db`. `applySnapshot`'s
    -- `storage.OpenSnapshotBackend` renames a received image onto it (`os.Rename`'s axiom takes it)
    "Hpath" ∷ backend.pathOwn (config.backendPathOf cfg.DataDir') ∗
    -- the error paths' close
    "#Hclose" ∷ □ ({{ True }}
      (App (Val (b @!! go.GoType.PointerType bootstrappedServer.ty @!! go!"Close")) (Val #()))
      {{ RET #(); True }}))

/-- **The configuration's URLs, as `bootstrap` reads them** (D19r (F), 2026-10-18): the peer and
client URL slices and the initial cluster's map (member name to its peer URLs' slice), with their
contents. -/
structure BootURLs [GooseExts] where
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
    (γ : SrvRaft) (id : w64) (ctxs : List (List w8)) (N : Nat) (dir : w64 → List GoString) :
    IProp GF :=
  iprop(□ ({{ bootCfgRO cfg U ∗ memStorRegAuth (∅ : GMap Loc MemStorNamesRec) }}
      (App (Val (@! bootstrap)) (Val #cfg))
    {{ (b : Loc) (err : GoInterface), RET (PairV #b #err);
        ⌜err ≠ GoInterface.nil⌝ ∨ ⌜err = GoInterface.nil⌝ ∗ bootOk cfg γ id ctxs N dir b }}))

instance bootstrapContract_persistent (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (U : BootURLs) (γ : SrvRaft) (id : w64) (ctxs : List (List w8)) (N : Nat)
    (dir : w64 → List GoString) :
    Persistent (bootstrapContract (GF := GF) cfg U γ id ctxs N dir) := by
  unfold bootstrapContract; infer_instance

end defs

section snap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [MemStorReg GF]

/-- **`run`'s snapshot contract from the application's token** (D17d, 2026-10-18; until then the
construction's residual `srvBuildGap`): the wrapper's `raftStorage` field holds the storage `ms`,
and `ms.Snapshot()` -- `MemoryStorage.Snapshot.spec` with the "no snapshot taken yet" token
`memSnapNone` (2026-10-30, the repair; until then the application's snapshot token) -- returns the
empty snapshot (index and term `0`), whole (metadata and conf state set), frozen. PENDING (Stage F,
reported): `Snapshot.spec` admits `ErrSnapshotTemporarilyUnavailable` for any storage, on which
`run` panics; the bare `MemoryStorage` never returns it, but its spec does not say so. -/
theorem rnSnapOnce_of_tok (wp_Snapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
    (E : RNEnv GF) (γ : RNNames) (r ms0 : Loc) (γs : MemStorNames) (Hms0 : γ.ms = ms0) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver -∗
      isRaftNode E γ r -∗ memStorInv ms0 γs γ.node.cl γ.id -∗ memSnapNone γs -∗
      ∃ ms : Loc, rnRaftStorageAddr r ↦□ ms ∗ rnSnapOnce ms γs (W64 0) (W64 0) := by
  subst Hms0
  iintro #Hpkg #Hrn #Hinv Hnone
  iunfold memStorInv at Hinv
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
  ihave #Hinit := isInitialized_access $$ Hraft
  iunfold isInitialized at Hinit
  iNamed Hinit
  ihave #Hc0 := memCompacted_zero (GF := GF) γs
  iapply wp_fupd
  wp_apply wp_Snapshot γ.ms γs _ 0 true _ $$ [$Hraft $Hinv $Hc0 Hnone $ErrSnapUnavail]
    as %snap %err ⟨Hnone, %Herr, %sv, Hw, %Hsv, -⟩
  · simp only [↓reduceIte]; iexact Hnone
  imod ownSnapW_persist $$ Hw with ⟨%pm, %pc, %Hnn, #Hsn, #Hpm, #Hpc, #Hcs⟩
  imodintro
  have Hsv0 := Hsv.2 rfl
  subst Hsv0
  subst Herr
  iapply HΦ $$ %snap %pm %pc %memSnapEmpty [] Hsn Hpm Hpc [] [Hnone]
  · ipureintro
    exact ⟨rfl, rfl, Hnn.1, Hnn.2⟩
  · iapply epCsOk_of_csOptA $$ Hcs
  · iexact Hnone

end snap

section transport
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- The `*rafthttp.Transport` `t` as an interface. -/
abbrev transportIface (t : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType
    go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty) #t

/-- The names a server's transport is fixed to (`srvTrKey`): the server `s` (whose `lgMu` readers
the transport's calls into `Raft` borrow, `srvLgReader`), the transport `t`, and the transport's
member, snapshot directory and lock's records. -/
abbrev SrvKey := Loc × Loc × w64 × GName × GName × GName

/-- The transport's names of a key. -/
abbrev SrvKey.trN (x : SrvKey) : TrN GF :=
  ⟨x.2.2.1, x.2.2.2.1, srvLgReader x.1, x.2.2.2.2.1, x.2.2.2.2.2, [], x.2.2.2.2.1, x.2.2.2.2.1⟩

/-- **The raft loop's key to the transport's `Send`** (rafthttp stage 6d, 2026-10-24, the user's
choice: the raft loop holds one of the transport's lock's reader tokens): the server's transport's
names, fixed for good under the name `γk` (a discarded element of a ghost map, `SrvKey`), and a
reader's token of that transport. The raft node's environment (`srvEr`) is built before the server
and its transport exist, so its `S` is this key, of a name `NewServer` allocates first
(`srvSendKey_alloc`) and fixes once the transport is started (`srvSendKey_fix`). -/
def srvTrKey (γn : NetNames GF) (γk : GName) : IProp GF :=
  iprop(∃ x : SrvKey, ghostMapElem γk () DFrac.discard x ∗ trTok γn x.2.1 (SrvKey.trN x))

/-- The key's name, allocated, the transport's names not yet fixed. -/
theorem srvSendKey_alloc :
    ⊢ |==> ∃ γk : GName, ghostMapAuth (GF := GF) γk 1 (∅ : GMap Unit SrvKey) := by
  imod ghost_map_alloc_empty (GF := GF) (K := Unit) (V := SrvKey) with ⟨%γk, Hk⟩
  imodintro
  iexists γk
  iexact Hk

/-- The key's name fixed to the server `s`'s transport `t` with the names `c` (once). -/
theorem srvSendKey_fix (γk : GName) (s t : Loc) (c : TrN GF) :
    ⊢ ghostMapAuth (GF := GF) γk 1 (∅ : GMap Unit SrvKey) ==∗
      ghostMapElem γk () DFrac.discard (s, t, c.lid, c.γd, c.γs, c.γr) := by
  iintro Hk
  imod ghost_map_insert_persist () (s, t, c.lid, c.γd, c.γs, c.γr) rfl $$ Hk with ⟨-, Hx⟩
  imodintro
  iexact Hx

/-- A reader's token of the fixed transport is the key. -/
theorem srvTrKey_of_trTok (γn : NetNames GF) (γk : GName) (s t : Loc) (c : TrN GF)
    (hR : c.R = srvLgReader s) :
    ghostMapElem γk () DFrac.discard (s, t, c.lid, c.γd, c.γs, c.γr) ∗ trTok γn t c ⊢
      srvTrKey γn γk := by
  iintro ⟨#Hk, Htok⟩
  iunfold srvTrKey
  iexists (s, t, c.lid, c.γd, c.γs, c.γr)
  iframe Hk
  obtain ⟨lid, γd, R, γs, γr, L, γk', γo⟩ := c
  simp only at hR
  subst hR
  iunfold trTok at Htok
  iunfold trTok
  iexact Htok

/-- **The network's transport, with the key** (stage 6d): a transport whose `Send` borrows a
reader's token of the transport fixed under `γk` borrows the key. -/
theorem netTransport_of_key (γn : NetNames GF) (lid : w64) (tr : GoInterface) (γk : GName)
    (s t : Loc) (c : TrN GF) (hR : c.R = srvLgReader s) (TS : IProp GF) :
    ⊢ ghostMapElem γk () DFrac.discard (s, t, c.lid, c.γd, c.γs, c.γr) -∗
      netTransport γn lid tr (trTok γn t c) TS -∗ netTransport γn lid tr (srvTrKey γn γk) TS := by
  iintro #Hk #Htr
  iunfold netTransport at Htr
  icases Htr with ⟨%ti, %Hti, #Hsend, #Hstop, #Hsnap⟩
  iunfold netTransport
  iexists ti
  isplitr
  · ipureintro; exact Hti
  isplitr
  · imodintro
    iintro %sl %msL %Φ !> ⟨Hsl, Hms, HS⟩ HΦ
    iunfold srvTrKey at HS
    icases HS with ⟨%x, #Hx, Htok⟩
    ihave %Heq := ghostMapElem_agree () γk DFrac.discard DFrac.discard _ _ $$ Hk Hx
    subst Heq
    ihave Htok' : trTok γn t c $$ [Htok]
    · obtain ⟨lid', γd, R, γs, γr, L, γk', γo⟩ := c
      simp only at hR
      subst hR
      iunfold trTok at Htok
      iunfold trTok
      iexact Htok
    wp_apply Hsend $$ [Hsl Hms Htok'] as Htok
    · iframe
    iapply HΦ
    iapply srvTrKey_of_trTok γn γk s t c hR $$ [Htok]
    iframe #
    iexact Htok
  isplitr
  · iexact Hstop
  · iexact Hsnap

/-- **No one may stop it** (D43 M5e, 2026-10-26): a network transport whose `Stop` asks nothing
it is given (`False`), the static server's raft wrapper's (its transport frozen, the stop token
the apply thread's, `srvApRes`; M6 hands it to the wrapper). -/
theorem netTransport_noStop (γn : NetNames GF) (lid : w64) (tr : GoInterface) (T TS : IProp GF) :
    netTransport (GF := GF) γn lid tr T TS ⊢ netTransport γn lid tr T iprop(False) := by
  iintro #Htr
  iunfold netTransport at Htr
  icases Htr with ⟨%ti, %Hti, #Hsend, #Hstop, #Hsnap⟩
  iunfold netTransport
  iexists ti
  isplitr
  · ipureintro; exact Hti
  iframe Hsend Hsnap
  iintro !> %Φ !> Hf -
  iexfalso; iexact Hf

/-- **The raft wrapper's transport from the network's** (D21 M2): an environment whose messages
carry their bundle from the member `lid` (`E.M m` gives `netBundle`) can send them through it. -/
theorem isRNTransport_of_net (γn : NetNames GF) (lid : w64) (E : RNEnv GF) (tr : GoInterface) :
    ⊢ □ (∀ m : Loc, E.M m -∗ netBundle γn.N lid m) -∗ netTransport γn lid tr E.S E.ST -∗
      isRNTransport E tr := by
  iintro #HM #Htr
  iunfold netTransport at Htr
  icases Htr with ⟨%ti, %Hti, #Hsend, #Hstop, -⟩
  iunfold isRNTransport
  iexists ti
  isplitr
  · ipureintro; exact Hti
  isplitr
  · imodintro
    iintro %sl %msL %Φ !> ⟨Hsl, Hms, HS⟩ HΦ
    wp_apply Hsend $$ [HS Hsl Hms] as HS
    · iframe HS Hsl
      iapply BigSepL.bigSepL_impl $$ Hms
      imodintro
      iintro %k %m %_ Hm
      iunfold rnMsgOk at Hm
      icases Hm with ⟨%to, %ty, -, HEM⟩
      iapply HM $$ HEM
    iapply HΦ
    iexact HS
  · iexact Hstop


/-- **The dynamic mode's hand-off** (D43 M5c, the user's (A)): with the transport's live right as
the raft wrapper's stop right (`E.ST`, carried by `stopped`), a started transport's network view
(`trState_net`: `Stop` takes the live right, `Stop_live`) is the raft wrapper's transport; the live
right itself goes to the apply thread, which hands it to `raftNode.stop` when `run` returns (M6).
The static server freezes instead (`E.ST = True`, `trFrozen_net`). -/
theorem isRNTransport_of_live (γn : NetNames GF) (lid : w64) (E : RNEnv GF) (tr : GoInterface)
    (t : Loc) (c : TrN GF) (hST : E.ST = iprop(∃ rs : trIds, trLive γn t c rs)) :
    ⊢ □ (∀ m : Loc, E.M m -∗ netBundle γn.N lid m) -∗
      netTransport γn lid tr E.S iprop(∃ rs : trIds, trLive γn t c rs) -∗ isRNTransport E tr := by
  iintro #HM #Htr
  rw [← hST] at *
  iapply isRNTransport_of_net γn lid E tr $$ HM Htr
/-- **The lessor's `SetCheckpointer`** (names-only, a contract of `lease.NewLessor`): it returns, the
checkpointer an opaque value (the lessor calls it later, outside the model: `NewServer`'s
closure over `raftRequest`). -/
def lessorCkptOk (l : GoInterface) : IProp GF :=
  iprop(∃ li : GoInterfaceOk, ⌜l = GoInterface.ok li⌝ ∗
    □ (∀ cp : GoFunc,
      {{ True }} (App (Val #(methods li.ty go!"SetCheckpointer" li.v)) (Val #cp)) {{ RET #(); True }}))

instance lessorCkptOk_persistent (l : GoInterface) : Persistent (lessorCkptOk (GF := GF) l) := by
  unfold lessorCkptOk; infer_instance

end transport

end EtcdGrove
end Perennial
