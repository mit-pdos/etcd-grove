/-
**What `NewServer` is proved over: `bootstrap`'s result and the names-only constructors'
contracts** (the server-construction unit's stage N0, 2026-10-16; D13b, D13d,
`notes/decisions.md`). Lean-first (no Rocq counterpart). Unit N1's file: the contracts here are
used by `NewServer`'s proof alone (unit N2 does not read them), and N1 refines them.

* **`bootstrap`'s contract** (`bootstrapContract`, D13b) is a premise of `NewServer.spec`, a triple
  in its precondition, not an axiom. Its raft configuration is `raftConfig`'s (`bootstrap.go:572`)
  of the patched fork (D15, temporary): `CheckQuorum` is `!cfg.DisableCheckQuorum` (etcd's own code
  sets it `true`; the field, added by the patch, is off by default) and `PreVote` is `cfg.PreVote`;
  `NewServer.spec` requires the configuration that turns both off, the only one the raft start
  result (`NodeStartSpec`) covers. On success the bootstrapped record carries `bootOk`:
  - the records `NewServer` reads (`b`, `b.storage`, `b.storage.backend`, `b.storage.wal`,
    `b.cluster`, `b.raft`);
  - `b.raft` with `NodeStartSpec`'s premises on it (the raft config valid, `CheckQuorum`/
    `PreVote` as `cfg` sets them, the fresh registered `MemoryStorage`, the peers and the bootstrap log, the
    `InitialState` closure, `Marshal` at the peers' conf changes) and the cluster's
    `IsIDRemoved` contract;
  - the cluster (`isRaftCluster`, its id, this node's id, the remote members, read-only);
  - the consistent index at `0` (`isCI`, `ciOwner` of the backend, the applying index at `0`)
    and the apply protocol's names and invariant (`consInv`, the apply thread's half at the start:
    the backend's batch lock's resource names them, so they exist before the backend; the
    protocol's allocation is `consInv_alloc`, `BuildAlloc.lean`), the backend's meta keys at
    `(0, 0)` (a new cluster's fresh backend);
  - the backend of the real instance `d` with the server's hooks (`server_kv_backend_hooks`'s
    premises but the post-lock hook's, which `NewServer` sets: the hook's half, its open fraction,
    the write budget);
  - `b.Close()` returns (the error paths' deferred close).
* **`transportStarted`**: the `rafthttp.Transport` after `Start` (names-only): its `Send`/`Stop`
  for any environment (`isRNTransport`: the transport asks nothing of the messages) and its
  `ActiveSince` (`rafthttp.isTransporter`).
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
2026-10-17: `membership.peerURLsOk`, the transport's `AddRemote` panics otherwise). -/
def memberRO (m : Loc) : IProp GF :=
  iprop(⌜m ≠ null⌝ ∗ ∃ (v : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member)
      (us : List GoString), m ↦□ v ∗ v.RaftAttributes'.PeerURLs' ↦*□ us ∗
    ⌜membership.peerURLsOk us⌝)

instance memberRO_persistent (m : Loc) : Persistent (memberRO (GF := GF) m) := by
  unfold memberRO; infer_instance

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

/-- **The background goroutines' effects** (opaque, the named premises of D14e and D14g,
2026-10-17): what the model does not cover of the goroutines the construction starts, assumed as
a whole. `transportEffectsOk`: the transport's goroutines (`rafthttp`: each peer's readers and
writers, the inbound messages) call into the server (`Process`, `ReportUnreachable`,
`ReportSnapshot`, `IsIDRemoved`) and the network safely -- the cluster's message trust
assumption. `ckptEffectsOk`: the lessor's loop, once its lessor is promoted, calls the server's
checkpointer (`NewServer`'s closure over `raftRequest`, installed when the `LeaseCheckpoint`
feature is on), which proposes outside the request path's model. Premises of
`rafthttp.Transport`'s and `lease.NewLessor`'s axioms and so of `NewServer.spec`; nothing in the
model proves or refutes them. -/
opaque transportEffectsOk : Prop

@[inherit_doc transportEffectsOk]
opaque ckptEffectsOk : Prop

/-- **The auth store's records fit bbolt's value bound** (opaque, a workload premise; unit N4,
2026-10-17): a user's record grows with its roles and a role's with its permissions, each grant
within the request size bound; a record above bbolt's `MaxValueSize` (`2 ^ 31 - 2` bytes) makes
the backend's put fatal (`issues/etcd-backend-put-value-too-large-fatal.md`). The model does not
keep the auth store's contents, so the bound is named, a premise of `auth.NewAuthStore`'s axiom
and of `NewServer.spec`. -/
opaque authRecordsFit : Prop

/-- **The bootstrapped record `b`** (see the file header) of the configuration `cfg` (its
`DisableCheckQuorum` and `PreVote`, D15) for this node `id` of the cluster with
raft's names `γ` and the bootstrap log `bootLog`, the backend's write-back budget `N + 7` (D14g,
2026-10-17: what the backend has, within its `2 ^ 40` bound, `backend.bgOk`: `N` for the applied
entries, `NewServer.spec`'s lifetime bound, and seven for the construction: `mvcc.New` two,
`NewLessor` one, `NewAuthStore` two, `NewAlarmStore` one, `SetTxPostLockInsideApplyHook` one;
until then `2 ^ 64 + 3`, which no backend has); the post-lock hook unset (nil). -/
def bootOk (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (γ : RaftNames) (id : w64)
    (bootLog : List EntryM) (N : Nat) (b : Loc) : IProp GF :=
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
      sint.Z cv.MaxInflightMsgs' < 2 ^ 62 ∧ cv.CheckQuorum' = !cfg.DisableCheckQuorum' ∧
      cv.DisableProposalForwarding' = false ∧ cv.ReadOnlyOption' = W64 0 ∧
      cv.DisableConfChangeValidation' = false ∧
      (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) ∧
      cv.AsyncStorageWrites' = false ∧ cv.PreVote' = cfg.PreVote' ∧ cv.Applied' = W64 0 ∧
      cv.ID' = id ∧
      ps = pv.map Peer.ID' ∧ ps ≠ [] ∧ ps.Nodup ∧ W64 0 ∉ ps ∧ (ps.length : Int) ≤ 2 ^ 62 ∧
      cv.ID' ∈ ps ∧ γ.reCfg = GMap.listToSet ps ∧ γ.reBoot = bootLog ∧
      BootLogOk γ.reCCOk ps bootLog⌝ ∗
    "Hc" ∷ bv.config' ↦ cv ∗ "#Hlok" ∷ isLogger lok ∗
    "#Hreg" ∷ memStorReg bv.storage' γs ∗
    "#Hsi" ∷ isStorage (memStorIface bv.storage') ∗
    "Hstor" ∷ ownStorage (memStorIface bv.storage') memStorEmpty ∗
    "#Hinit" ∷ □ (∀ (Φ : val → IProp GF) (ss' : entryID),
       ownStorage (memStorIface bv.storage') { memStorEmpty with ss := ss' } -∗
       (∀ (hp cs : Loc) (al : Bool),
        ownStorage (memStorIface bv.storage') { memStorEmpty with ss := ss' } -∗
        hsOpt hp (HardStateM.mk (W64 0) (W64 0) (W64 0)) -∗
        csPts cs DFrac.discard (ConfStateM.mk [] [] [] [] false) al -∗
        Φ (PairV (PairV #hp #cs) #interface.nil)) -∗
       WP (App (Val #(methods (go.GoType.PointerType MemoryStorage.ty) go!"InitialState" #bv.storage'))
         (Val #())) {{ Φ }}) ∗
    "Hpeers" ∷ bv.peers' ↦* pv ∗ "#Hctx" ∷ peersCtx pv ctxs ∗
    "#Hmarshal" ∷ bootMarshal ps ctxs bootLog ∗
    -- the cluster
    "#Hcl" ∷ rnClusterOk bc.cl' ∗ "#Hrc" ∷ membership.isRaftCluster bc.cl' ∗
    "#Hcid" ∷ membership.clusterCid bc.cl' cid ∗ "%Hid" ∷ ⌜bc.nodeID' = id⌝ ∗
    "#Hrms" ∷ bc.remotes' ↦*□ rms ∗ "#Hrmsi" ∷ ([∗list] m ∈ rms, memberRO m) ∗
    -- the cluster's contracts (unit N4, 2026-10-17): the lessor's (`Version()`), and the apply
    -- package's at the backend's batch lock and any frozen hook (its writes: one write-back
    -- each, `membershipBackend`'s `LockInsideApply`/`Unlock`, as the stores', D14f)
    "#Hclok" ∷ lease.clusterOk (interface.mkOk (go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty) #bc.cl') ∗
    "#Hisc" ∷ □ (∀ (γ' : mvcc.StoreNames) (f : GoFunc), ⌜γ'.kb = some d⌝ -∗
      backend.plHookRO d.γB f -∗ ⌜f ≠ func.nil⌝ -∗
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

/-- **`bootstrap`'s contract** (D13b: a premise of `NewServer.spec`, see the file header): on the
configuration `cfg`, an error, or the record with `bootOk` (at the write-back budget `N + 7`). -/
def bootstrapContract (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (γ : RaftNames)
    (id : w64) (bootLog : List EntryM) (N : Nat) : IProp GF :=
  iprop(□ ({{ True }} (App (Val (@! bootstrap)) (Val #cfg))
    {{ (b : Loc) (err : GoInterface), RET (PairV #b #err);
        ⌜err ≠ GoInterface.nil⌝ ∨ ⌜err = GoInterface.nil⌝ ∗ bootOk cfg γ id bootLog N b }}))

instance bootstrapContract_persistent (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (γ : RaftNames) (id : w64) (bootLog : List EntryM) (N : Nat) :
    Persistent (bootstrapContract (GF := GF) cfg γ id bootLog N) := by
  unfold bootstrapContract; infer_instance

end defs

section transport
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The `*rafthttp.Transport` `t` as an interface. -/
abbrev transportIface (t : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType
    go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty) #t

/-- **The transport `t` live** (opaque, exclusive; unit N4, 2026-10-17): started and not
stopped. `Start` gives it; `AddRemote`/`AddPeer` take it and give it back (`AddPeer` panics after
`Stop`); it is given up for `transportStarted` (whose `isRNTransport` has `Stop`). -/
opaque transportLive (t : Loc) : IProp GF

/-- **The transport `t` after `Start`** (persistent; names-only, see the file header). -/
def transportStarted (t : Loc) : IProp GF :=
  iprop(□ (∀ E : RNEnv GF, isRNTransport E (transportIface t)) ∗
    rafthttp.isTransporter (transportIface t))

instance transportStarted_persistent (t : Loc) : Persistent (transportStarted (GF := GF) t) := by
  unfold transportStarted; infer_instance

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
