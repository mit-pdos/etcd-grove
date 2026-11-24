/- Lean-first (no Rocq counterpart).

# `etcd/dist`: the definitions its top-level statement is written in (DRAFT)

**Draft** (`notes/etcd-dist-plan.md`): the statements' definitions (built; the Spec file imports it). What is a
placeholder is marked `PLACEHOLDER`; each names the stage of the plan that replaces it.

The deployment `etcd_safe` quantifies over: one etcd cluster of `k ≥ 1` members, each on a
machine of its own that may crash and restart (`servers`), and client machines that never crash,
each running one workload against the members' client addresses (`clients`). Its premise is one
decidable predicate, `Deployment.WellFormed` (addresses, names, ids, the server configuration in
its supported set, the workloads' bounds and their compatibility), plus the machines' start
states (`ServerStart`, `ClientStart`) and the environment premises not yet
discharged (`EtcdEnv`, the plan's "what is still not decidable").

The Go programs are `examples/etcd/dist/{server,client}` (sketches); their translations do not
exist yet, so the boot programs `serverProg`/`clientProg` are placeholders.
-/
module

public import Robustness.Statement
public import GooseLang.Ext.Net.Impl
public import GooseLang.Ext.Fs.Impl
public import GooseLang.Ext.IdIssue.Impl
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.FsExts
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SrvRaftLog
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.WalAreasInit
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Contracts
public import Proof.google_golang_org.grpc.InvGrpcServer
public import Proof.go_etcd_io.etcd.server.v3.storage.InvOpen
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseRead
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend
public import Perennial.GooseLang.InitAdequacy
public import GooseLang.Ext.Net.Ghost
public import GooseLang.Ext.IdIssue.Specs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NetExts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open go_etcd_io.raft.v3

/-! ## The server configuration and its supported set -/

/-- The auto-compactor (etcd's `--auto-compaction-mode` and `--auto-compaction-retention`). -/
inductive Compactor where
  | off
  /-- revision mode, keeping `retention` revisions -/
  | revision (retention : Nat)
  /-- periodic mode, keeping the revisions of the last `period` nanoseconds -/
  | periodic (period : Nat)
  deriving DecidableEq

/-- The periodic compactor. -/
def Compactor.isPeriodic : Compactor → Bool
  | .periodic _ => true
  | _ => false

/-- **The server configuration** (one per cluster, the same at every member): what
`examples/etcd/dist/server`'s `Config` takes beyond the member's own name and addresses. The other
`ServerConfig` fields are the examples' fixed values (`TickMs` 100, `ElectionTicks` 10, `MaxTxnOps`
128, `MaxRequestBytes` 1.5 MiB, the default quota, pre-vote off): open question Q9. -/
structure ServerCfg where
  compactor : Compactor
  /-- a disk snapshot every `snapCount` applied entries (`--snapshot-count`) -/
  snapCount : Nat
  /-- raft's log compacted to `catchUp` entries below a snapshot -/
  catchUp : Nat
  /-- the simple token provider (TTL 300 s) installed, or no token provider -/
  auth : Bool
  deriving DecidableEq

/-- **The supported set**: what `NewServer.spec` covers today (any snapshot settings since
2026-10-30; the compactor in either mode, a period of at least 10 ns: a shorter one busy-loops). -/
def ServerCfg.Supported (c : ServerCfg) : Prop :=
  (match c.compactor with
    | .off => True
    | .revision r => 1 ≤ r ∧ r < 2 ^ 63
    | .periodic p => 10 ≤ p ∧ p < 2 ^ 63) ∧
  1 ≤ c.snapCount ∧ c.snapCount < 2 ^ 64 ∧ 1 ≤ c.catchUp ∧ c.catchUp < 2 ^ 64

instance (c : ServerCfg) : Decidable c.Supported := by
  unfold ServerCfg.Supported; split <;> infer_instance

/-! ## Workloads -/

/-- **A client machine's workload** (`examples/etcd/dist/client`'s `Workload`): today's drivers
with their start removed. -/
inductive Workload where
  /-- txnlinfaultsN's: `clients` concurrent clients of `ops` operations, porcupine (txnlin) -/
  | kv (clients ops : Nat)
  /-- partition's `MainWatch`: a watch from revision 1, `writers` writers of `ops` Puts -/
  | watch (writers ops : Nat)
  /-- cache's: the watch cache, `writers` writers of `ops` Puts -/
  | cache (writers ops : Nat)
  /-- compactwatch's rounds of Put, explicit compaction, latest and old Gets; its watches -/
  | compact
  /-- compacted's Put then Get -/
  | putget
  /-- authN's set-up, barrier, principals and checks -/
  | auth
  /-- authlease's lease rows of auth -/
  | authLease
  /-- leaseN's lease reads at every member -/
  | leaseRead
  /-- leasecatchup's grant, fillers and listing (no cut of its own) -/
  | leaseCatchup
  /-- leaseexpiryN's expiring leases -/
  | leaseExpiry
  /-- restartN's durability check over `puts ≤ 256` Puts: acknowledged keys present at version
  1, other keys only from attempted Puts (no revision check) -/
  | durable (puts : Nat)
  deriving DecidableEq

/-- The workload's kind (its constructor), for "at most one of each kind". -/
def Workload.kind : Workload → Nat
  | .kv .. => 0 | .watch .. => 1 | .cache .. => 2 | .compact => 3 | .putget => 4 | .auth => 5
  | .authLease => 6 | .leaseRead => 7 | .leaseCatchup => 8 | .leaseExpiry => 9 | .durable _ => 10

/-- **A workload that writes keys** (each under its own prefix, `client.go`: no two workloads
write one key). The lease workloads only grant and revoke leases with no keys attached, which
leaves the store's revision unchanged. -/
def Workload.writesKeys : Workload → Bool
  | .leaseRead | .leaseCatchup | .leaseExpiry => false
  | _ => true

/-- **A workload whose check reads the store's revisions as its own** (review F1): txnlin's model
starts at revision 1 and checks every reply's revision; the watch checks need gap-free revisions;
the auth workloads' set-ups and checks likewise. It needs to be the only workload writing keys. -/
def Workload.needsSoleWriter : Workload → Bool
  | .kv .. | .watch .. | .cache .. | .auth | .authLease => true
  | _ => false

/-- **A workload that changes what every other client may do** (it enables auth): alone. -/
def Workload.alone : Workload → Bool
  | .auth | .authLease => true
  | _ => false

/-- A workload that needs the simple token provider. -/
def Workload.needsAuth : Workload → Bool
  | .auth | .authLease => true
  | _ => false

/-- A workload that grants leases (whose ids must be apart in 15 bits across the members). -/
def Workload.grantsLeases : Workload → Bool
  | .authLease | .leaseCatchup | .leaseExpiry => true
  | _ => false

/-- A workload whose proof needs that no lease expires (`lease.leasesNoExpiry`). -/
def Workload.needsNoExpiry : Workload → Bool
  | .authLease | .leaseCatchup => true
  | _ => false

/-- The workload's own bounds (today's drivers' premises). -/
def Workload.BoundsOk : Workload → Prop
  | .kv c o => c < 2 ^ 31 ∧ c * o < 2 ^ 60
  | .watch w o => w < 2 ^ 31 ∧ w * o < 2 ^ 62
  | .cache w o => w < 2 ^ 31 ∧ w * o < 2 ^ 62
  | .durable n => n ≤ 256
  | _ => True

/-- **The workload's client machines** (D8; Go's `client.NodeCount`): kv's clients, watch's and cache's
writers, auth's four principals (`auth.Principals()`), each on a machine of its own, called by the
workload's orchestrator machine; the other workloads run on their orchestrator alone. -/
def Workload.nodeCount : Workload → Nat
  | .kv c _ => c | .watch w _ => w | .cache w _ => w | .auth => 4 | _ => 0

instance (w : Workload) : Decidable w.BoundsOk := by
  cases w <;> unfold Workload.BoundsOk <;> infer_instance

/-- **The workloads can run at once on one cluster** (review F1): at most one of each kind; a
workload that enables auth alone; a workload that reads revisions as its own beside no other
workload that writes keys; never an expiring lease beside a workload that needs none to expire. -/
def Compatible (ws : List Workload) : Prop :=
  (ws.map Workload.kind).Nodup ∧
  ((∃ w ∈ ws, w.alone = true) → ws.length = 1) ∧
  (∀ w ∈ ws, w.needsSoleWriter = true →
    ∀ w' ∈ ws, w' ≠ w → w'.writesKeys = false) ∧
  ¬ (Workload.leaseExpiry ∈ ws ∧ ∃ w ∈ ws, w.needsNoExpiry = true)

instance (ws : List Workload) : Decidable (Compatible ws) := by
  unfold Compatible; infer_instance

/-! ## The deployment -/

/-- A member: its name (its data directory `/tmp/etcd-grove-data/<name>.etcd`, its WAL area
`/tmp/etcd-grove-wal/<name>.etcd`), its peer address (its one peer URL `http://peer`, served by its
raft handler) and its client address (served by etcd's gRPC API). -/
structure Member where
  name : GoString
  peer : GoString
  client : GoString

/-- **A deployment**: the cluster (its members, in the initial cluster's order, its token, its
server configuration), the workloads (each run by an orchestrator machine) and, per workload, its
client machines' addresses (`nodes`, in the workloads' order; `nodeCount` of them each, D8). -/
structure Deployment where
  members : List Member
  token : GoString
  cfg : ServerCfg
  workloads : List Workload
  nodes : List (List GoString)

/-- Every client machine of the deployment: its workload, its index among the workload's client
machines, its address (in the workloads' order, then the index's). -/
def Deployment.nodeList (d : Deployment) : List (Workload × Nat × GoString) :=
  (d.workloads.zip d.nodes).flatMap (fun p => p.2.zipIdx.map (fun q => (p.1, q.2, q.1)))

/-- PLACEHOLDER (stage D2, open question Q5): **etcd's member id**, as `membership.NewMember`
computes it: the first 8 bytes, big-endian, of the SHA-1 of the member's sorted peer URLs
concatenated with the cluster token. Since 2026-11-24 not in any premise: `WellFormed` is checked by
the programs (Go's `dist.WellFormed`, which computes the ids with `membership.ComputeMemberID` over
Perennial's translated and proved `crypto/sha1`); this becomes that function's Lean model, used only
inside the proof. -/
opaque memberId (peerURL : GoString) (token : GoString) : w64

/-- The members' ids, in the members' order. -/
def Deployment.ids (d : Deployment) : List w64 :=
  d.members.map (fun m => memberId (go!"http://" ++ m.peer) d.token)

/-- The addresses the deployment listens on: every member's peer and client address, then every
client machine's (the orchestrators listen nowhere). -/
def Deployment.addrs (d : Deployment) : List GoString :=
  d.members.flatMap (fun m => [m.peer, m.client]) ++ d.nodes.flatten

/-- A member name the data directory can carry: nonempty, of ASCII letters, digits and `-` (so
no `/`, `.` or `..`: one directory per member, `etcdWalAreasInit`'s `memberDataDir`). -/
def nameOk (n : GoString) : Bool :=
  !n.isEmpty && n.all (fun b => decide
    ((48 ≤ b.toNat ∧ b.toNat ≤ 57) ∨ (65 ≤ b.toNat ∧ b.toNat ≤ 90) ∨
    (97 ≤ b.toNat ∧ b.toNat ≤ 122) ∨ b.toNat = 45))

/-- **The deployment is well formed** (decidable; the theorem's one premise about the deployment):

1. the cluster has a member, and the members' names are distinct and valid (`nameOk`);
2. every address is the net extension's `addrOk` (a canonical `a.b.c.d:p`, first octet 1-223, port
   outside the ephemeral range), and the members' peer and client addresses and the client
   machines' addresses are all distinct; each workload has its `nodeCount` client machines;
3. the members' ids have distinct, nonzero 16 low bits (etcd's request ids carry them: `BootCore`'s
   `lowNodup`/`lowNz`), and, when a workload grants leases, distinct 15 low bits
   (`leaseIdsApart`, `issues/etcd-lease-id-mask-member-prefix.md`);
4. the token is nonempty, and the server configuration is in the supported set;
5. the workloads are compatible (`Compatible`) and within their bounds, and a workload that
   needs the token provider has it; `compact` not under the periodic compactor (review F5); no token
   provider beside expiring leases (review F10). -/
def Deployment.WellFormed (d : Deployment) : Prop :=
  d.members ≠ [] ∧ (d.members.map Member.name).Nodup ∧ (∀ m ∈ d.members, nameOk m.name = true) ∧
  (∀ a ∈ d.addrs, Net.addrOk a = true) ∧ d.addrs.Nodup ∧
  d.nodes.length = d.workloads.length ∧ (∀ p ∈ d.workloads.zip d.nodes, p.2.length = p.1.nodeCount) ∧
  (d.ids.map (fun id => uint.Z id % 2 ^ 16)).Nodup ∧ (∀ id ∈ d.ids, uint.Z id % 2 ^ 16 ≠ 0) ∧
  ((∃ w ∈ d.workloads, w.grantsLeases = true) → leaseIdsApart d.ids) ∧
  d.token ≠ [] ∧ d.cfg.Supported ∧
  Compatible d.workloads ∧ (∀ w ∈ d.workloads, w.BoundsOk) ∧
  (∀ w ∈ d.workloads, w.needsAuth = true → d.cfg.auth = true) ∧
  -- review F5: compactwatch's checks hold under the revision compactor (or none), not the periodic
  (Workload.compact ∈ d.workloads → d.cfg.compactor.isPeriodic = false) ∧
  -- review F10: the revocable lease mode with the token provider needs `leasesNoExpiry`
  ¬ (d.cfg.auth = true ∧ Workload.leaseExpiry ∈ d.workloads)

instance (d : Deployment) : Decidable d.WellFormed := by
  unfold Deployment.WellFormed leaseIdsApart; infer_instance

/-! ## Bootstrap's results -/

section boot
variable [GooseExts]

/-- **`bootstrap`'s results, as Go computes them** (every example's `BootFacts`, for the one
cluster): the peers `ps` in `bootstrap`'s order, a permutation of the members' ids, their contexts
`ctxs` and the bootstrap log `boot` (`BootCore`). Not decidable as stated (the log's encoding is
opaque); like `memberId`, a function of the deployment once etcd's computation is a Lean
definition (open question Q5). -/
structure BootFacts (d : Deployment) (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry) : Prop extends BootCore ps ctxs boot where
  perm : ps.Perm d.ids

end boot

/-! ## The programs (PLACEHOLDER: stage D2, the translations)

Every machine's program takes the **whole deployment** as a Go value (`dist.Deployment`) and its
own index, and first checks the deployment (Go's `dist.WellFormed`, Lean's `Deployment.WellFormed`),
returning at once if it fails (rule: a premise the program can check is the program's, with a Go test
that the check passes and the real path runs: `TestWellFormed`, `TestDist`). So `WellFormed` is not a
premise of the statement: on a malformed deployment every machine stops at its first step. -/

section programs
variable [GooseExts] [GoGlobalContext]

/-- PLACEHOLDER (stage D2): **member `i`'s machine's boot program**, `server`'s initialization then
`server.MainDeployment(d, i)` (`dist.WellFormed(d)`, then `server.Main(d.ServerConfig(i))`), the
deployment as a Go value: the same expression at the first start and after every crash (etcd's
`NewServer` restarts from the WAL). -/
opaque serverProg (d : Deployment) (i : Nat) : Expr

/-- PLACEHOLDER (stage D2): **workload `j`'s orchestrator machine's boot program**, `client`'s
initialization then `client.MainDeployment(d, j)` (`dist.WellFormed(d)`, then `client.MainReady(w,
eps, nodes, _)` with the members' client addresses `eps` in the members' order and the workload's
client machines' addresses `nodes`, D8). -/
opaque clientProg (d : Deployment) (j : Nat) : Expr

/-- PLACEHOLDER (stage D2): **the `n`-th client machine's boot program** (in `nodeList`'s order),
`client`'s initialization then `client.NodeDeployment(d, n)` (`dist.WellFormed(d)`, then
`client.NodeMain(w, c, addr, eps)`: client machine `c` of workload `w`, listening at `addr`, D8). -/
opaque nodeProg (d : Deployment) (n : Nat) : Expr

/-- The members' machines, with their start states `σs`, in the members' order. -/
def servers (d : Deployment) (σs : List state) : List (Expr × state) :=
  σs.mapIdx (fun i σ => (serverProg d i, σ))

/-- The workloads' orchestrator machines, with their start states `σc`, in the workloads' order. -/
def clients (d : Deployment) (σc : List state) : List (Expr × state) :=
  σc.mapIdx (fun j σ => (clientProg d j, σ))

/-- The workloads' client machines, with their start states `σn`, in `nodeList`'s order. -/
def nodeMachines (d : Deployment) (σn : List state) : List (Expr × state) :=
  σn.mapIdx (fun n σ => (nodeProg d n, σ))

/-- **Every machine of the deployment**: the members', then the orchestrators', then the client
machines'. -/
def machines (d : Deployment) (σs σc σn : List state) : List (Expr × state) :=
  servers d σs ++ clients d σc ++ nodeMachines d σn

end programs

/-! ## The machines' start states -/

section start
variable [GooseExts] [ElemExt Net.netExt] [ElemExt Fs.fsExt]

/-- **A member's machine at the start** (`Robust` states the fresh Go process itself, and the
extensions' initial states: for the net extension no listener on any machine and no connection,
`initLocal`/`initGlobal`): its files as on disk (`FsInit`: a premise until `fsSemWithS` gets the
file extension's `initLocal`, D4a); the member's data directory and WAL area roots of its file
system, empty of what a member creates (`etcdWalAreasInit`, one directory). -/
def ServerStart (m : Member) (σ : state) : Prop :=
  Fs.FsInit (extLocal Fs.fsExt σ.world) ∧
  etcdWalAreasInit (extLocal Fs.fsExt σ.world) [memberDataDir m.name]

/-- A client's machine at the start: its files as on disk (review F11: the workloads' packages reach
`fileutil`, whose initializer probes the file system; a premise until D4a, as `ServerStart`'s). -/
def ClientStart (σ : state) : Prop :=
  Fs.FsInit (extLocal Fs.fsExt σ.world)

end start

/-! ## What is not decidable yet: the environment premises carried over -/

section env
variable [GooseExts]

/-- **The environment and workload premises `etcd_safe` takes that this draft keeps**, opaque,
each to be discharged or turned into a decidable fact of `WellFormed` (the plan, "What is still not
decidable"): the auth store's records fit bbolt's value bound; every backend under its quota;
every gRPC reply below the transport's maximum; the disk cooperates (bbolt's and the snapshots'
opens); the peers answer `/leases/internal` as etcd does or not with `200` (true by construction
here: every peer address is a member's raft handler); no lease expires, when a workload needs it.
(The programs' prometheus names, `HNs`, were a premise until prom-registry, 2026-11-22: each
proof allocates its registration rights itself.) (`verifyEnvOff` and the proxy variables are gone if the
server clears them, `clearProxyEnv`: open question Q10.) -/
structure EtcdEnv (d : Deployment) : Prop where
  authRecords : authRecordsFit
  underQuota : apply.backendUnderQuota
  repliesFit : grpcRepliesFit
  disk : storage.diskOk
  leasePeers : leasePeersOk
  noExpiry : (∃ w ∈ d.workloads, w.needsNoExpiry = true) → lease.leasesNoExpiry
  /-- PLACEHOLDER (review F8): `addrsUnclaimed`'s part (b) without its world assumption: etcd's
  names-only peer requests (the prober, the version monitor, bootstrap's `GET /members`,
  leasehttp's forwards) reach only the raft handler's mux, until those clients are translated over
  the net extension (phase 7 S5). -/
  peerRequests : True

end env

/-! ## The ghost state the statements' Iris premise is stated at -/

attribute [local instance] etcdNetExts

open Iris Iris.BI Iris.ProgramLogic Iris.Std in
/-- **The functors** the statements' Iris premise (`HEnvTok`) is stated at: `putgetGF`'s layout (the
universal camera `AllG` at slot 0, invariants, later credits, GooseLang's heap, prophecies and package
state, a ghost variable at slot 7; every other slot the unit functor). -/
def etcdDistGF : BundledGFunctors := fun i =>
  match i with
  | 0 => ⟨AllURF, inferInstance⟩
  | 1 => ⟨InvMapF, inferInstance⟩
  | 2 => ⟨constOF CoPsetDisjL, inferInstance⟩
  | 3 => ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  | 4 => ⟨Auth.AuthURF (constOF Credit), inferInstance⟩
  | 5 => ⟨constOF (NaHeapUR Loc val), inferInstance⟩
  | 6 => ⟨constOF (HeapView proph_id (Agree (DiscreteO (List val))) (GMap proph_id)),
          inferInstance⟩
  | 7 => ⟨GhostVarF (GMap GoString Bool), inferInstance⟩
  | _ => ⟨constOF Unit, inferInstance⟩

open Iris Iris.BI Iris.ProgramLogic Iris.Std in
/-- The universal camera at slot 0. -/
@[instance_reducible] def etcdDistGF_allG : AllG etcdDistGF := ⟨⟨0, rfl⟩⟩

open Iris Iris.BI Iris.ProgramLogic Iris.Std in
/-- The ghost state of GooseLang over `etcdNetExts` (each extension's at the universal camera). -/
instance etcdDistGF_gooseGpreS : GooseGpreS etcdDistGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨etcdDistGF_allG⟩, ⟨etcdDistGF_allG⟩, ⟨etcdDistGF_allG⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := etcdDistGF_allG

end etcd_dist
end EtcdGrove
end Perennial

end
