/- Lean-first (no Rocq counterpart).

# `etcd/dist`: the definitions its top-level statement is written in (DRAFT)

**Draft for review** (`notes/etcd-dist-plan.md`): not built, nothing imports it. What is a
placeholder is marked `PLACEHOLDER`; each names the stage of the plan that replaces it.

The deployment `etcd_safe` quantifies over: one etcd cluster of `k ≥ 1` members, each on a
machine of its own that may crash and restart (`servers`), and client machines that never crash,
each running one workload against the members' client addresses (`clients`). Its premise is one
decidable predicate, `Deployment.WellFormed` (addresses, names, ids, the server configuration in
its supported set, the workloads' bounds and their compatibility), plus the machines' start
states (`ServerStart`, `ClientStart`, `NetStart`) and the environment premises not yet
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
server configuration) and the client machines' workloads, one per client machine. -/
structure Deployment where
  members : List Member
  token : GoString
  cfg : ServerCfg
  workloads : List Workload

/-- PLACEHOLDER (stage D0/D2, open question Q5): **etcd's member id**, as `membership.NewMember`
computes it: the first 8 bytes, big-endian, of the SHA-1 of the member's sorted peer URLs
concatenated with the cluster token. To be a Lean definition (a SHA-1 in Lean, trusted and tested
against Go, or Perennial's `crypto/sha1` proved), so that `WellFormed` is evaluated by `decide`. -/
opaque memberId (peerURL : GoString) (token : GoString) : w64

/-- The members' ids, in the members' order. -/
def Deployment.ids (d : Deployment) : List w64 :=
  d.members.map (fun m => memberId (go!"http://" ++ m.peer) d.token)

/-- The addresses the deployment listens on: every member's peer and client address. -/
def Deployment.addrs (d : Deployment) : List GoString :=
  d.members.flatMap (fun m => [m.peer, m.client])

/-- A member name the data directory can carry: nonempty, of ASCII letters, digits and `-` (so
no `/`, `.` or `..`: one directory per member, `etcdWalAreasInit`'s `memberDataDir`). -/
def nameOk (n : GoString) : Bool :=
  !n.isEmpty && n.all (fun b => decide
    ((48 ≤ b.toNat ∧ b.toNat ≤ 57) ∨ (65 ≤ b.toNat ∧ b.toNat ≤ 90) ∨
    (97 ≤ b.toNat ∧ b.toNat ≤ 122) ∨ b.toNat = 45))

/-- **The deployment is well formed** (decidable; the theorem's one premise about the deployment):

1. the cluster has a member, and the members' names are distinct and valid (`nameOk`);
2. every address is the net extension's `addrOk` (a canonical `a.b.c.d:p`, first octet 1-223, port
   outside the ephemeral range), and the members' peer and client addresses are all distinct;
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

/-! ## Bootstrap's results and the trust-boundary premises (PLACEHOLDER) -/

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

/-- PLACEHOLDER (stage D6): **the trust-boundary contracts today's statement takes as Iris
premises** (`Hprem`: each member's `etcdstart.bootPremise`, with `bootstrapRestartContract` for its
restarts, `bootMarshal`, `etcdstart.commonPremises`; `Hctx`/`Hcec`: `ContextReadErrs`,
`ContextErrsClient`), at the proof's ghost state. A premise over the proof's ghost state has no
place in a deployment statement: each becomes an axiom of the trust boundary (reviewed) or a
theorem (bootstrap over the real code; context's facts in Perennial, item 8), and this goes. -/
opaque TrustBoundary (d : Deployment) (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry) : Prop

end boot

/-! ## The programs (PLACEHOLDER: stage D2, the translations) -/

section programs
variable [GooseExts] [GoGlobalContext]

/-- PLACEHOLDER (stage D2): **a member machine's boot program**, `server`'s initialization then
`server.Main(cfg)` with the member's `Config` as a Go value (`examples/etcd/dist/server`): the same
expression at the first start and after every crash (etcd's `NewServer` restarts from the WAL). -/
opaque serverProg (d : Deployment) (m : Member) : Expr

/-- PLACEHOLDER (stage D2): **a client machine's boot program**, `client`'s initialization then
`client.Main(w, eps)`, the members' client addresses `eps` in the members' order. -/
opaque clientProg (w : Workload) (eps : List GoString) : Expr

/-- The members' machines, with their start states `σs`, in the members' order. -/
def servers (d : Deployment) (σs : List state) : List (Expr × state) :=
  (d.members.zip σs).map (fun p => (serverProg d p.1, p.2))

/-- The client machines, with their start states `σc`, in the workloads' order. -/
def clients (d : Deployment) (σc : List state) : List (Expr × state) :=
  (d.workloads.zip σc).map (fun p => (clientProg p.1 (d.members.map Member.client), p.2))

end programs

/-! ## The machines' start states -/

section start
variable [GooseExts] [ElemExt Net.netExt] [ElemExt Fs.fsExt]

/-- The network at the start: no connection (`DistDeploy`'s, `kvraftRobust`'s `FreshNet`). -/
def NetStart (g : GlobalState) : Prop := (extGlobal Net.netExt g.globalWorld).init

/-- **A member's machine at the start** (`Robust` states the fresh Go process itself): no
listener; its files as on disk; the member's data directory and WAL area roots of its file
system, empty of what a member creates (`etcdWalAreasInit`, one directory). -/
def ServerStart (m : Member) (σ : state) : Prop :=
  (extLocal Net.netExt σ.world).init ∧
  Fs.FsInit (extLocal Fs.fsExt σ.world) ∧
  etcdWalAreasInit (extLocal Fs.fsExt σ.world) [memberDataDir m.name]

/-- A client's machine at the start: no listener; its files as on disk (review F11: the workloads'
packages reach `fileutil`, whose initializer probes the file system). -/
def ClientStart (σ : state) : Prop :=
  (extLocal Net.netExt σ.world).init ∧ Fs.FsInit (extLocal Fs.fsExt σ.world)

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

end etcd_dist
end EtcdGrove
end Perennial

end
