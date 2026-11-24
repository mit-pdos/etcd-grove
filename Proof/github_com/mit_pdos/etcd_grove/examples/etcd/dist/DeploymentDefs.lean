/- Lean-first (no Rocq counterpart).

# `etcd/dist`: what a deployment means (the proofs' vocabulary)

`etcd_safe`'s statement quantifies over the Go value of a deployment (`TopLevelDefs.lean`: Go's
`deployment.Deployment`, field by field). This module gives it its meaning, for the proofs: the typed
deployment (`typed.Deployment`: the workloads and the compactor as Lean types, numbers as `Nat`), its
well-formedness (`typed.Deployment.WellFormed`, the Lean mirror of Go's `deployment.WellFormed`), the
encoding of a typed deployment as a Go value (`typed.Deployment.Encodes`), and a Go value's
well-formedness (`Deployment.WellFormed`: it encodes a well-formed typed deployment), which the spec of
Go's `deployment.WellFormed` is to give when it returns `nil`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.TopLevelDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist
namespace typed

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

/-! ## The encoding of a typed deployment as the Go value -/

/-- The server configuration's Go value: the compactor off iff the retention is 0 (its mode then any),
otherwise the mode's name and the retention; the counts and the token provider as they are. -/
def ServerCfg.Encodes (t : ServerCfg) (c : etcd_dist.ServerCfg) : Prop :=
  (match t.compactor with
    | .off => sint.Z c.retention = 0
    | .revision r => c.compactorMode = go!"revision" ∧ sint.Z c.retention = r ∧ r ≠ 0
    | .periodic p => c.compactorMode = go!"periodic" ∧ sint.Z c.retention = p ∧ p ≠ 0) ∧
  uint.Z c.snapCount = t.snapCount ∧ uint.Z c.catchUp = t.catchUp ∧ c.auth = t.auth

/-- A workload's Go value: its kind's number, and the parameters the kind has (the others any: Go
ignores them). -/
def Workload.Encodes : Workload → etcd_dist.Workload → Prop
  | .kv c o, w => w.kind = W64 0 ∧ sint.Z w.clients = c ∧ sint.Z w.ops = o
  | .watch n o, w => w.kind = W64 1 ∧ sint.Z w.clients = n ∧ sint.Z w.ops = o
  | .cache n o, w => w.kind = W64 2 ∧ sint.Z w.clients = n ∧ sint.Z w.ops = o
  | .compact, w => w.kind = W64 3
  | .putget, w => w.kind = W64 4
  | .auth, w => w.kind = W64 5
  | .authLease, w => w.kind = W64 6
  | .leaseRead, w => w.kind = W64 7
  | .leaseCatchup, w => w.kind = W64 8
  | .leaseExpiry, w => w.kind = W64 9
  | .durable n, w => w.kind = W64 10 ∧ sint.Z w.clients = n

/-- **A typed deployment's Go value**: the same members, token and client machines' addresses, the
server configuration and every workload encoded. -/
def Deployment.Encodes (t : Deployment) (d : etcd_dist.Deployment) : Prop :=
  t.members = d.members ∧ t.token = d.token ∧ t.cfg.Encodes d.cfg ∧
  List.Forall₂ Workload.Encodes t.workloads d.workloads ∧ t.nodes = d.nodes

end typed

/-- **A deployment's Go value is well formed**: it encodes a well-formed typed deployment (what Go's
`deployment.WellFormed` returning `nil` is to mean). -/
def Deployment.WellFormed (d : Deployment) : Prop :=
  ∃ t : typed.Deployment, t.Encodes d ∧ t.WellFormed

/-- The addresses a deployment listens on: every member's peer and client address, then every client
machine's (the orchestrators listen nowhere). -/
def Deployment.addrs (d : Deployment) : List GoString :=
  d.members.flatMap (fun m => [m.peer, m.client]) ++ d.nodes.flatten

theorem typed.Deployment.addrs_encodes {t : typed.Deployment} {d : Deployment} (h : t.Encodes d) :
    t.addrs = d.addrs := by
  obtain ⟨hm, -, -, -, hn⟩ := h
  simp only [typed.Deployment.addrs, Deployment.addrs, hm, hn]

/-- A well-formed deployment's addresses are valid and distinct. -/
theorem Deployment.WellFormed.addrs {d : Deployment} (h : d.WellFormed) :
    d.addrs.Nodup ∧ ∀ a ∈ d.addrs, Net.addrOk a = true := by
  obtain ⟨t, he, hw⟩ := h
  rw [← typed.Deployment.addrs_encodes he]
  exact ⟨hw.2.2.2.2.1, hw.2.2.2.1⟩

end etcd_dist
end EtcdGrove
end Perennial

end
