/- Lean-first (no Rocq counterpart).

# `etcd/dist`: the definitions its top-level statement is written in

The statements' definitions (the Spec file imports this module): the deployment as the programs receive
it (a Go value: `Deployment`, `deploymentLit`), the machines and their boot programs (`servers`,
`clients`, `nodeMachines`), the machines' start states (`ServerStart`, `ClientStart`), the peers and contexts
`bootstrap` computes from the deployment (`distPs`, `distCtxs`) and its bootstrap log (`BootFacts`), the environment premises not yet discharged (`EtcdEnv`) and the two bounds (`etcdThreads`,
`etcdSteps`). What a placeholder is is marked `PLACEHOLDER`, with the stage of `notes/etcd-dist-plan.md`
that replaces it. No premise is on the deployment: every program checks it (Go's `deployment.WellFormed`)
and returns if it fails.
-/
module

public import Robustness.Statement
public import Iris.Instances.Lib.NaInvariants
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.MemberId
public import GooseLang.Ext.Net.Impl
public import GooseLang.Ext.Fs.Impl
public import GooseLang.Ext.IdIssue.Impl
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.FsExts
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SrvRaftLog
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.WalAreasInit
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BootValues
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Contracts
public import Proof.google_golang_org.grpc.InvGrpcServer
public import Proof.go_etcd_io.etcd.server.v3.storage.InvOpen
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseRead
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend
public import Perennial.GooseLang.InitAdequacy
public import GooseLang.Ext.Net.Ghost
public import GooseLang.Ext.IdIssue.Specs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NetExts
public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server
public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open go_etcd_io.raft.v3

/-! ## The deployment, as the programs receive it (Go's `deployment.Deployment`, field by field)

The statement quantifies over the Go value every machine's program receives: these structures mirror
`examples/etcd/dist/deployment`'s types field for field (Go's `int`/`int64`/`uint64` as `w64`), and
`deploymentLit` is the composite literal of that value. What a deployment means (the workloads, the
compactor, which deployments are well formed) is the programs' own business (Go's
`deployment.WellFormed`); its Lean vocabulary is the proofs' (`DeploymentDefs.lean`), not the
statement's. -/

/-- Go's `deployment.Member`: a member's name (its data directory `/tmp/etcd-grove-data/<name>.etcd`,
its WAL area `/tmp/etcd-grove-wal/<name>.etcd`), its peer address (its one peer URL `http://peer`, served
by its peer handler) and its client address (served by etcd's gRPC API). -/
structure Member where
  name : GoString
  peer : GoString
  client : GoString

/-- Go's `deployment.ServerCfg`: the auto-compactor's mode and retention (off when the retention is 0),
the snapshot count, the catch-up entries, the simple token provider. -/
structure ServerCfg where
  compactorMode : GoString
  retention : w64
  snapCount : w64
  catchUp : w64
  auth : Bool

/-- Go's `deployment.Workload`: its kind (`deployment.Kind`, an `int`: `KV` 0, `Watch` 1, `Cache` 2,
`Compact` 3, `PutGet` 4, `Auth` 5, `AuthLease` 6, `LeaseRead` 7, `LeaseCatchup` 8, `LeaseExpiry` 9,
`Durable` 10) and its two parameters. -/
structure Workload where
  kind : w64
  clients : w64
  ops : w64

/-- Go's `deployment.Deployment`: the members (in the initial cluster's order), the token, the server
configuration, the workloads (each run by an orchestrator machine) and, per workload, its client
machines' addresses. -/
structure Deployment where
  members : List Member
  token : GoString
  cfg : ServerCfg
  workloads : List Workload
  nodes : List (List GoString)

/-- Every client machine of the deployment (Go's `Deployment.Node`): its workload, its index among the
workload's client machines, its address (in the workloads' order, then the index's). -/
def Deployment.nodeList (d : Deployment) : List (Workload × Nat × GoString) :=
  (d.workloads.zip d.nodes).flatMap (fun p => p.2.zipIdx.map (fun q => (p.1, q.2, q.1)))

/-- A workload whose proof needs that no lease expires (`AuthLease`, `LeaseCatchup`). -/
def Workload.needsNoExpiry (w : Workload) : Bool :=
  decide (w.kind = W64 6 ∨ w.kind = W64 8)

/-- **etcd's member id** of the member whose one peer URL is `peerURL`, in the cluster `token`: the Lean
model of `computeMemberID`, single URL, no time (`membership.memberIdOf`: the first 8 bytes, big-endian,
of the SHA-1 of the URL followed by the token), the definition `membership.NewMember`'s proved one-URL spec (`specOne`)
gives. -/
def memberId (peerURL : GoString) (token : GoString) : w64 := membership.memberIdOf peerURL token

/-- The members' ids, in the members' order. -/
def Deployment.ids (d : Deployment) : List w64 :=
  d.members.map (fun m => memberId (go!"http://" ++ m.peer) d.token)

/-! ## Bootstrap's results -/

section boot
variable [GooseExts]

/-- A URL `http://<host>` (`url.URL{Scheme: "http", Host: host}`): a member's one peer URL, as
`server.serverConfig` builds it from the member's peer address. -/
def peerURL (host : GoString) : _root_.Perennial.net.url.URL :=
  { Scheme' := go!"http", Opaque' := [], User' := null, Host' := host, Path' := [], Fragment' := [],
    RawQuery' := [], RawPath' := [], RawFragment' := [], ForceQuery' := false, OmitHost' := false }

/-- **The deployment's initial cluster, as `bootstrap` reads it** (`BootURLs`): each member's name to its
one peer URL `http://peer` (of the first member of that name), the map `server.serverConfig` builds from the
deployment's members. `bootGo.ps` and `bootGo.ctxs` read only the map's keys and the URLs by name, not the
map's slices or the configuration's own peer and client URLs, which are left empty. -/
def distURLs (d : Deployment) : BootURLs where
  peer := []
  client := []
  initMap := GMap.ofList (d.members.map (fun m => (m.name, slice.nil)))
  initURLs := fun n => match d.members.find? (fun m => decide (m.name = n)) with
    | some m => [peerURL m.peer]
    | none => []

/-- **The peers, as Go computes them** (`bootGo.ps` at the deployment's initial cluster and token:
`NewClusterFromURLsMap`'s members' ids, in `MemberIDs()`' order, sorted). -/
def distPs (d : Deployment) : List w64 := bootGo.ps (distURLs d) d.token

/-- **The peers' contexts, as Go computes them** (`bootGo.ctxs`: `json.Marshal` of each member, in
`distPs`' order). -/
def distCtxs (d : Deployment) : List (List w8) := bootGo.ctxs (distURLs d) d.token

/-- **`bootstrap`'s bootstrap log, as Go computes it** (every example's `BootFacts`, for the one
cluster): `boot` is the node API's bootstrap log of Go's peers and contexts (`distPs d`, `distCtxs d`),
with `BootCore`'s facts of it. (2026-11-25: until then the peers `ps` and contexts `ctxs` were
quantified, with `ps` a permutation of the members' ids; `BootGoD.of_wf` derives that of a well-formed
deployment.) -/
abbrev BootFacts (d : Deployment) (boot : List LogEntry) : Prop :=
  BootCore (distPs d) (distCtxs d) boot

end boot

/-! ## The programs

Every machine's program receives the **whole deployment** as a Go value (`deploymentLit d`) and its own
index, and first checks the deployment (Go's `deployment.WellFormed`), returning at once if it fails
(rule: a premise the program can check is the program's, with a Go test that the check passes and the
real path runs: `TestWellFormed`, `TestDist`). So the statement has no premise on the deployment: on a
malformed one every machine stops after its check. -/

section programs
variable [GooseExts] [GoGlobalContext]

open github_com.mit_pdos.etcd_grove.examples.etcd.dist in
/-- **The deployment as a Go value**: the composite literal
`deployment.Deployment{Members: []deployment.Member{{Name: …, Peer: …, Client: …}, …}, Token: …,
Cfg: deployment.ServerCfg{…}, Workloads: []deployment.Workload{{Kind: …, Clients: …, Ops: …}, …},
Nodes: [][]string{{…}, …}}`, field for field `d`. -/
def deploymentLit (d : Deployment) : Expr :=
  let str (s : GoString) := ElementExpression go.string (Val #s)
  let lit (t : go.GoType) (es : List keyed_element) := App (Val (GoInstruction (CompositeLiteral t))) (LiteralValue es)
  let fld (n : GoString) (t : go.GoType) (e : Expr) := KeyedElement (some (KeyField n)) (ElementExpression t e)
  let memberE (m : Member) := KeyedElement none (ElementExpression deployment.Member.ty
    (lit deployment.Member.ty [fld go!"Name" go.string (Val #m.name), fld go!"Peer" go.string (Val #m.peer),
      fld go!"Client" go.string (Val #m.client)]))
  let workloadE (w : Workload) := KeyedElement none (ElementExpression deployment.Workload.ty
    (lit deployment.Workload.ty [fld go!"Kind" deployment.Kind.ty (Val #w.kind),
      fld go!"Clients" go.int (Val #w.clients), fld go!"Ops" go.int (Val #w.ops)]))
  let nodesE (ns : List GoString) := KeyedElement none (ElementExpression (go.GoType.SliceType go.string)
    (lit (go.GoType.SliceType go.string) (ns.map (fun n => KeyedElement none (str n)))))
  lit deployment.Deployment.ty
    [fld go!"Members" (go.GoType.SliceType deployment.Member.ty)
       (lit (go.GoType.SliceType deployment.Member.ty) (d.members.map memberE)),
     fld go!"Token" go.string (Val #d.token),
     fld go!"Cfg" deployment.ServerCfg.ty
       (lit deployment.ServerCfg.ty [fld go!"CompactorMode" go.string (Val #d.cfg.compactorMode),
         fld go!"Retention" go.int64 (Val #d.cfg.retention), fld go!"SnapCount" go.uint64 (Val #d.cfg.snapCount),
         fld go!"CatchUp" go.uint64 (Val #d.cfg.catchUp), fld go!"Auth" go.bool (Val #d.cfg.auth)]),
     fld go!"Workloads" (go.GoType.SliceType deployment.Workload.ty)
       (lit (go.GoType.SliceType deployment.Workload.ty) (d.workloads.map workloadE)),
     fld go!"Nodes" (go.GoType.SliceType (go.GoType.SliceType go.string))
       (lit (go.GoType.SliceType (go.GoType.SliceType go.string)) (d.nodes.map nodesE))]

variable [GoSemanticsFunctions]

open github_com.mit_pdos.etcd_grove.examples.etcd.dist in
/-- **Member `i`'s machine's boot program**: `server`'s initialization, then
`server.MainDeployment(d, i)` (`deployment.WellFormed(d)`, then `server.Main` of member `i`'s
configuration, `server.ConfigOf(d, i)`): the same expression at the first start and after every crash
(etcd's `NewServer` restarts from the WAL). -/
def serverProg (d : Deployment) (i : Nat) : Expr :=
  server.initialize' #() ;;
  App (App (Val (@! server.MainDeployment)) (deploymentLit d)) (Val #(W64 i))

open github_com.mit_pdos.etcd_grove.examples.etcd.dist in
/-- **Workload `j`'s orchestrator machine's boot program**: `client`'s initialization, then
`client.Orchestrator(d, j)` (`deployment.WellFormed(d)`, then `client.MainReady` of workload `j` with the
members' client addresses and the workload's client machines' addresses, D8). -/
def clientProg (d : Deployment) (j : Nat) : Expr :=
  client.initialize' #() ;;
  App (App (Val (@! client.Orchestrator)) (deploymentLit d)) (Val #(W64 j))

open github_com.mit_pdos.etcd_grove.examples.etcd.dist in
/-- **The `n`-th client machine's boot program** (in `nodeList`'s order): `client`'s initialization,
then `client.NodeDeployment(d, n)` (`deployment.WellFormed(d)`, then `client.NodeMain`: client machine
`c` of workload `w`, listening at its address, D8). -/
def nodeProg (d : Deployment) (n : Nat) : Expr :=
  client.initialize' #() ;;
  App (App (Val (@! client.NodeDeployment)) (deploymentLit d)) (Val #(W64 n))

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
here: every peer address is a member's peer handler); no lease expires, when a workload needs it. -/
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

/-! ## The bounds -/

/-- **The statements' thread bound** (`Robust`'s `threads`): the executions covered are those along which
every machine keeps fewer than `etcdThreads` live threads. It is the logic's thread bound on every machine
(`Net.robust_of_distBootILT`): at least the levels of a thread token a serving member uses (`srvLevelK =
5`), at most the `2 ^ 28` the server's and the clients' specs cap it by (their reader-slot pools and
`RWMutex` readers; `notes/etcd-dist-plan.md` §14). -/
def etcdThreads : Nat := 2 ^ 28

/-- **The statements' step bound** (`Robust`'s `bound`): the executions covered are those of fewer than
`etcdSteps` steps. It is the cap on the proofs' time receipts (`receiptBound ≤ 2 ^ 48`), the highest the
specs allow, for three lifetime counters of the Go code: etcd's request-id generator (`idutil`) issues
`prefix | (suffix mod 2 ^ 48)`, distinct only for fewer than `2 ^ 48` ids per generator; the mvcc store's
changes (revisions, compactions) are counted below `2 ^ 48`; and the auth store's admin requests, one
receipt each (its fuel), stay below `2 ^ 48`, which keeps its revision and its permissions within their
bounds (`auth/Fuel.lean`; `notes/etcd-dist-plan.md` §14). -/
def etcdSteps : Nat := 2 ^ 48

/-! ## The ghost state the statements' Iris premise is stated at -/

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp

open Iris Iris.BI Iris.ProgramLogic Iris.Std in
/-- **The functors** the proofs' ghost state is over (until 2026-11-25 also the statements' Iris premise
`HEnvTok`, now the pure `EtcdVerifyOff`): `putgetGF`'s layout (the
universal camera `AllG` at slot 0, invariants, later credits, GooseLang's heap, prophecies and package
state, a ghost variable at slot 7, and, since 2026-11-26, iris-lean's non-atomic invariants at slot 8
(`etcdDistGF_naInvG`, the instance porcupine's results take: the kv orchestrator's `kvremote.Orch`, M1); every
other slot the unit functor). -/
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
  | 8 => ⟨NaInvF, inferInstance⟩
  | _ => ⟨constOF Unit, inferInstance⟩

open Iris Iris.BI Iris.ProgramLogic Iris.Std in
/-- iris-lean's camera of non-atomic invariants, at slot 8: the instance porcupine's results take (the kv
orchestrator's `kvremote.Orch`, M1). -/
instance etcdDistGF_naInvG : NaInvG etcdDistGF := ⟨⟨8, rfl⟩⟩

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
