/- Lean-first (no Rocq counterpart).

# `etcd/dist/server`: the vocabulary of the member machine's specs (N5, `notes/etcd-dist-plan.md` §19)

What `server.MainDeployment(d, i)`'s specs are stated over:
* the deployment's members as the start and `bootstrap` see them (`gmsD`, `cmsD`, `dirD`), and what `bootstrap`
  computes at each member's URLs (`BootGoD`: putgetK's `BootGoK` at the deployment's members, with the peers
  a permutation of the ids);
* the Go value of member `i`'s configuration (`configOf`, `configRepr`: `server.ConfigOf(d, i)`'s) and the
  `config.ServerConfig` `server.serverConfig` builds of it (`memberCfg`);
* **member `i`'s share of the cluster's start** (`memberShareD`): putgetK's `memberShareK` at the
  deployment's members (its client address at the cluster's view `c.view`), with every member's peer address
  set to etcd's peer protocols of the cluster (`peerAddrFactsAt`, `S5Interim.lean`'s `httpAddrAt`, indexed by
  the cluster: §19) in place of `S5Draft`'s unindexed fact, and the compactor's slot (`v3compactor.bootCfg`) at
  the cluster's compaction mode.
No proof here but pure lemmas.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.TopLevelDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.DeploymentDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Repr
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ClusterStart
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.MemberNames
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.S5Interim
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.BootDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.DirN
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.MembersDefs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.BootCfg

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Net go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcdstart
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

/-! ## The deployment's members -/

section pure
variable [GooseExts]

/-- A member as `etcdstart`'s `Member` (the name, the peer address, the client address). -/
def gmOf (m : Member) : GMember := ⟨m.name, m.peer, m.client⟩

/-- **The deployment's members** as `etcdstart`'s `Member`s, in its order. -/
def gmsD (d : Deployment) : List GMember := d.members.map gmOf

/-- **The deployment's members as the start sees them** (`ClusterMember`: peer address, client address, id). -/
def cmsD (d : Deployment) : List ClusterMember :=
  (d.members.zip d.ids).map (fun p => ⟨p.1.peer, p.1.client, p.2⟩)

/-- **The URL directory** of the deployment's cluster: the id of each member to its one peer URL
(`etcd_putgetN.dirN`, at the deployment's members and ids). -/
abbrev dirD (d : Deployment) : w64 → List GoString := etcd_putgetN.dirN (gmsD d) d.ids

/-- **What `bootstrap` computes at each member's URLs** (pure; putgetK's `BootGoK` at the deployment's
members, `BootDist.lean`'s `bootGoAt`), and the peers in `bootstrap`'s order a permutation of the members' ids
(putgetK's `BootLogFacts.perm`, which `BootFacts` does not carry): facts of the deployment (SHA-1 ids, the
bootstrap log's contexts) not yet evaluated in Lean, as `BootFacts`. -/
structure BootGoD (d : Deployment) (ps : List w64) (ctxs : List (List w8)) : Prop where
  perm : ps.Perm d.ids
  go : ∀ (m : GMember) (id : w64), (m, id) ∈ (gmsD d).zip d.ids →
    (id ≠ W64 18446744073709551615 ∧ id ≠ W64 18446744073709551614) ∧
    ∀ U, urlsN (gmsD d) m U → bootGoAt ps ctxs (dirD d) d.token m.Name' id U

/-- A member's entry of the initial cluster (`server.Peer`: its name, its peer address). -/
def peerOf (m : Member) : server.Peer := { Name' := m.name, Addr' := m.peer }

/-- **Member `m`'s configuration in the deployment `d`** (`server.ConfigOf(d, i)`'s value, its initial cluster
the slice `cl`). -/
def configOf (d : Deployment) (m : Member) (cl : GoSlice) : server.Config :=
  { Name' := m.name, Peer' := m.peer, Client' := m.client, Cluster' := cl, Token' := d.token,
    CompactorMode' := d.cfg.compactorMode, Retention' := d.cfg.retention, SnapCount' := d.cfg.snapCount,
    CatchUp' := d.cfg.catchUp, Auth' := d.cfg.auth }

/-- **The initial cluster's URLs by name, as `serverConfig` builds them** (from `server.Peer`s): a name to the
one peer URL `http://Addr` of its first entry, any other name to none. -/
def iuP (pl : List server.Peer) (n : GoString) : List _root_.Perennial.net.url.URL :=
  match pl.find? (fun p => decide (p.Name' = n)) with
  | some p => [httpURL p.Addr']
  | none => []

/-- `serverConfig`'s URLs by name, at the deployment's members, are `iuOf`'s. -/
theorem iuP_peerOf (d : Deployment) : iuP (d.members.map peerOf) = iuOf (gmsD d) := by
  funext n
  unfold iuP iuOf gmsD
  induction d.members with
  | nil => rfl
  | cons m ms ih =>
    simp only [List.map_cons, List.find?_cons]
    by_cases h : m.name = n
    · simp [peerOf, gmOf, h]
    · simp only [peerOf, gmOf, h, decide_false]
      exact ih

end pure

/-! ## The configuration's Go values -/

section values
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`cv` is member `i`'s configuration of the deployment `d`** (persistent): `configOf d m` of its member
`m`, its initial cluster's slice pointing read-only to every member's entry. -/
def configRepr (cv : server.Config) (d : Deployment) (i : Nat) : IProp GF :=
  iprop(∃ m : Member, ⌜d.members[i]? = some m ∧ cv = configOf d m cv.Cluster'⌝ ∗
    cv.Cluster' ↦*□ d.members.map peerOf)

instance configRepr_persistent (cv : server.Config) (d : Deployment) (i : Nat) :
    Persistent (configRepr (GF := GF) cv d i) := by
  unfold configRepr; infer_instance

/-- **The `config.ServerConfig` `serverConfig(c, lg)` returns** (`server.go`'s literal): `c`'s name, its data
directory and WAL directory under `etcdstart`'s bases, the initial cluster's map `cluster`, its peer and client
URL slices `pu`, `cu`, the token, a new cluster, raft's clock (`TickMs` 100, `ElectionTicks` 10), the snapshot
settings, etcd's default request limits (`MaxTxnOps` 128, `MaxRequestBytes` 1.5 MiB), the auto-compactor (its
mode `""` when the retention is `0`), the logger `lg`, the feature gate `fg`, and with `c.Auth` the simple token
provider with a TTL of 300 s; every other field zero. (Its form is the literal's as GooseLang evaluates it.) -/
def memberCfg (c : server.Config) (lg : Loc) (cluster : Loc) (pu cu : GoSlice) (fg : GoInterface) :
    go_etcd_io.etcd.server.v3.config.ServerConfig :=
  let base : go_etcd_io.etcd.server.v3.config.ServerConfig :=
    { (zeroValDef : go_etcd_io.etcd.server.v3.config.ServerConfig) with
      Name' := c.Name'
      DataDir' := go!"/tmp/etcd-grove-data/" ++ c.Name' ++ go!".etcd"
      DedicatedWALDir' := go!"/tmp/etcd-grove-wal/" ++ c.Name' ++ go!".etcd" ++ go!"/wal"
      InitialPeerURLsMap' := cluster
      PeerURLs' := pu
      ClientURLs' := cu
      InitialClusterToken' := c.Token'
      NewCluster' := true
      TickMs' := W64 100
      ElectionTicks' := W64 10
      SnapshotCount' := c.SnapCount'
      SnapshotCatchUpEntries' := c.CatchUp'
      MaxTxnOps' := W64 128
      MaxRequestBytes' := W64 1572864
      AutoCompactionMode' := if c.Retention' = W64 0 then go!"" else c.CompactorMode'
      AutoCompactionRetention' := c.Retention'
      Logger' := lg
      ServerFeatureGate' := fg }
  if c.Auth' then { base with AuthToken' := go!"simple", TokenTTL' := W64 300 } else base

end values

/-! ## Member `i`'s share of the cluster's start -/

section share
variable {GF : BundledGFunctors} [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
  [GoGlobalContext] [GoLocalContext] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
  [go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
  [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
  [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- **Every member's peer address set to etcd's peer protocols of the cluster of `γ`** (persistent;
`httpAddrAt γ m.id m.peer` for each start member `m`): `peerAddrFacts` at `S5Interim.lean`'s indexed fact. -/
def peerAddrFactsAt (γ : SrvRaft) (ms : List ClusterMember) : IProp GF :=
  iprop([∗list] m ∈ ms, httpAddrAt γ m.id m.peer)

instance peerAddrFactsAt_persistent (γ : SrvRaft) (ms : List ClusterMember) :
    Persistent (peerAddrFactsAt (GF := GF) γ ms) := by
  unfold peerAddrFactsAt; infer_instance

/-- **Member `i`'s share of the cluster's start** (of the deployment `d`, at the cluster's names `c`): the
names as the start chose them (`ClusterOk`, at the lease mode `lm`, the deployment's auth mode (#50 F7 S2 step 4),
and at a compaction mode `cmp` and retention
`cret` whose compactor slot the deployment's configuration meets), the cluster's facts, every member's peer address fact
(`peerAddrFactsAt`, of `c`'s cluster), member `i`'s slice, and its client address set to serve etcd's table for its
id at the cluster's view (`etcdAddrAt … c.view …`; O1 option B, `notes/etcd-dist-plan.md` §18.3, no publication),
and (#50 F7, L4) its lessor and auth names (`memberNamesShare` at `c.ls id`, `c.au id`), distinct per member
(`ClusterNames.NamesInj`). putgetK's `memberShareK` at the deployment's members. -/
def memberShareD (c : ClusterNames) (lm : lease.Mode) (d : Deployment) (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry) (i : Nat) : IProp GF :=
  iprop(∃ (cmp : Bool) (cret : Nat),
    ⌜ClusterOk c ps boot lm cmp cret d.ids d.cfg.auth ∧
      v3compactor.bootCfg d.cfg.compactorMode d.cfg.retention cmp cret ∧ c.NamesInj⌝ ∗
    clusterFactsOf c d.cfg.auth ∗ peerAddrFactsAt c.γ (cmsD d) ∗
    memberSliceOf c d.ids ps ctxs (LogEntry.toEntries boot 0) (d.ids.getD i (W64 0)) ∗
    etcdAddrAt ((d.members.getD i ⟨go!"", go!"", go!""⟩).client) (c.view d.cfg.auth) (d.ids.getD i (W64 0)) ∗
    memberNamesShare (c.ls (d.ids.getD i (W64 0))) (c.au (d.ids.getD i (W64 0))))

end share

end etcd_dist
end EtcdGrove
end Perennial

end
