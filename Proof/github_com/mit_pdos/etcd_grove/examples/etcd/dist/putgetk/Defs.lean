/- Lean-first (no Rocq counterpart).

# `etcd/dist/putgetk`: the members' vocabulary (plan item 4, `notes/putget-dist-plan.md` §13)

What `Member.spec` (`Spec/.../examples/etcd/dist/putgetk/Member.lean`) is written in, beside the cluster's
start (`etcd_dist.etcdClusterStart`, `dist/ClusterStart.lean`) and the in-process `putgetN`'s audited
per-member premises (`etcdstart.bootPremise` at `etcd_putgetN.dirN` and `etcdstart.urlsN`; since 2026-11-25
`BootGoK`, the pure facts `bootstrap`'s interim axiom asks of them):
* `nameOf j`: member `j`'s name as `putgetk.Name(j)` computes it;
* `cmsOf ms ids`: the start's members (`etcd_dist.ClusterMember`: peer address, client address, member id)
  from the deployment's members and their ids, in the members' order;
* `memberShareK`: member `i`'s share of the cluster's start (its client address at the cluster's view,
  `c.view`: O1 option B, `notes/etcd-dist-plan.md` §18.3; until 2026-11-25 also a publication obligation).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ClusterStart
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Base
public import Perennial.Proof.crypto.sha1.Fips180
public import Proof.go_etcd_io.raft.v3.BootMarshal
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.BootDist

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_putgetk_dist

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3 etcdstart

/-- **Member `j`'s name**, as `putgetk.Name(j)` computes it: `"putgetk-"` and `j` in decimal. -/
def nameOf [GooseExts] (j : Nat) : GoString := go!"putgetk-" ++ fmtUint (W64 j) (W64 10)

/-- **The start's members** (`etcd_dist.ClusterMember`) of the deployment's members `ms` with the ids `ids`,
in the members' order. -/
def cmsOf [GooseExts] (ms : List GMember) (ids : List w64) : List etcd_dist.ClusterMember :=
  (ms.zip ids).map (fun p => ⟨p.1.Peer', p.1.Client', p.2⟩)

/-! ## The configuration -/

section config
variable [GooseExts]

/-- The cluster's token (`putgetk.Token`). -/
abbrev token : GoString := go!"putgetk"

/-- **The members** of the configuration (Go's `etcdstart.Member` values), one per peer address: member
`j` named `nameOf j` (`putgetk.Name(j)`), its peer address `peers[j]`, its client address `clients[j]`
(`""` if `clients` is shorter: such a configuration is not `cfgOk`, and `Member` returns at once). -/
def membersOf (peers clients : List GoString) : List GMember :=
  peers.mapIdx (fun j p => ⟨nameOf j, p, clients.getD j go!""⟩)

/-- **etcd's id of the member whose one peer URL is `http://peer`** in the cluster `token`
(`membership.NewMember`'s `computeMemberID` for one URL and no time): the first 8 bytes, big-endian, of
the SHA-1 (Perennial's `crypto.sha1.sha1`, FIPS 180-4) of the URL followed by the token. `putgetk.MemberID`
computes it (proved); `TestMemberIDEtcd` checks it against etcd's own over 3000 random configurations. -/
def memberIdOf (peer : GoString) : w64 :=
  W64 (((crypto.sha1.sha1 (go!"http://" ++ peer ++ token)).take 8).foldl
    (fun acc b => acc * 256 + b.toNat) 0)

/-- The members' ids, in the members' order. -/
def idsOf (peers : List GoString) : List w64 := peers.map memberIdOf

/-- **The ids are what etcd needs** (`putgetk.Valid`'s check on them, `BootCore`'s `lowNodup`, `lowNz`):
their 16 low bits distinct and not `0`. -/
def idsOk (ids : List w64) : Prop :=
  (ids.map (fun id => uint.Z id % 2 ^ 16)).Nodup ∧ ∀ id ∈ ids, uint.Z id % 2 ^ 16 ≠ 0

/-- **The configuration's addresses**: every member's peer address, then every member's client address. -/
def addrs (peers clients : List GoString) : List GoString := peers ++ clients

end config

/-- **`bootstrap`'s log, as etcd computes it** for the members' ids `ids` (`BootCore` but its two facts on
the ids, which the program checks, `idsOk`): the peers `ps` in `bootstrap`'s order, a permutation of the
ids (the in-process `putgetN`'s `BootFacts.perm`), their contexts `ctxs` and the bootstrap log `bl`: one
conf change per peer (`BootLog`), its changes' bytes and URLs as `bootstrap` writes them, the log's one
bound. What `bootstrap` produces for any configuration, not a condition on the configuration; it moves into
`bootstrap`'s contract when the named premises are converted (the survey of 2026-11-24). -/
structure BootLogFacts [GooseExts] (ids ps : List w64) (ctxs : List (List w8)) (bl : List LogEntry) :
    Prop where
  boot : BootLog ps ctxs bl
  cc : ∀ e ∈ LogEntry.toEntries bl 0,
    ccIdOf e.Data' = W64 0 ∧ ccBootOk (GMap.listToSet ps) e.Data'
  urls : bootURLsOk (LogEntry.toEntries bl 0)
  data : bootDataOk bl
  perm : ps.Perm ids
  /-- (etcd-safe-main, 2026-11-25: hprem-axioms' swap, as `BootCore.wire`) the boot entries' bytes are
  `proto.Marshal`'s of the boot conf changes (`bootWire`), in place of the premise `bootMarshal` -/
  wire : bootWire ps ctxs bl

/-- **The configuration is one the program runs** (what `putgetk.Valid` returning `true` implies; the
start's case split): a member, one client address per peer address, the ids `idsOk`. -/
def cfgOk [GooseExts] (peers clients : List GoString) : Prop :=
  peers ≠ [] ∧ peers.length = clients.length ∧ idsOk (idsOf peers)

/-! ## The members' named premises -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **What `bootstrap` computes at each member's URLs** (pure; 2026-11-25, in place of the members' named
premises `premises`, every member's `bootstrap` contract `etcdstart.bootPremise`, now derived from the interim
axiom `bootstrap.wp_proof_dist`): for every member `m` of the configuration with its id `id`, the id is not one
of raft's local targets, and at every URLs the member's configuration names (`urlsN`) the peers `ps`, contexts
`ctxs`, the directory `dirN` and `id` are Go's (`bootGo.*` at the token), the URLs and names plain, and the
initial cluster is `etcd_safe`'s shape: one peer URL per member, **at most 64 members** (`etcd_dist.bootGoAt`).
Facts of the configuration (SHA-1 ids, the boot log's contexts) not yet evaluated in Lean. -/
def BootGoK (peers clients : List GoString) (ps : List w64) (ctxs : List (List w8)) : Prop :=
  ∀ (m : GMember) (id : w64), (m, id) ∈ (membersOf peers clients).zip (idsOf peers) →
    (id ≠ W64 18446744073709551615 ∧ id ≠ W64 18446744073709551614) ∧
    ∀ U, urlsN (membersOf peers clients) m U →
      etcd_dist.bootGoAt ps ctxs (etcd_putgetN.dirN (membersOf peers clients) (idsOf peers)) token m.Name'
        id U

end defs

/-! ## Member `i`'s share of the start -/

section shareK
open Net
variable {GF : BundledGFunctors} [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
  [GoGlobalContext] [GoLocalContext] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
  [go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
  [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
  [G : GooseGlobalGS .hasLC GF] [π : Net.NetProtoGS]

/-- **Member `i`'s share of the cluster's start** (when the configuration is `cfgOk`; `etcdClusterStart`'s,
at S5's names `S5` and the cluster's names `c`): the names as the start chose them (`ClusterOk`, lease mode
`none`, no compaction), the addresses distinct and valid (`DistDeploy`'s), its `memberStartShare` (of the
configuration's members `cmsOf (membersOf peers clients) (idsOf peers)`): its client address set at the
cluster's view. -/
def memberShareK (S5 : etcd_dist.S5Draft GF) (c : etcd_dist.ClusterNames) (peers clients : List GoString)
    (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry) (i : Nat) : IProp GF :=
  iprop(⌜etcd_dist.ClusterOk c ps boot .none false 0 (idsOf peers) ∧ (addrs peers clients).Nodup ∧
      ∀ a ∈ addrs peers clients, Net.addrOk a = true⌝ ∗
    etcd_dist.memberStartShare S5 c (cmsOf (membersOf peers clients) (idsOf peers)) ps ctxs
      (LogEntry.toEntries boot 0)
      ((cmsOf (membersOf peers clients) (idsOf peers)).getD i ⟨go!"", go!"", W64 0⟩))

end shareK

end etcd_putgetk_dist
end EtcdGrove
end Perennial

end
