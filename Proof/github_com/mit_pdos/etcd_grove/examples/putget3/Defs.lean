/-
**putget3's `Main` and `startMember`: their named premises and vocabulary** (D21 stage M5,
2026-10-19). Lean-first (no Rocq counterpart). putget's (`examples/putget`, `putget/Defs.lean`) for
the three members of `examples/putget3/putget3.go`.

**The pure facts** (`BootFacts`): `bootstrap`'s results for the three configurations, as Go
computes them: the member ids `id₁ id₂ id₃` (etcd's, from the peer URLs and the cluster token
`putget3`; `TestMemberIDs` in `putget3_test.go` prints them), their 16 low bits distinct and not `0`
(D21e (A): the request ids' prefixes), the peers in that order (`bootstrap` sorts the member ids:
`0x4594…`, `0x615e…`, `0xecbf…`, the members `putget3-1`, `-2`, `-3`), and the bootstrap log with
the peers' contexts (the node API's `BootLog`), one conf change adding each member, each of id `0`
and one the server's `applyConfChange` takes.

**The Iris premises** (`premises`, persistent; each a triple of a function the program calls, as
putget's, D19a's second kind):
* `bootstrap`'s contract for each member (`bootPremise`), at every server raft names of the
  three-member cluster (its peers, static, the bootstrap log), at the peers' contexts, for a configuration with the scalar fields `startMember`
  sets (`cfgOk`) and the member's URLs (`urlsOk`), at the URL directory `dir3` (each member's one
  peer URL, the records `bootstrap` makes name it);
* `proto.Marshal`'s contract at the bootstrap log's conf changes (`bootMarshal`, 2026-10-27);
* putget's others: the raft wrapper's trust-boundary contracts (2026-10-30: no `rnStopOkStarted`),
  `v3rpc.runsNoRequireLeader`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.NewServer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Start
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatch
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvStreamInterceptor
public import Proof.github_com.mit_pdos.etcd_grove.examples.putget3.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvGrpcStart
public import Proof.net.InvNet

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace putget3

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **`bootstrap`'s results, as Go computes them** (pure facts of the program; see the file
header). (2026-10-27, the server port: the bootstrap log `bl` with the peers' contexts `ctxs` the
node API's `BootLog`, each entry a conf change of id `0` that the server's `applyConfChange` takes;
until then `srvBootLogOk (ccOk [id₁, id₂, id₃]) [id₁, id₂, id₃] bootLog`, under the conf-change
policy `ccOk`, over raft's records.) -/
structure BootFacts (id₁ id₂ id₃ : w64) (ctxs : List (List w8)) (bl : List LogEntry) :
    Prop where
  idLow : ([id₁, id₂, id₃].map (fun id => uint.Z id % 2 ^ 16)).Nodup
  idLow0 : ∀ id ∈ [id₁, id₂, id₃], uint.Z id % 2 ^ 16 ≠ 0
  boot : BootLog [id₁, id₂, id₃] ctxs bl
  cc : ∀ e ∈ LogEntry.toEntries bl 0,
    ccIdOf e.Data' = W64 0 ∧ ccBootOk (GMap.listToSet [id₁, id₂, id₃]) e.Data'

/-- A URL `http://<host>`. -/
def httpURL (host : GoString) : _root_.Perennial.net.url.URL :=
  { Scheme' := go!"http", Opaque' := [], User' := null, Host' := host, Path' := [], Fragment' := [],
    RawQuery' := [], RawPath' := [], RawFragment' := [], ForceQuery' := false, OmitHost' := false }

/-- The members' names. -/
abbrev name₁ : GoString := go!"putget3-1"
abbrev name₂ : GoString := go!"putget3-2"
abbrev name₃ : GoString := go!"putget3-3"

/-- The members' peer addresses (each member's one peer URL is `http://` of it). -/
abbrev peerAddr₁ : GoString := go!"127.0.0.1:23801"
abbrev peerAddr₂ : GoString := go!"127.0.0.1:23802"
abbrev peerAddr₃ : GoString := go!"127.0.0.1:23803"

/-- The members' client addresses (the first served, to the client). -/
abbrev clientAddr₁ : GoString := go!"127.0.0.1:23791"
abbrev clientAddr₂ : GoString := go!"127.0.0.1:23792"
abbrev clientAddr₃ : GoString := go!"127.0.0.1:23793"

/-- **The initial cluster's peer URLs, by name** (the map `Main` builds, `cluster`). -/
def initURLs3 (k : GoString) : List _root_.Perennial.net.url.URL :=
  if k = name₁ then [httpURL peerAddr₁] else if k = name₂ then [httpURL peerAddr₂]
  else if k = name₃ then [httpURL peerAddr₃] else []

/-- **The URLs of member `name`'s configuration** (D19r (F), putget's at three members): its peer
URLs `[http://peerAddr]`, its client URLs `[http://client]`, the initial cluster's map (`Main`'s
`cluster`: the three members' names to their peer URL slices) and its URLs by name `initURLs3`. -/
def urlsOk (peerAddr client : GoString) (U : BootURLs) : Prop :=
  U.peer = [httpURL peerAddr] ∧ U.client = [httpURL client] ∧
    (∃ sl₁ sl₂ sl₃ : GoSlice,
      U.initMap = GMap.insert name₃ sl₃ (GMap.insert name₂ sl₂ (GMap.insert name₁ sl₁ ∅))) ∧
    U.initURLs = initURLs3

/-- **The peer-URL directory of `Main`'s cluster** (D21 M2): each member's one peer URL. -/
def dir3 (id₁ id₂ id₃ : w64) (id : w64) : List GoString :=
  if id = id₁ then [go!"http://" ++ peerAddr₁] else if id = id₂ then [go!"http://" ++ peerAddr₂]
  else if id = id₃ then [go!"http://" ++ peerAddr₃] else []

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The configuration `startMember` passes to `NewServer`**, by its scalar fields (putget's
`cfgOk` at the member's name): member `name` of a new cluster with token `putget3`, data directory
`name.etcd`, raft's clock `100` ms and `10` ticks. -/
def cfgOk (name : GoString) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : Prop :=
  cfg.Name' = name ∧ cfg.DataDir' = name ++ go!".etcd" ∧
    cfg.InitialClusterToken' = go!"putget3" ∧ cfg.NewCluster' = true ∧
    cfg.TickMs' = W64 100 ∧ cfg.ElectionTicks' = W64 10

/-- **`bootstrap`'s contract for member `name`** (id `id`, its addresses `peerAddr`, `client`), at
every server raft names of the cluster `ps` (its peers, static, the bootstrap log; at the storage
registry they name; 2026-10-27, the server port: until then raft's names, with raft's no-snapshot
and no-transfer modes and the policy `ccOk ps`), for its configuration and URLs (the initial
cluster's map `Main`'s), at the peers' contexts `ctxs`, the bound `N` and the directory `dir`. -/
def bootPremise (N : Nat) (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8))
    (dir : w64 → List GoString) (name peerAddr client : GoString) (id : w64) : IProp GF :=
  iprop(□ ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft),
      ⌜cfgOk name cfg ∧ urlsOk peerAddr client U ∧ γ.vs = ps ∧ γ.rule = srvRule (W64 0) bootLog ∧
        γ.boot = bootLog⌝ -∗
      letI : MemStorReg GF := ⟨γ.reg⟩; bootstrapContract cfg U γ id ctxs N dir)

instance bootPremise_persistent (N : Nat) (ps : List w64) (bootLog : List EntryM)
    (ctxs : List (List w8)) (dir : w64 → List GoString) (name peerAddr client : GoString)
    (id : w64) :
    Persistent (bootPremise (GF := GF) N ps bootLog ctxs dir name peerAddr client id) := by
  unfold bootPremise; infer_instance

/-- **The premises shared by the members** (putget's, but `bootstrap`'s contract): the raft
wrapper's trust-boundary contracts and the deployment's
`runsNoRequireLeader`. -/
def commonPremises : IProp GF :=
  iprop(rnLoggerZapOk ∗ rnSetLoggerOk ∗ rnTimeoutDetectorOk ∗ rnNewStorageOk ∗
    (□ ∀ E : RNEnv GF, ⌜E.T = iprop(True)⌝ -∗ rnTickerOk E) ∗
    v3rpc.runsNoRequireLeader)

instance commonPremises_persistent : Persistent (commonPremises (GF := GF)) := by
  unfold commonPremises; infer_instance

/-- **`Main`'s named premises** (persistent; see the file header), at the bound `N` of each
member's apply thread's write tokens, the member ids, the peers' contexts and the bootstrap log;
(2026-10-27, the server port) with `proto.Marshal`'s contract at the bootstrap log's conf changes
(`bootMarshal`, which the cluster's allocation takes; until then `bootstrap`'s contract gave it). -/
def premises (N : Nat) (id₁ id₂ id₃ : w64) (ctxs : List (List w8)) (boot : List LogEntry) :
    IProp GF :=
  iprop(
    bootPremise N [id₁, id₂, id₃] (LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃)
      name₁ peerAddr₁ clientAddr₁ id₁ ∗
    bootPremise N [id₁, id₂, id₃] (LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃)
      name₂ peerAddr₂ clientAddr₂ id₂ ∗
    bootPremise N [id₁, id₂, id₃] (LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃)
      name₃ peerAddr₃ clientAddr₃ id₃ ∗
    bootMarshal [id₁, id₂, id₃] ctxs (LogEntry.toEntries boot 0) ∗
    commonPremises)

instance premises_persistent (N : Nat) (id₁ id₂ id₃ : w64) (ctxs : List (List w8))
    (boot : List LogEntry) :
    Persistent (premises (GF := GF) N id₁ id₂ id₃ ctxs boot) := by
  unfold premises; infer_instance

end defs

end putget3
end EtcdGrove
end Perennial
