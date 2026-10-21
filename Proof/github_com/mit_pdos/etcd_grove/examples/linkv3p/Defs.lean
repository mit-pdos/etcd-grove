/-
Lean-first (no Rocq counterpart).

**linkv3p's `Main`, `startMember`, `partitioner`, `Apply`, `Check`: their named premises and
vocabulary** (the partition plan's S3a, 2026-10-20, `notes/partition-plan.md`). putget3's
(`putget3/Defs.lean`, whose header explains each) at linkv3p's configuration: the member names
`linkv3p-1`, `-2`, `-3`, the cluster token `linkv3p`, the peer addresses `127.0.0.1:2384{1,2,3}`
and the client addresses `127.0.0.1:2383{1,2,3}` (every one served, to its client). The
conf-change policy (`putget3.ccOk`), the URL builder (`putget3.httpURL`), the premises shared by
the members (`putget3.commonPremises`) are putget3's, which name no configuration.

**The member ids' order** (`BootFacts`): `id₁ id₂ id₃` are the ids of `linkv3p-1`, `-2`, `-3`.
`bootstrap` sorts the members by id, and for linkv3p's names and token the order is the names'
(`0x77e2…`, `0xcc14…`, `0xecbe…`: `TestMemberIDs` in `examples/linkv3p/linkv3p_test.go` prints
them; their 16 low bits `0x2126`, `0x3ef6`, `0xf29c` are distinct and not `0`, D21e (A)), unlike
linkv3's. So the cluster's list (`ids`: the bootstrap log's order, one conf change per member) is
`[id₁, id₂, id₃]`, and `BootFacts` is putget3's in that order.

**What a started member gives** (`memberServed`) and **what a client's `Apply` takes**
(`clientOk`) are at the end.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.putget3.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3p.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Inv
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftHandler

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section pure
variable [ext : FfiSyntax]

/-- **The cluster's members in `bootstrap`'s order** (by id; see the file header). -/
def ids (id₁ id₂ id₃ : w64) : List w64 := [id₁, id₂, id₃]

/-- **`bootstrap`'s results, as Go computes them**: putget3's, in the members' id order (see the
file header). -/
abbrev BootFacts (id₁ id₂ id₃ : w64) (bootLog : List EntryM) : Prop :=
  putget3.BootFacts id₁ id₂ id₃ bootLog

/-- The members' names. -/
abbrev name₁ : GoString := go!"linkv3p-1"
abbrev name₂ : GoString := go!"linkv3p-2"
abbrev name₃ : GoString := go!"linkv3p-3"

/-- The members' peer addresses (each member's one peer URL is `http://` of it). -/
abbrev peerAddr₁ : GoString := go!"127.0.0.1:23841"
abbrev peerAddr₂ : GoString := go!"127.0.0.1:23842"
abbrev peerAddr₃ : GoString := go!"127.0.0.1:23843"

/-- The members' client addresses (each served, to its client). -/
abbrev clientAddr₁ : GoString := go!"127.0.0.1:23831"
abbrev clientAddr₂ : GoString := go!"127.0.0.1:23832"
abbrev clientAddr₃ : GoString := go!"127.0.0.1:23833"

/-- **The initial cluster's peer URLs, by name** (the map `Main` builds, `cluster`). -/
def initURLs3 (k : GoString) : List _root_.Perennial.net.url.URL :=
  if k = name₁ then [putget3.httpURL peerAddr₁] else if k = name₂ then [putget3.httpURL peerAddr₂]
  else if k = name₃ then [putget3.httpURL peerAddr₃] else []

/-- **The URLs of member `name`'s configuration** (putget3's `urlsOk` at linkv3p's names). -/
def urlsOk (peerAddr client : GoString) (U : BootURLs) : Prop :=
  U.peer = [putget3.httpURL peerAddr] ∧ U.client = [putget3.httpURL client] ∧
    (∃ sl₁ sl₂ sl₃ : GoSlice,
      U.initMap = GMap.insert name₃ sl₃ (GMap.insert name₂ sl₂ (GMap.insert name₁ sl₁ ∅))) ∧
    U.initURLs = initURLs3

/-- **The peer-URL directory of `Main`'s cluster** (D21 M2): each member's one peer URL. -/
def dir3 (id₁ id₂ id₃ : w64) (id : w64) : List GoString :=
  if id = id₁ then [go!"http://" ++ peerAddr₁] else if id = id₂ then [go!"http://" ++ peerAddr₂]
  else if id = id₃ then [go!"http://" ++ peerAddr₃] else []

end pure

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The configuration `startMember` passes to `NewServer`**, by its scalar fields (putget3's
`cfgOk` with the token `linkv3p`). -/
def cfgOk (name : GoString) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : Prop :=
  cfg.Name' = name ∧ cfg.DataDir' = name ++ go!".etcd" ∧
    cfg.InitialClusterToken' = go!"linkv3p" ∧ cfg.NewCluster' = true ∧
    cfg.TickMs' = W64 100 ∧ cfg.ElectionTicks' = W64 10

/-- **`bootstrap`'s contract for member `name`** (putget3's `bootPremise` at linkv3p's `cfgOk` and
`urlsOk`). -/
def bootPremise (N : Nat) (ps : List w64) (bootLog : List EntryM) (dir : w64 → List GoString)
    (name peerAddr client : GoString) (id : w64) : IProp GF :=
  iprop(□ ∀ (reg : GName) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
        (γ : RaftNames),
      ⌜cfgOk name cfg ∧ urlsOk peerAddr client U ∧ γ.reCfg = GMap.listToSet ps ∧
        γ.reDyn = none ∧ γ.reCCOk = putget3.ccOk ps ∧ γ.reBoot = bootLog ∧ γ.reNoSnap = true⌝ -∗
      letI : MemStorReg GF := ⟨reg⟩; bootstrapContract cfg U γ id bootLog N dir)

instance bootPremise_persistent (N : Nat) (ps : List w64) (bootLog : List EntryM)
    (dir : w64 → List GoString) (name peerAddr client : GoString) (id : w64) :
    Persistent (bootPremise (GF := GF) N ps bootLog dir name peerAddr client id) := by
  unfold bootPremise; infer_instance

/-- **`Main`'s named premises** (persistent; putget3's at linkv3p's configuration): `bootstrap`'s
contract for each member, at the cluster `ids id₁ id₂ id₃` and the directory `dir3`, and the
premises the members share. -/
def premises (N : Nat) (id₁ id₂ id₃ : w64) (bootLog : List EntryM) : IProp GF :=
  iprop(
    bootPremise N (ids id₁ id₂ id₃) bootLog (dir3 id₁ id₂ id₃) name₁ peerAddr₁ clientAddr₁ id₁ ∗
    bootPremise N (ids id₁ id₂ id₃) bootLog (dir3 id₁ id₂ id₃) name₂ peerAddr₂ clientAddr₂ id₂ ∗
    bootPremise N (ids id₁ id₂ id₃) bootLog (dir3 id₁ id₂ id₃) name₃ peerAddr₃ clientAddr₃ id₃ ∗
    putget3.commonPremises)

instance premises_persistent (N : Nat) (id₁ id₂ id₃ : w64) (bootLog : List EntryM) :
    Persistent (premises (GF := GF) N id₁ id₂ id₃ bootLog) := by
  unfold premises; infer_instance

/-- **What `Apply` and `Check` take of one client** (persistent): linkvtxn's `Apply.spec`'s
premises for a client `cl` of some member -- `New`'s one-attempt client (`isNewClient`,
`clientKVOnce`), etcd's `Put`, `Range`, `DeleteRange` and `Txn` registered at its endpoint with that
member's apply environment, read names and ids, and the instance's invariant at the member's KV
names (the cluster's state, D21 M4: `linkvInv_congr`, `Alloc.lean`). A list of clients is a
`[∗list]` of these. (Until 2026-10-20, linkv's: `Put` and `Range`, linkv's invariant.) -/
def clientOk (γ : linkvtxn.LinkvNames) (cl : Loc) : IProp GF :=
  iprop(∃ (ep : GoString) (V : EtcdGrove.client.WEnv GF) (E : apply.AEnv GF) (γr : ReadNames)
      (cid mid : w64),
    isNewClient cl ep V ∗ clientKVOnce cl ep ∗
    isGrpcRpc ep go!"/etcdserverpb.KV/Put" (EtcdGrove.client.etcdPutSpec E γr cid mid) ∗
    isGrpcRpc ep go!"/etcdserverpb.KV/Range" (EtcdGrove.client.etcdRangeSpec E γr cid mid) ∗
    isGrpcRpc ep go!"/etcdserverpb.KV/DeleteRange" (EtcdGrove.client.etcdDeleteSpec E γr cid mid) ∗
    isGrpcRpc ep go!"/etcdserverpb.KV/Txn" (EtcdGrove.client.etcdTxnSpec E γr γr cid mid) ∗
    linkvtxn.linkvInv γ γr.kv)

instance clientOk_persistent (γ : linkvtxn.LinkvNames) (cl : Loc) :
    Persistent (clientOk (GF := GF) γ cl) := by
  unfold clientOk; infer_instance

/-- **A member started and served** (the success of `startMember`): putget3's `memberUp` reduced
to what `Main` needs of it -- the server's request and read views (at its apply environment `E`,
agreeing with the stand-in `E₀`, auth off), the `GoAttach` resources with the thread token
(`srvGoRes`), the member's place in the network (`srvNetMember`: what the partitioner's
`CutPeer`/`MendPeer` take), and etcd's `Put`, `Range`, `DeleteRange` and `Txn` registered at its
client address (`etcd_kv_started`), what its client's `Apply` takes. -/
def memberServed (γn : NetNames GF) (s : Loc) (id : w64) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (client : GoString) : IProp GF :=
  iprop(∃ (E : apply.AEnv GF) (γw : GName) (cid mid : w64),
    ⌜envAgree E E₀ ∧ E.authOn = false⌝ ∗
    isServerReq s E { ρ with wait := γw } ∗ isServerRead s E ρ.rd ∗ srvGoRes s ∗
    srvNetMember γn s id ∗
    isGrpcRpc client go!"/etcdserverpb.KV/Put" (EtcdGrove.client.etcdPutSpec E ρ.rd cid mid) ∗
    isGrpcRpc client go!"/etcdserverpb.KV/Range" (EtcdGrove.client.etcdRangeSpec E ρ.rd cid mid) ∗
    isGrpcRpc client go!"/etcdserverpb.KV/DeleteRange"
      (EtcdGrove.client.etcdDeleteSpec E ρ.rd cid mid) ∗
    isGrpcRpc client go!"/etcdserverpb.KV/Txn" (EtcdGrove.client.etcdTxnSpec E ρ.rd ρ.rd cid mid))

end defs

end linkv3p
end EtcdGrove
end Perennial
