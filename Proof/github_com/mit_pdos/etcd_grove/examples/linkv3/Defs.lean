/-
Lean-first (no Rocq counterpart).

**linkv3's `Main` and `startMember`: their named premises and vocabulary** (D20, D21, 2026-10-19).
putget3's (`putget3/Defs.lean`, whose header explains each) at linkv3's configuration: the member
names `linkv3-1`, `-2`, `-3`, the cluster token `linkv3`, the peer addresses
`127.0.0.1:2382{1,2,3}` and the client addresses `127.0.0.1:2381{1,2,3}` (the first served). The
conf-change policy (`putget3.ccOk`), the URL builder (`putget3.httpURL`), the premises shared by
the members (`putget3.commonPremises`) are putget3's, which name no configuration.

**The member ids' order** (`BootFacts`): `id₁ id₂ id₃` are the ids of `linkv3-1`, `-2`, `-3`.
`bootstrap` sorts the members by id, and for linkv3's names and token the order is
`linkv3-2` (`0x3e1a…`), `linkv3-3` (`0xa5ec…`), `linkv3-1` (`0xd507…`) (`TestMemberIDs` in
`examples/linkv3/linkv3_test.go` prints them; their 16 low bits `0x99df`, `0xb926`, `0x725a` are
distinct and not `0`, D21e (A)). So the cluster's list (`ids`: the bootstrap log's order, one
conf change per member) is `[id₂, id₃, id₁]`, and `BootFacts` is putget3's in that order.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.putget3.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section pure
variable [ext : FfiSyntax]

/-- **The cluster's members in `bootstrap`'s order** (by id; see the file header). -/
def ids (id₁ id₂ id₃ : w64) : List w64 := [id₂, id₃, id₁]

/-- **`bootstrap`'s results, as Go computes them**: putget3's, in the members' id order (see the
file header). -/
abbrev BootFacts (id₁ id₂ id₃ : w64) (bootLog : List EntryM) : Prop :=
  putget3.BootFacts id₂ id₃ id₁ bootLog

/-- The members' names. -/
abbrev name₁ : GoString := go!"linkv3-1"
abbrev name₂ : GoString := go!"linkv3-2"
abbrev name₃ : GoString := go!"linkv3-3"

/-- The members' peer addresses (each member's one peer URL is `http://` of it). -/
abbrev peerAddr₁ : GoString := go!"127.0.0.1:23821"
abbrev peerAddr₂ : GoString := go!"127.0.0.1:23822"
abbrev peerAddr₃ : GoString := go!"127.0.0.1:23823"

/-- The members' client addresses (the first served, to the client). -/
abbrev clientAddr₁ : GoString := go!"127.0.0.1:23811"
abbrev clientAddr₂ : GoString := go!"127.0.0.1:23812"
abbrev clientAddr₃ : GoString := go!"127.0.0.1:23813"

/-- **The initial cluster's peer URLs, by name** (the map `Main` builds, `cluster`). -/
def initURLs3 (k : GoString) : List _root_.Perennial.net.url.URL :=
  if k = name₁ then [putget3.httpURL peerAddr₁] else if k = name₂ then [putget3.httpURL peerAddr₂]
  else if k = name₃ then [putget3.httpURL peerAddr₃] else []

/-- **The URLs of member `name`'s configuration** (putget3's `urlsOk` at linkv3's names). -/
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
`cfgOk` with the token `linkv3`). -/
def cfgOk (name : GoString) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : Prop :=
  cfg.Name' = name ∧ cfg.DataDir' = name ++ go!".etcd" ∧
    cfg.InitialClusterToken' = go!"linkv3" ∧ cfg.NewCluster' = true ∧
    cfg.TickMs' = W64 100 ∧ cfg.ElectionTicks' = W64 10

/-- **`bootstrap`'s contract for member `name`** (putget3's `bootPremise` at linkv3's `cfgOk` and
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

/-- **`Main`'s named premises** (persistent; putget3's at linkv3's configuration): `bootstrap`'s
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

end defs

end linkv3
end EtcdGrove
end Perennial
