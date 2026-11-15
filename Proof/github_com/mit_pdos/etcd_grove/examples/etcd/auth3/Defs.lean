/-
**auth3's `Main` and `startMember`: their named premises and vocabulary** (the auth3 Scope's A1,
`notes/auth3-scope.md`, 2026-11-14). Lean-first (no Rocq counterpart). putget3's
(`putget3/Defs.lean`) for the three members of `examples/etcd/auth3/auth3.go`, with authkv's
configuration (`auth/Defs.lean`: the simple token provider).

**The pure facts** (putget3's `BootFacts`, reused): `bootstrap`'s results for the three
configurations, as Go computes them: the member ids `id₁ id₂ id₃` of the members `auth3-1`, `-2`,
`-3` (etcd's, from the peer URLs and the cluster token `auth3`; `TestMemberIDs` in `auth3_test.go`
prints them), their 16 low bits distinct and not `0`, the peers `ps` in `bootstrap`'s order, a
permutation of the ids, and the bootstrap log with the peers' contexts.

**The Iris premises** (`premises`, persistent; putget3's at auth3's configuration):
* `bootstrap`'s contract for each member (`bootPremise`), at every server raft names of the
  three-member cluster, for a configuration with the scalar fields `startMember` sets (`cfgOk`:
  putget3's at the token `auth3`, and the simple token provider, as authkv's) and the member's URLs
  (`urlsOk`), at the URL directory `dir3`;
* `proto.Marshal`'s contract at the bootstrap log's conf changes (`bootMarshal`);
* the raft wrapper's trust-boundary contracts (`etcdstart.commonPremises`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putget3.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_auth3

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- The members' names. -/
abbrev name₁ : GoString := go!"auth3-1"
abbrev name₂ : GoString := go!"auth3-2"
abbrev name₃ : GoString := go!"auth3-3"

/-- The members' peer addresses (each member's one peer URL is `http://` of it). -/
abbrev peerAddr₁ : GoString := go!"127.0.0.1:24131"
abbrev peerAddr₂ : GoString := go!"127.0.0.1:24132"
abbrev peerAddr₃ : GoString := go!"127.0.0.1:24133"

/-- The members' client addresses (the first served, to every client). -/
abbrev clientAddr₁ : GoString := go!"127.0.0.1:24141"
abbrev clientAddr₂ : GoString := go!"127.0.0.1:24142"
abbrev clientAddr₃ : GoString := go!"127.0.0.1:24143"

/-- **The initial cluster's peer URLs, by name** (the map `Main` builds, `cluster`). -/
def initURLs3 (k : GoString) : List _root_.Perennial.net.url.URL :=
  if k = name₁ then [etcdstart.httpURL peerAddr₁] else if k = name₂ then [etcdstart.httpURL peerAddr₂]
  else if k = name₃ then [etcdstart.httpURL peerAddr₃] else []

/-- **The URLs of member `name`'s configuration**: its peer URLs `[http://peerAddr]`, its client
URLs `[http://client]`, the initial cluster's map (`Main`'s `cluster`) and its URLs by name. -/
def urlsOk (peerAddr client : GoString) (U : BootURLs) : Prop :=
  etcdstart.urls3 name₁ name₂ name₃ initURLs3 peerAddr client U

/-- **The peer-URL directory of `Main`'s cluster**: each member's one peer URL. -/
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

/-- **The configuration `startMember` passes to `NewServer`**, by its scalar fields: member `name`
of a new cluster with token `auth3`, data directory `name.etcd`, raft's clock `100` ms and `10`
ticks, and the simple token provider (authkv's `cfgOk` at the member's name). -/
def cfgOk (name : GoString) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : Prop :=
  cfg.Name' = name ∧ cfg.DataDir' = name ++ go!".etcd" ∧
    cfg.InitialClusterToken' = go!"auth3" ∧ cfg.NewCluster' = true ∧
    cfg.TickMs' = W64 100 ∧ cfg.ElectionTicks' = W64 10 ∧ cfg.AuthToken' = go!"simple"

/-- **`bootstrap`'s contract for member `name`** (id `id`, its addresses `peerAddr`, `client`), at
every server raft names of the cluster `ps`, for its configuration and URLs, at the peers'
contexts `ctxs`, the bound `N` and the directory `dir` (putget3's `bootPremise` at auth3's
`cfgOk`). -/
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

/-- **`Main`'s named premises** (persistent; see the file header). -/
def premises (N : Nat) (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry) : IProp GF :=
  iprop(
    bootPremise N ps (LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃)
      name₁ peerAddr₁ clientAddr₁ id₁ ∗
    bootPremise N ps (LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃)
      name₂ peerAddr₂ clientAddr₂ id₂ ∗
    bootPremise N ps (LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃)
      name₃ peerAddr₃ clientAddr₃ id₃ ∗
    bootMarshal ps ctxs (LogEntry.toEntries boot 0) ∗
    etcdstart.commonPremises)

instance premises_persistent (N : Nat) (id₁ id₂ id₃ : w64) (ps : List w64)
    (ctxs : List (List w8)) (boot : List LogEntry) :
    Persistent (premises (GF := GF) N id₁ id₂ id₃ ps ctxs boot) := by
  unfold premises; infer_instance

end defs

end etcd_auth3
end EtcdGrove
end Perennial
