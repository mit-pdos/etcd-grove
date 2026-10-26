/-
**authkv's vocabulary** (the auth plan's E2b, 2026-10-25; `notes/decisions.md`, "E2b of the auth
plan"). Lean-first (no Rocq counterpart).

* The configuration `Main` starts its member with: watchkv's (`watchkv/Defs.lean`, whose header
  points at putget's for each premise) at authkv's names and ports, with the simple token provider
  (`AuthToken` `simple`): `cfgOk` (member and token `authkv`, data directory `authkv.etcd`),
  `urlsOk` (peer URL `http://127.0.0.1:23926`, client URL `http://127.0.0.1:23916`), the peer
  directory `akDir`, and `premises`: putget's at these.
* The program's auth state and verdicts: `Model.lean`.

`Main`'s proof is not done (`Main.lean`), so these premises are those of the server's start as
watchkv states them; the proof may need others (an auth-enabled server's, after E2a: the client's
auth contract, `ClientAuth.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Model
public import Proof.github_com.mit_pdos.etcd_grove.examples.putget.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section pure
variable [ext : FfiSyntax]

/-- `Main`'s peer URL, `http://127.0.0.1:23926`. -/
def peerURL : _root_.Perennial.net.url.URL :=
  { (zero_val _root_.Perennial.net.url.URL) with Scheme' := go!"http", Host' := go!"127.0.0.1:23926" }

/-- `Main`'s client URL, `http://127.0.0.1:23916`. -/
def clientURL : _root_.Perennial.net.url.URL :=
  { (zero_val _root_.Perennial.net.url.URL) with Scheme' := go!"http", Host' := go!"127.0.0.1:23916" }

/-- **The URLs of `Main`'s configuration**: the peer URLs `[peerURL]`, the client URLs
`[clientURL]`, the initial cluster's map `{authkv ↦ [peerURL]}`. -/
def urlsOk (U : BootURLs) : Prop :=
  U.peer = [peerURL] ∧ U.client = [clientURL] ∧
    (∃ sl : GoSlice, U.initMap = GMap.insert go!"authkv" sl ∅) ∧ U.initURLs go!"authkv" = [peerURL]

/-- **The peer-URL directory of `Main`'s cluster**: its one member's peer URL, of the member `id`
only. -/
def akDir (id : w64) : w64 → List GoString := dirOne id go!"http://127.0.0.1:23926"

end pure

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The configuration `Main` passes to `NewServer`**, by its scalar fields: member `authkv` of a
new cluster with token `authkv`, data directory `authkv.etcd`, raft's clock `100` ms and `10`
ticks, and the simple token provider. -/
def cfgOk (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : Prop :=
  cfg.Name' = go!"authkv" ∧ cfg.DataDir' = go!"authkv.etcd" ∧
    cfg.InitialClusterToken' = go!"authkv" ∧ cfg.NewCluster' = true ∧
    cfg.TickMs' = W64 100 ∧ cfg.ElectionTicks' = W64 10 ∧ cfg.AuthToken' = go!"simple"

/-- **`Main`'s named premises** (persistent): putget's (`putget.premises`) at `authkv`'s
configuration, URLs and peer directory. -/
def premises (N : Nat) (id : w64) (bootLog : List EntryM) : IProp GF :=
  iprop(
    (□ ∀ (reg : GName) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
        (γ : RaftNames),
      ⌜cfgOk cfg ∧ urlsOk U ∧ γ.reCfg = GMap.listToSet [id] ∧ γ.reDyn = none ∧
        γ.reCCOk = putget.ccOk id ∧ γ.reBoot = bootLog ∧ γ.reNoSnap = true ∧ γ.reNoXfer = true⌝ -∗
      letI : MemStorReg GF := ⟨reg⟩; bootstrapContract cfg U γ id bootLog N (akDir id)) ∗
    rnLoggerZapOk ∗ rnSetLoggerOk ∗ rnTimeoutDetectorOk ∗ rnNewStorageOk ∗
    (□ ∀ E : RNEnv GF, ⌜E.T = iprop(True)⌝ -∗ rnTickerOk E) ∗
    rnStopOkStarted ∗
    v3rpc.runsNoRequireLeader)

instance premises_persistent (N : Nat) (id : w64) (bootLog : List EntryM) :
    Persistent (premises (GF := GF) N id bootLog) := by
  unfold premises; infer_instance

end defs

end authkv
end EtcdGrove
end Perennial
