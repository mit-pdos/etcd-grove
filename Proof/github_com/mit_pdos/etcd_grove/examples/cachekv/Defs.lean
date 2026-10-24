/-
**cachekv's vocabulary** (2026-10-20). Lean-first (no Rocq counterpart).

watchkv's (`Proof/.../watchkv/Defs.lean`) at cachekv's names, ports and prefix:

* The configuration `Main` starts its member with, as putget's (`Proof/.../putget/Defs.lean`,
  whose header explains each premise) at cachekv's names and ports: `cfgOk` (member and token
  `cachekv`, data directory `cachekv.etcd`), `urlsOk` (peer URL `http://127.0.0.1:23861`, client
  URL `http://127.0.0.1:23851`), the peer directory `ckDir`, and `premises`: putget's at these
  (until 2026-10-20 also the transport premise `client.noRetryableStreamErr`, gone with D25: the
  client watcher's reconnection is verified).
* The program's values: `genKeys`/`genVals` (`Gen`'s, under the prefix `ck/`), `pairOf` (a `kv`'s
  key and value), `CheckOk` (what `check` needs not to panic).
* The workload (`watchkv.workload`), its logs (`watchkv.WkLog`) and `watchkv.revAt` are watchkv's.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.cachekv.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.watchkv.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.putget.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cachekv

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3
open github_com.mit_pdos.etcd_grove.examples.cachekv

section pure
variable [ext : FfiSyntax]

/-- The program's structs (`kv`, `event`, `putRec`), by short names. -/
abbrev ckv := github_com.mit_pdos.etcd_grove.examples.cachekv.kv
abbrev cev := github_com.mit_pdos.etcd_grove.examples.cachekv.event
abbrev crec := github_com.mit_pdos.etcd_grove.examples.cachekv.putRec

/-- `Main`'s peer URL, `http://127.0.0.1:23861`. -/
def peerURL : _root_.Perennial.net.url.URL :=
  { (zero_val _root_.Perennial.net.url.URL) with Scheme' := go!"http", Host' := go!"127.0.0.1:23861" }

/-- `Main`'s client URL, `http://127.0.0.1:23851`. -/
def clientURL : _root_.Perennial.net.url.URL :=
  { (zero_val _root_.Perennial.net.url.URL) with Scheme' := go!"http", Host' := go!"127.0.0.1:23851" }

/-- **The URLs of `Main`'s configuration**: the peer URLs `[peerURL]`, the client URLs
`[clientURL]`, the initial cluster's map `{cachekv ↦ [peerURL]}`. -/
def urlsOk (U : BootURLs) : Prop :=
  U.peer = [peerURL] ∧ U.client = [clientURL] ∧
    (∃ sl : GoSlice, U.initMap = GMap.insert go!"cachekv" sl ∅) ∧ U.initURLs go!"cachekv" = [peerURL]

/-- **The peer-URL directory of `Main`'s cluster**: its one member's peer URL, of the
member `id` only (`dirOne`; 2026-10-24, rafthttp stage 6d; until then every id's). -/
def ckDir (id : w64) : w64 → List GoString := dirOne id go!"http://127.0.0.1:23861"

/-- The prefix the writers' keys are under and the watch covers. -/
abbrev ckPfx : GoString := go!"ck/"

/-- The keys `Gen` picks from. -/
abbrev genKeys : List GoString := [go!"ck/k0", go!"ck/k1", go!"ck/k2"]

/-- The values `Gen` picks from. -/
abbrev genVals : List GoString := [go!"a", go!"b", go!"c", go!"d"]

/-- A `kv`'s key and value. -/
def pairOf (p : ckv) : GoString × GoString := (p.key', p.val')

/-- A `kv` `Gen` may return. -/
def GenKv (p : ckv) : Prop := p.key' ∈ genKeys ∧ p.val' ∈ genVals

/-- **What `check` needs not to panic**: the events are puts at revisions `2, 3, ...` (one per
revision, in order), each of a key and value tried, fewer than `2 ^ 63 - 1`; and each successful Put
is the event at its revision with its key and value. -/
def CheckOk (evs : List cev) (tried : List ckv) (oks : List crec) : Prop :=
  evs.length + 1 < 2 ^ 63 ∧
  (∀ (i : Nat) (e : cev), evs[i]? = some e →
    e.put' = true ∧ sint.Z e.rev' = 2 + i ∧ (e.key', e.val') ∈ tried.map pairOf) ∧
  (∀ p ∈ oks, 2 ≤ sint.Z p.rev' ∧ ∃ e, evs[(sint.Z p.rev' - 2).toNat]? = some e ∧
    e.key' = p.key' ∧ e.val' = p.val')

end pure

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The configuration `Main` passes to `NewServer`**, by its scalar fields: member `cachekv` of
a new cluster with token `cachekv`, data directory `cachekv.etcd`, raft's clock `100` ms and `10`
ticks. -/
def cfgOk (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : Prop :=
  cfg.Name' = go!"cachekv" ∧ cfg.DataDir' = go!"cachekv.etcd" ∧
    cfg.InitialClusterToken' = go!"cachekv" ∧ cfg.NewCluster' = true ∧
    cfg.TickMs' = W64 100 ∧ cfg.ElectionTicks' = W64 10

/-- **`Main`'s named premises** (persistent): putget's (`putget.premises`) at `cachekv`'s
configuration, URLs and peer directory. -/
def premises (N : Nat) (id : w64) (bootLog : List EntryM) : IProp GF :=
  iprop(
    (□ ∀ (reg : GName) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
        (γ : RaftNames),
      ⌜cfgOk cfg ∧ urlsOk U ∧ γ.reCfg = GMap.listToSet [id] ∧ γ.reDyn = none ∧
        γ.reCCOk = putget.ccOk id ∧ γ.reBoot = bootLog ∧ γ.reNoSnap = true ∧ γ.reNoXfer = true⌝ -∗
      letI : MemStorReg GF := ⟨reg⟩; bootstrapContract cfg U γ id bootLog N (ckDir id)) ∗
    rnLoggerZapOk ∗ rnSetLoggerOk ∗ rnTimeoutDetectorOk ∗ rnNewStorageOk ∗
    (□ ∀ E : RNEnv GF, ⌜E.T = iprop(True)⌝ -∗ rnTickerOk E) ∗
    rnStopOkStarted ∗
    v3rpc.runsNoRequireLeader)

instance premises_persistent (N : Nat) (id : w64) (bootLog : List EntryM) :
    Persistent (premises (GF := GF) N id bootLog) := by
  unfold premises; infer_instance

end defs

end cachekv
end EtcdGrove
end Perennial
