/-
**watchkv's vocabulary** (D23, 2026-10-20). Lean-first (no Rocq counterpart).

* The configuration `Main` starts its member with, as putget's (`Proof/.../putget/Defs.lean`,
  whose header explains each premise) at watchkv's names and ports: `cfgOk` (member and token
  `watchkv`, data directory `watchkv.etcd`), `urlsOk` (peer URL `http://127.0.0.1:23841`, client
  URL `http://127.0.0.1:23831`), the peer directory `wkDir`, and `premises`: putget's at these,
  (until 2026-10-20 also the transport premise `client.noRetryableStreamErr`, that the transport
  never fails a watch stream with a retryable code; gone with D25: the client watcher's
  reconnection is verified).
* The program's values: `genKeys`/`genVals` (`Gen`'s), `pairOf` (a `kv`'s key and value),
  `CheckOk` (what `check` needs not to panic).
* `revAt E r k v`: revision `r` of a sealed log of the server's store is the put of `k ↦ v` (no
  lease); two agree (`revAt_agree`: sealed logs are in prefix order).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.watchkv.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.watchkv.LogFacts
public import Proof.github_com.mit_pdos.etcd_grove.examples.putget.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace watchkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3
open github_com.mit_pdos.etcd_grove.examples.watchkv

section pure
variable [ext : FfiSyntax]

/-- The program's structs (`kv`, `event`, `putRec`), by short names. -/
abbrev wkv := github_com.mit_pdos.etcd_grove.examples.watchkv.kv
abbrev wev := github_com.mit_pdos.etcd_grove.examples.watchkv.event
abbrev wrec := github_com.mit_pdos.etcd_grove.examples.watchkv.putRec

/-- `Main`'s peer URL, `http://127.0.0.1:23841`. -/
def peerURL : _root_.Perennial.net.url.URL :=
  { (zero_val _root_.Perennial.net.url.URL) with Scheme' := go!"http", Host' := go!"127.0.0.1:23841" }

/-- `Main`'s client URL, `http://127.0.0.1:23831`. -/
def clientURL : _root_.Perennial.net.url.URL :=
  { (zero_val _root_.Perennial.net.url.URL) with Scheme' := go!"http", Host' := go!"127.0.0.1:23831" }

/-- **The URLs of `Main`'s configuration**: the peer URLs `[peerURL]`, the client URLs
`[clientURL]`, the initial cluster's map `{watchkv ↦ [peerURL]}`. -/
def urlsOk (U : BootURLs) : Prop :=
  U.peer = [peerURL] ∧ U.client = [clientURL] ∧
    (∃ sl : GoSlice, U.initMap = GMap.insert go!"watchkv" sl ∅) ∧ U.initURLs go!"watchkv" = [peerURL]

/-- **The peer-URL directory of `Main`'s cluster**: its one member's peer URL, of the
member `id` only (`dirOne`; 2026-10-24, rafthttp stage 6d; until then every id's). -/
def wkDir (id : w64) : w64 → List GoString := dirOne id go!"http://127.0.0.1:23841"

/-- The prefix the writers' keys are under and the watch covers. -/
abbrev wkPfx : GoString := go!"wk/"

/-- The keys `Gen` picks from. -/
abbrev genKeys : List GoString := [go!"wk/k0", go!"wk/k1", go!"wk/k2"]

/-- The values `Gen` picks from. -/
abbrev genVals : List GoString := [go!"a", go!"b", go!"c", go!"d"]

/-- A `kv`'s key and value. -/
def pairOf (p : wkv) : GoString × GoString := (p.key', p.val')

/-- A `kv` `Gen` may return. -/
def GenKv (p : wkv) : Prop := p.key' ∈ genKeys ∧ p.val' ∈ genVals

/-- **What `check` needs not to panic**: the events are puts at revisions `2, 3, ...` (one per
revision, in order), each of a key and value tried, fewer than `2 ^ 63 - 1`; and each successful Put
is the event at its revision with its key and value. -/
def CheckOk (evs : List wev) (tried : List wkv) (oks : List wrec) : Prop :=
  evs.length + 1 < 2 ^ 63 ∧
  (∀ (i : Nat) (e : wev), evs[i]? = some e →
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

/-- **The configuration `Main` passes to `NewServer`**, by its scalar fields: member `watchkv` of
a new cluster with token `watchkv`, data directory `watchkv.etcd`, raft's clock `100` ms and `10`
ticks. -/
def cfgOk (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : Prop :=
  cfg.Name' = go!"watchkv" ∧ cfg.DataDir' = go!"watchkv.etcd" ∧
    cfg.InitialClusterToken' = go!"watchkv" ∧ cfg.NewCluster' = true ∧
    cfg.TickMs' = W64 100 ∧ cfg.ElectionTicks' = W64 10

/-- **`Main`'s named premises** (persistent): putget's (`putget.premises`) at `watchkv`'s
configuration, URLs and peer directory. -/
def premises (N : Nat) (id : w64) (bootLog : List EntryM) : IProp GF :=
  iprop(
    (□ ∀ (reg : GName) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
        (γ : RaftNames),
      ⌜cfgOk cfg ∧ urlsOk U ∧ γ.reCfg = GMap.listToSet [id] ∧ γ.reDyn = none ∧
        γ.reCCOk = putget.ccOk id ∧ γ.reBoot = bootLog ∧ γ.reNoSnap = true ∧ γ.reNoXfer = true⌝ -∗
      letI : MemStorReg GF := ⟨reg⟩; bootstrapContract cfg U γ id bootLog N (wkDir id)) ∗
    rnLoggerZapOk ∗ rnSetLoggerOk ∗ rnTimeoutDetectorOk ∗ rnNewStorageOk ∗
    (□ ∀ E : RNEnv GF, ⌜E.T = iprop(True)⌝ -∗ rnTickerOk E) ∗
    rnStopOkStarted ∗
    v3rpc.runsNoRequireLeader)

instance premises_persistent (N : Nat) (id : w64) (bootLog : List EntryM) :
    Persistent (premises (GF := GF) N id bootLog) := by
  unfold premises; infer_instance

end defs

section rev
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **Revision `r` of the store is the put of `k ↦ v`** (persistent): a sealed log of the store
`E.γ` has it. -/
def revAt (E : apply.AEnv GF) (r : Nat) (k v : GoString) : IProp GF :=
  iprop(∃ L : mvcc.Log, mvcc.idxSealed E.γ.idx L ∗ ⌜L[r]? = some [mvcc.Change.put k v (W64 0)]⌝)

instance revAt_persistent (E : apply.AEnv GF) (r : Nat) (k v : GoString) :
    Persistent (revAt (GF := GF) E r k v) := by
  unfold revAt; infer_instance

/-- **Two `revAt`s of one revision agree.** -/
theorem revAt_agree (E : apply.AEnv GF) (r : Nat) (k v k' v' : GoString) :
    revAt (GF := GF) E r k v ∗ revAt E r k' v' ⊢ ⌜k = k' ∧ v = v'⌝ := by
  unfold revAt
  iintro ⟨⟨%L, #H, %h⟩, ⟨%L', #H', %h'⟩⟩
  ihave %Hp := mvcc.idxSealed_prefix E.γ.idx L L' $$ [H H']
  · isplit
    · iexact H
    · iexact H'
  ipureintro
  have hrL : r < L.length := (List.getElem?_eq_some_iff.mp h).1
  have hrL' : r < L'.length := (List.getElem?_eq_some_iff.mp h').1
  have e : L[r]? = L'[r]? := by
    rcases Hp with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · rw [List.getElem?_append_left hrL]
    · rw [List.getElem?_append_left hrL']
  rw [h, h'] at e
  simp at e
  exact e

end rev

end watchkv
end EtcdGrove
end Perennial
