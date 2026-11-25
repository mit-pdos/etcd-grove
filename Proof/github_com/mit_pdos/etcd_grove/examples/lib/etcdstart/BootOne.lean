/-
**A one-member example's `bootstrap` contract from the interim bootstrap axiom's statement**
(2026-11-24; `notes/decisions.md`, "The interim bootstrap axiom at one member"). The one-member examples'
closed theorems took `bootstrap`'s contract as their named Iris premise (`premises`, `OneMember.lean`:
`bootstrapContract` at every configuration and URLs of the member `name` at `peer` and `client`).
`bootstrap.specOne` (`bootstrap.spec` at a one-member initial cluster of one peer URL) gives it, at Go's
values: `premises_of_specOne`, given the pure facts `BootGo1` (the member id, the peers' contexts, the
directory and the bootstrap log are what Go computes from `name` and `peer`) and the `fips140` GODEBUG
setting off (`crypto.fips140.GodebugFips140Off`, an environment premise of the spec). As `BootBridge.lean`
(#34's, for `bootstrap.spec`) does for every cluster.

A defs module: it takes `bootstrap.specOne` as a hypothesis (the linking module `BootOneLinked.lean`
passes the interim axiom `bootstrap.wp_proofOne`) and imports no proof.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrapOne
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.OneMember

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **`bootstrap`'s results for a one-member cluster are Go's** (pure facts of the program, the
interim bootstrap axiom's premises at `urls1`): for the member `name` (its cluster token its name) at the
peer address `peer` and the client address `client`, the member id `id` is not one of raft's local
targets (`bootGo.idRaftOk`), the bootstrap log `boot` is the node API's log of the one peer `id` and the
contexts `ctxs` (`BootLog`), and at every URLs `urls1` admits (all of which agree on the initial
cluster: the one entry `name`, of the one URL `http://peer`) Go's peers are `[id]`, its contexts `ctxs`,
its directory `dir1 peer id`, the entry's member id `id`, the log's members (`memBoot`, through the
opaque `membership.ccMemberOf`) the cluster's, and the URLs plain, not empty and fitting
(`bootURLsPlain`, `urlsNe`, `initMapOk`). -/
structure BootGo1 (name peer client : GoString) (id : w64) (ctxs : List (List w8))
    (boot : List LogEntry) : Prop where
  idRaft : id ≠ W64 18446744073709551615 ∧ id ≠ W64 18446744073709551614
  log : BootLog [id] ctxs boot
  go : ∀ U : BootURLs, urls1 name peer client U →
    bootGo.bootURLsPlain U ∧ bootGo.ps U name = [id] ∧ bootGo.ctxs U name = ctxs ∧
      bootGo.dir U name = dir1 peer id ∧ (bootGo.memberOf U name name).id = id ∧
      memBoot (LogEntry.toEntries boot 0) = bootGo.memMap U name ∧ bootGo.urlsNe U ∧
      bootGo.initMapOk U name

end pure

section bridge
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`premises` from `bootstrap.specOne`** (see the file header): at the pure facts `BootGo1` and the
`fips140` setting off, every `bootstrapContract` that `premises` names is `bootstrap.specOne`'s triple at
the configuration (its member `name`, one URL: `urls1`), with `isPkgInit` framed from the context. -/
theorem premises_of_specOne [ThreadBoundLe GF (2 ^ 29)] [ReceiptBoundLe GF (2 ^ 60)]
    (hb : ∀ [MemStorReg GF], _root_.Perennial.EtcdGrove.bootstrap.specOne (GF := GF) (hG := hG))
    (name peer client : GoString) (N : Nat) (id : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (hfips : crypto.fips140.GodebugFips140Off) (hf : BootGo1 name peer client id ctxs boot) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ⊢
      premises (GF := GF) name peer client N id ctxs boot := by
  iintro #Hpkg
  iunfold premises
  imodintro
  iintro %cfg %U %γ %Hp
  obtain ⟨hc, hu, hvs, -, hboot⟩ := Hp
  obtain ⟨hname, -, htok, -, -, -, hnf⟩ := hc
  obtain ⟨hplain, hps, hctxs, hdir, hid, hmem, hune, hiok⟩ := hf.go U hu
  obtain ⟨-, -, ⟨sl, hsl⟩, hiu⟩ := hu
  have hid' : bootGo.id cfg U = id := by unfold bootGo.id; rw [htok, hname]; exact hid
  have hone : (U.initURLs cfg.Name').length = 1 := by rw [hname, hiu]; rfl
  have hmap : ∃ sl : GoSlice, U.initMap = GMap.insert cfg.Name' sl ∅ := ⟨sl, by rw [hname]; exact hsl⟩
  have hidr : bootGo.idRaftOk cfg U := by unfold bootGo.idRaftOk; rw [hid']; exact hf.idRaft
  rw [← htok] at hps hctxs hdir hmem hiok
  letI : MemStorReg GF := ⟨γ.reg⟩
  rw [← hdir, ← hctxs, ← hid']
  iunfold bootstrapContract
  imodintro
  iintro %Φ !> Hpre HΦ
  iapply (hb cfg U γ N hmap hone hnf hidr hune hplain hfips hiok (by rw [hvs, hps])
    ⟨boot, by rw [hps, hctxs]; exact hf.log, hboot⟩ (by rw [hboot]; exact hmem)) $$ [Hpre] HΦ
  isplitr
  · iexact Hpkg
  · iexact Hpre

end bridge

end etcdstart
end EtcdGrove
end Perennial
