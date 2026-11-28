/- Lean-first (no Rocq counterpart).

# `bootPremiseR` from `bootstrap.specRestart` (premises to axioms, 2026-11-27)

The restart examples took `bootstrap`'s restart contract as an Iris premise (`bootPremiseR`, every stopped
member's `bootstrapRestartContract`); the interim axiom `bootstrap.wp_proofRestart` (`bootstrap.specRestart`)
gives it at Go's values, as `BootBridge.lean`'s `bootPremise_of_spec` does for a first start:
* `bootPremiseR_of_specRestart`: given, for every URLs the caller admits, that the peers, contexts, directory
  and id it names are Go's (`bootGo.*` at the token and the member's name), the boot log the node API's log of
  them and its members the cluster's, and the member one of the peers;
* `bootPremiseR_one`: at a one-member cluster (`urls1`), from `BootGo1` (the one-member examples' pure facts).

A defs module: it takes the axiom's statement as a hypothesis (the linking module passes
`bootstrap.wp_proofRestart`) and imports no proof.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrapRestart
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Restart
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.BootOne

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section bridge
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`bootPremiseR` from `bootstrap.specRestart`**: for member `name` (id `id`, one of the peers `ps`) of the
cluster with token `token`, when, for every URLs `U` the caller admits (`Uok`), the peers, contexts, directory
and id are Go's, the boot log `bootLog` is the node API's log of `ps` and `ctxs` and its members are the
cluster's; the id not one of raft's local targets, and the `fips140` GODEBUG setting off. -/
theorem bootPremiseR_of_specRestart [ThreadBoundLe GF (2 ^ 29)] [ReceiptBoundLe GF (2 ^ 60)]
    (hb : ∀ [MemStorReg GF], _root_.Perennial.EtcdGrove.bootstrap.specRestart (GF := GF) (hG := hG))
    (N : Nat) (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8))
    (dir : w64 → List GoString) (token name : GoString) (Uok : BootURLs → Prop) (id : w64)
    (hfips : crypto.fips140.GodebugFips140Off)
    (hidr : id ≠ W64 18446744073709551615 ∧ id ≠ W64 18446744073709551614)
    (hfacts : ∀ U, Uok U →
      bootGo.bootURLsPlain U ∧ bootGo.ps U token = ps ∧ bootGo.ctxs U token = ctxs ∧
        bootGo.dir U token = dir ∧ (bootGo.memberOf U token name).id = id ∧
        (∃ bl : List LogEntry, BootLog ps ctxs bl ∧ bootLog = LogEntry.toEntries bl 0) ∧
        memBoot bootLog = bootGo.memMap U token ∧ bootGo.urlsNe U ∧ bootGo.initMapOk U token)
    (hid : id ∈ ps) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ⊢
      bootPremiseR (GF := GF) N ps bootLog ctxs dir token name Uok id := by
  iintro #Hpkg
  iunfold bootPremiseR
  imodintro
  iintro %cfg %U %γ %Hp
  obtain ⟨hc, hu, hvs, -, hboot⟩ := Hp
  obtain ⟨hplain, hps, hctxs, hdir, hidU, ⟨bl, hbl, hbl0⟩, hmem, hune, hiok⟩ := hfacts U hu
  obtain ⟨hname, -, htok, -, -, -, hnf⟩ := hc
  have hid' : bootGo.id cfg U = id := by unfold bootGo.id; rw [htok, hname]; exact hidU
  subst hps hctxs hdir hid' hboot htok
  letI : MemStorReg GF := ⟨γ.reg⟩
  iapply (hb cfg U γ N hnf (by unfold bootGo.idRaftOk; exact hidr) hune hplain hfips hiok hvs
    ⟨bl, hbl, hbl0⟩ hmem hid)
  iexact Hpkg

/-- **`bootPremiseR` at a one-member cluster** (`urls1`: the member `name`, its token its name, at `peer`
and `client`), from the one-member examples' pure facts `BootGo1` and the member's name plain. -/
theorem bootPremiseR_one [ThreadBoundLe GF (2 ^ 29)] [ReceiptBoundLe GF (2 ^ 60)]
    (hb : ∀ [MemStorReg GF], _root_.Perennial.EtcdGrove.bootstrap.specRestart (GF := GF) (hG := hG))
    (name peer client : GoString) (N : Nat) (id : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (hnp : ∀ c ∈ name, JsonScan.plainEnc c)
    (hfips : crypto.fips140.GodebugFips140Off) (hf : BootGo1 name peer client id ctxs boot) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ⊢
      bootPremiseR (GF := GF) N [id] (LogEntry.toEntries boot 0) ctxs (dir1 peer id) name name
        (urls1 name peer client) id :=
  bootPremiseR_of_specRestart hb N [id] (LogEntry.toEntries boot 0) ctxs (dir1 peer id) name name
    (urls1 name peer client) id hfips hf.idRaft
    (fun U hu => by
      obtain ⟨hplain, hps, hctxs, hdir, hid, hune, hiok⟩ := hf.go U hu
      obtain ⟨-, -, ⟨sl, hsl⟩, -⟩ := hu
      exact ⟨hplain, hps, hctxs, hdir, hid, ⟨boot, hf.log, rfl⟩,
        memBoot_one U name id ctxs boot hnp ⟨sl, hsl⟩ hplain hps hctxs hf.log, hune, hiok⟩)
    (List.mem_singleton_self id)

end bridge

end etcdstart
end EtcdGrove
end Perennial

end
