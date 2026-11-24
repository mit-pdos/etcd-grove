/-
**`bootPremise` from `bootstrap.spec`** (claim #34, 2026-11-24). The examples take `bootstrap`'s
contract as a premise (`bootPremise`, every member's `bootstrapContract`); `bootstrap.spec`, the
function's own spec, gives it at Go's values (`bootGo`) for the raft names it covers. This bridge says
what an example still has to show to replace the premise by the spec: pure facts about its URLs (the
peers, contexts, directory and id it names are Go's, `bootGo.*` at the configuration's token and
name), and the package's initialization (`isPkgInit`, which `bootstrap.spec`'s precondition carries and
`bootstrapContract`'s does not: callers have it persistently, `iPkgInit`).

A defs module: it takes `bootstrap.spec` as a hypothesis (the linking module passes
`bootstrap.wp_proof`'s result) and imports no proof.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrap
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Defs

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

/-- **`bootstrapContract` at Go's values, from `bootstrap.spec`**: for raft names `γ` meeting the
spec's conditions, the contract's triple is the spec's with `isPkgInit` framed from the context. -/
theorem bootstrapContract_of_spec [ThreadBoundLe GF (2 ^ 29)] [ReceiptBoundLe GF (2 ^ 60)]
    [MemStorReg GF]
    (hb : _root_.Perennial.EtcdGrove.bootstrap.spec (GF := GF) (hG := hG))
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft) (N : Nat)
    (hplain : bootGo.bootURLsPlain U)
    (hvs : γ.vs = bootGo.ps U cfg.InitialClusterToken')
    (hbl : ∃ bl : List LogEntry, BootLog (bootGo.ps U cfg.InitialClusterToken')
      (bootGo.ctxs U cfg.InitialClusterToken') bl ∧ γ.boot = LogEntry.toEntries bl 0)
    (hmem : memBoot γ.boot = bootGo.memMap U cfg.InitialClusterToken') :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ⊢
      bootstrapContract cfg U γ (bootGo.id cfg U) (bootGo.ctxs U cfg.InitialClusterToken') N
        (bootGo.dir U cfg.InitialClusterToken') := by
  iintro #Hpkg
  iunfold bootstrapContract
  imodintro
  iintro %Φ !> Hpre HΦ
  iapply (hb cfg U γ N hplain hvs hbl hmem) $$ [Hpre] HΦ
  isplitr
  · iexact Hpkg
  · iexact Hpre

/-- **`bootPremise` from `bootstrap.spec`** (see the file header): for member `name` of the cluster
with token `token`, at the peers `ps`, bootstrap log `bootLog`, contexts `ctxs`, directory `dir` and
id `id`, when, for every URLs `U` the example admits (`Uok`), these are Go's (`bootGo.*` at `token`
and `name`), the initial cluster's URLs are plain, the bootstrap log is the node API's log of `ps`
and `ctxs` (`BootLog`), and its members are the cluster's (`memBoot`, the spec's `Hmem`). -/
theorem bootPremise_of_spec [ThreadBoundLe GF (2 ^ 29)] [ReceiptBoundLe GF (2 ^ 60)]
    (hb : ∀ [MemStorReg GF], _root_.Perennial.EtcdGrove.bootstrap.spec (GF := GF) (hG := hG))
    (N : Nat) (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8))
    (dir : w64 → List GoString) (token name : GoString) (Uok : BootURLs → Prop) (id : w64)
    (hfacts : ∀ U, Uok U →
      bootGo.bootURLsPlain U ∧ bootGo.ps U token = ps ∧ bootGo.ctxs U token = ctxs ∧
        bootGo.dir U token = dir ∧ (bootGo.memberOf U token name).id = id ∧
        (∃ bl : List LogEntry, BootLog ps ctxs bl ∧ bootLog = LogEntry.toEntries bl 0) ∧
        memBoot bootLog = bootGo.memMap U token) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ⊢
      bootPremise (GF := GF) N ps bootLog ctxs dir token name Uok id := by
  iintro #Hpkg
  iunfold bootPremise
  imodintro
  iintro %cfg %U %γ %Hp
  obtain ⟨hc, hu, hvs, -, hboot⟩ := Hp
  obtain ⟨hplain, hps, hctxs, hdir, hid, ⟨bl, hbl, hbl0⟩, hmem⟩ := hfacts U hu
  obtain ⟨hname, -, htok, -⟩ := hc
  have hid' : bootGo.id cfg U = id := by unfold bootGo.id; rw [htok, hname]; exact hid
  subst hps hctxs hdir hid' hboot htok
  iapply (letI : MemStorReg GF := ⟨γ.reg⟩
    bootstrapContract_of_spec hb cfg U γ N hplain hvs ⟨bl, hbl, hbl0⟩ hmem)
  iexact Hpkg

end bridge

end etcdstart
end EtcdGrove
end Perennial
