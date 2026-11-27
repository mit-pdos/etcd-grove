/- Lean-first (no Rocq counterpart).

# `bootstrap`'s contract on a member machine, from the interim axiom `bootstrap.wp_proof_dist`

`notes/etcd-dist-plan.md` §16.3. The members of `etcd_safe`'s line took `bootstrap`'s contract as an Iris premise
(`etcdstart.bootPremise`, every member's `bootstrapContract`, in each statement's `Hprem`); now from the interim
axiom (`bootstrap.specDist`), as `etcdstart.BootBridge` does from `bootstrap.spec`:
* `bootGoAt`: the pure facts the axiom asks of a member's URLs: the values the caller names are Go's (`bootGo.*`
  at the token and the member's name), and the URLs are `etcd_safe`'s shape (one peer URL per entry, at most `typed.maxMembers`
  entries, this member's peer URLs its entry's, one client URL);
* `bootPremiseDist`: `bootPremise` with the round tripper's contract `etcd_dist.bootRTOk` at the raft names `γ`
  as a further hypothesis (the caller has it where it builds the server: `NewServer.specG_dist`'s `#Hpeers`,
  `#Hnoproxy`);
* `bootstrapContract_of_specDist`, `bootPremiseDist_of_specDist`: the contract from the axiom;
* `bootstrap.specDist_of_spec`: `bootstrap.spec` implies the axiom's statement (the retirement is a swap).

A defs module: it takes the axiom's statement as a hypothesis and imports no proof.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrapDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.BootBridge

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Net go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3 etcdstart

/-- **What `bootstrap` computes at the URLs `U`, and `etcd_safe`'s shape** (pure): the peers `ps`, contexts
`ctxs`, directory `dir` and member `name`'s id `id` are Go's (`bootGo.*` at the token `token`), the initial
cluster's URLs and names plain, every entry with one peer URL, at most `typed.maxMembers` entries, the member's peer URLs its
entry's and one client URL, and `bootstrap.spec`'s facts of the URLs (`urlsNe`, `initMapOk`). -/
def bootGoAt [GooseExts] (ps : List w64) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (token name : GoString) (id : w64) (U : BootURLs) : Prop :=
  bootGo.bootURLsPlain U ∧ bootGo.ps U token = ps ∧ bootGo.ctxs U token = ctxs ∧
    bootGo.dir U token = dir ∧ (bootGo.memberOf U token name).id = id ∧ bootNamesPlain U ∧
    bootGo.urlsNe U ∧ bootGo.initMapOk U token ∧
    (∀ k, (U.initMap.lookup k).isSome → (U.initURLs k).length = 1) ∧ GMap.size U.initMap ≤ typed.maxMembers ∧
    U.peer = U.initURLs name ∧ U.client.length = 1

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [π : NetProtoGS]

/-- **`bootstrap`'s contract for member `name` on a member machine** (`etcdstart.bootPremise` with the round
tripper's contract): at every server raft names `γ` of the cluster `ps`, for its configuration and URLs meeting
`Uok`, given `bootRTOk` at `γ` (the other members' peer addresses), `bootstrapContract`. -/
def bootPremiseDist (N : Nat) (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8))
    (dir : w64 → List GoString) (token name : GoString) (Uok : BootURLs → Prop) (id : w64) :
    IProp GF :=
  iprop(□ ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft),
      ⌜cfgOk token name cfg ∧ Uok U ∧
        γ.vs = ps ∧ γ.rule = srvRule (W64 0) bootLog ∧ γ.boot = bootLog⌝ -∗
      bootRTOk (hG := hG) γ id dir -∗
      letI : MemStorReg GF := ⟨γ.reg⟩; bootstrapContract cfg U γ id ctxs N dir)

instance bootPremiseDist_persistent (N : Nat) (ps : List w64) (bootLog : List EntryM)
    (ctxs : List (List w8)) (dir : w64 → List GoString) (token name : GoString)
    (Uok : BootURLs → Prop) (id : w64) :
    Persistent (bootPremiseDist (GF := GF) N ps bootLog ctxs dir token name Uok id) := by
  unfold bootPremiseDist; infer_instance

/-- **`bootstrap.spec` implies `bootstrap.specDist`**: the latter asks more (the shape, and the round tripper's
contract, framed away) and gives the same post. -/
theorem bootstrap.specDist_of_spec [MemStorReg GF]
    (hb : _root_.Perennial.EtcdGrove.bootstrap.spec (GF := GF) (hG := hG)) :
    _root_.Perennial.EtcdGrove.bootstrap.specDist (GF := GF) (hG := hG) := by
  intro _ _ cfg U γ N _ _ _ _ hnf hidr hune hplain hfips hiok hvs hbl hmem
  iintro %Φ Hpre HΦ
  icases Hpre with ⟨-, Hrest⟩
  iapply (hb cfg U γ N hnf hidr hune hplain hfips hiok hvs hbl hmem) $$ [Hrest] HΦ
  iexact Hrest

/-- **`bootstrapContract` at Go's values, from `bootstrap.specDist`**: for raft names `γ` meeting the spec's
conditions, given the package's initialization and the round tripper's contract (both persistent). -/
theorem bootstrapContract_of_specDist [ThreadBoundLe GF (2 ^ 29)] [ReceiptBoundLe GF (2 ^ 60)]
    [MemStorReg GF]
    (hb : _root_.Perennial.EtcdGrove.bootstrap.specDist (GF := GF) (hG := hG))
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft) (N : Nat)
    (h1 : ∀ k, (U.initMap.lookup k).isSome → (U.initURLs k).length = 1)
    (h64 : GMap.size U.initMap ≤ typed.maxMembers) (hpeer : U.peer = U.initURLs cfg.Name')
    (hcl : U.client.length = 1)
    (hidr : bootGo.idRaftOk cfg U) (hune : bootGo.urlsNe U)
    (hplain : bootGo.bootURLsPlain U) (hfips : crypto.fips140.GodebugFips140Off)
    (hiok : bootGo.initMapOk U cfg.InitialClusterToken')
    (hvs : γ.vs = bootGo.ps U cfg.InitialClusterToken')
    (hbl : ∃ bl : List LogEntry, BootLog (bootGo.ps U cfg.InitialClusterToken')
      (bootGo.ctxs U cfg.InitialClusterToken') bl ∧ γ.boot = LogEntry.toEntries bl 0)
    (hmem : memBoot γ.boot = bootGo.memMap U cfg.InitialClusterToken') :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ⊢
      bootRTOk (hG := hG) γ (bootGo.id cfg U) (bootGo.dir U cfg.InitialClusterToken') -∗
      bootstrapContract cfg U γ (bootGo.id cfg U) (bootGo.ctxs U cfg.InitialClusterToken') N
        (bootGo.dir U cfg.InitialClusterToken') := by
  iintro #Hpkg #Hrt
  iunfold bootstrapContract
  imodintro
  iintro %Φ !> Hpre HΦ
  icases Hpre with ⟨%Hpure, Hrest⟩
  have hnf : cfg.UnsafeNoFsync' = false := by
    obtain ⟨⟨-, -, -, -, -, -, h⟩, -⟩ := Hpure; exact h
  iapply (hb cfg U γ N h1 h64 hpeer hcl hnf hidr hune hplain hfips hiok hvs hbl hmem) $$ [Hrest] HΦ
  isplitr
  · iexact Hrt
  · isplitr
    · iexact Hpkg
    · isplitr
      · ipureintro; exact Hpure
      · iexact Hrest

/-- **`bootPremiseDist` from `bootstrap.specDist`**: for member `name` of the cluster with token `token`, at the
peers `ps`, bootstrap log `bootLog`, contexts `ctxs`, directory `dir` and id `id`, when, for every URLs `U` the
caller admits (`Uok`), these are Go's and the URLs `etcd_safe`'s shape (`bootGoAt`), and the bootstrap log is the
node API's log of `ps` and `ctxs` (`BootLog`); the id not one of raft's local targets, and the `fips140` GODEBUG
setting off (`bootstrap.spec`'s). As `etcdstart.bootPremise_of_spec`. -/
theorem bootPremiseDist_of_specDist [ThreadBoundLe GF (2 ^ 29)] [ReceiptBoundLe GF (2 ^ 60)]
    (hb : ∀ [MemStorReg GF], _root_.Perennial.EtcdGrove.bootstrap.specDist (GF := GF) (hG := hG))
    (N : Nat) (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8))
    (dir : w64 → List GoString) (token name : GoString) (Uok : BootURLs → Prop) (id : w64)
    (hfips : crypto.fips140.GodebugFips140Off)
    (hidr : id ≠ W64 18446744073709551615 ∧ id ≠ W64 18446744073709551614)
    (hfacts : ∀ U, Uok U → bootGoAt ps ctxs dir token name id U)
    (hlog : ∃ bl : List LogEntry, BootLog ps ctxs bl ∧ bootLog = LogEntry.toEntries bl 0) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ⊢
      bootPremiseDist (GF := GF) N ps bootLog ctxs dir token name Uok id := by
  iintro #Hpkg
  iunfold bootPremiseDist
  imodintro
  iintro %cfg %U %γ %Hp #Hrt
  obtain ⟨hc, hu, hvs, -, hboot⟩ := Hp
  obtain ⟨hplain, hps, hctxs, hdir, hid, hnp, hune, hiok, h1, h64, hpeer, hcl⟩ := hfacts U hu
  obtain ⟨bl, hbl, hbl0⟩ := hlog
  obtain ⟨hname, -, htok, -⟩ := hc
  have hid' : bootGo.id cfg U = id := by unfold bootGo.id; rw [htok, hname]; exact hid
  rw [← hname] at hpeer
  subst hps hctxs hdir hid' hboot htok
  have hmem : memBoot γ.boot = bootGo.memMap U cfg.InitialClusterToken' := by
    rw [hbl0]; exact memBoot_bootLog U _ bl hplain hnp hbl
  iapply (letI : MemStorReg GF := ⟨γ.reg⟩
    bootstrapContract_of_specDist hb cfg U γ N h1 h64 hpeer hcl
      (by unfold bootGo.idRaftOk; exact hidr) hune hplain hfips hiok hvs ⟨bl, hbl, hbl0⟩ hmem)
  all_goals first | iexact Hpkg | iexact Hrt

end defs

end etcd_dist
end EtcdGrove
end Perennial

end
