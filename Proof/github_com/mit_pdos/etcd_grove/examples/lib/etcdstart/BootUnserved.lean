/-
**`bootPremiseF` from `bootstrap.specUnserved`** (2026-11-27, restartN's first boots): as `BootBridge`'s
`bootPremise_of_spec`, the contract of a member of a cluster started in one process before any member serves its
peer address, from the interim axiom `bootstrap.wp_proofUnserved`, with the frame the other members' peer addresses'
rights (`http.httpAddrFree`, lent for the call). What an example shows: `BootBridge`'s pure facts (its values are
Go's) and the axiom's shape (`shapeUnserved`); `urlsN_shapeUnserved` gives the latter for `StartMembers`' URLs
(`urlsN`), at the members' peer addresses.

A defs module: it takes the axiom's statement as a hypothesis and imports no proof.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrapUnserved
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.BootBridge
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.MembersDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **`bootstrap.specUnserved`'s shape** of the URLs `U` of member `name`: one peer URL per initial-cluster entry,
the member's peer URLs its entry's, one client URL, and the other entries' hosts among `addrs`. -/
def shapeUnserved (U : BootURLs) (name : GoString) (addrs : List GoString) : Prop :=
  (∀ k, (U.initMap.lookup k).isSome → (U.initURLs k).length = 1) ∧
    U.peer = U.initURLs name ∧ U.client.length = 1 ∧
    (∀ k, (U.initMap.lookup k).isSome → k ≠ name → ∀ u ∈ U.initURLs k, u.Host' ∈ addrs)

/-- **`StartMembers`' URLs have the shape**, at the members' peer addresses: member `m` of the members `ms`
(distinct names). -/
theorem urlsN_shapeUnserved (ms : List GMember) (hnd : (ms.map (·.Name')).Nodup) (m : GMember)
    (hm : m ∈ ms) (U : BootURLs) (hu : urlsN ms m U) :
    shapeUnserved U m.Name' (ms.map (·.Peer')) := by
  obtain ⟨hpeer, hcl, hdom, hiu⟩ := hu
  refine ⟨fun k hk => ?_, ?_, by rw [hcl]; rfl, fun k _ _ u hu' => ?_⟩
  · obtain ⟨m', hm', rfl⟩ := List.mem_map.1 ((hdom k).1 hk)
    rw [hiu, iuOf_mem ms hnd m' hm']; rfl
  · rw [hpeer, hiu, iuOf_mem ms hnd m hm]
  · rw [hiu] at hu'
    unfold iuOf at hu'
    split at hu'
    · rename_i m' hf
      rw [List.mem_singleton] at hu'
      subst hu'
      exact List.mem_map_of_mem (List.mem_of_find?_eq_some hf)
    · simp at hu'

end pure

section bridge
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The frame of the other members' peer addresses**: the right to listen at each of `addrs`, reserved for HTTP. -/
abbrev addrsFree (addrs : List GoString) : IProp GF := iprop([∗list] a ∈ addrs, http.httpAddrFree (hG := hG) a)

/-- **`bootstrapContractF` at Go's values, from `bootstrap.specUnserved`**, at the frame `addrsFree addrs`: as
`bootstrapContract_of_spec`. -/
theorem bootstrapContractF_of_specUnserved [ThreadBoundLe GF (2 ^ 29)] [ReceiptBoundLe GF (2 ^ 60)]
    [MemStorReg GF]
    (hb : _root_.Perennial.EtcdGrove.bootstrap.specUnserved (GF := GF) (hG := hG))
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft) (N : Nat)
    (addrs : List GoString) (hsh : shapeUnserved U cfg.Name' addrs)
    (hidr : bootGo.idRaftOk cfg U) (hune : bootGo.urlsNe U)
    (hplain : bootGo.bootURLsPlain U) (hfips : crypto.fips140.GodebugFips140Off)
    (hiok : bootGo.initMapOk U cfg.InitialClusterToken')
    (hvs : γ.vs = bootGo.ps U cfg.InitialClusterToken')
    (hbl : ∃ bl : List LogEntry, BootLog (bootGo.ps U cfg.InitialClusterToken')
      (bootGo.ctxs U cfg.InitialClusterToken') bl ∧ γ.boot = LogEntry.toEntries bl 0)
    (hmem : memBoot γ.boot = bootGo.memMap U cfg.InitialClusterToken') :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ⊢
      bootstrapContractF (addrsFree addrs) cfg U γ (bootGo.id cfg U) (bootGo.ctxs U cfg.InitialClusterToken') N
        (bootGo.dir U cfg.InitialClusterToken') := by
  iintro #Hpkg
  iunfold bootstrapContractF
  imodintro
  iintro %Φ !> ⟨HR, Hpre⟩ HΦ
  icases Hpre with ⟨%Hpure, Hrest⟩
  have hnf : cfg.UnsafeNoFsync' = false := by
    obtain ⟨⟨-, -, -, -, -, -, h⟩, -⟩ := Hpure; exact h
  obtain ⟨h1, hpeer, hcl, hhosts⟩ := hsh
  iapply (hb cfg U γ N addrs h1 hpeer hcl hhosts hnf hidr hune hplain hfips hiok hvs hbl hmem) $$ [HR Hrest] HΦ
  iunfold addrsFree at HR
  iframe HR
  isplitr
  · iexact Hpkg
  · isplitr
    · ipureintro; exact Hpure
    · iexact Hrest

/-- **`bootPremiseF` from `bootstrap.specUnserved`** (see the file header): `bootPremise_of_spec`'s facts, and for
every URLs `U` the example admits the axiom's shape at the addresses `addrs`; the frame `addrsFree addrs`. -/
theorem bootPremiseF_of_specUnserved [ThreadBoundLe GF (2 ^ 29)] [ReceiptBoundLe GF (2 ^ 60)]
    (hb : ∀ [MemStorReg GF], _root_.Perennial.EtcdGrove.bootstrap.specUnserved (GF := GF) (hG := hG))
    (N : Nat) (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8))
    (dir : w64 → List GoString) (token name : GoString) (Uok : BootURLs → Prop) (id : w64)
    (addrs : List GoString)
    (hfips : crypto.fips140.GodebugFips140Off)
    (hidr : id ≠ W64 18446744073709551615 ∧ id ≠ W64 18446744073709551614)
    (hshape : ∀ U, Uok U → shapeUnserved U name addrs)
    (hfacts : ∀ U, Uok U →
      bootGo.bootURLsPlain U ∧ bootGo.ps U token = ps ∧ bootGo.ctxs U token = ctxs ∧
        bootGo.dir U token = dir ∧ (bootGo.memberOf U token name).id = id ∧
        (∃ bl : List LogEntry, BootLog ps ctxs bl ∧ bootLog = LogEntry.toEntries bl 0) ∧
        bootNamesPlain U ∧ bootGo.urlsNe U ∧ bootGo.initMapOk U token) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ⊢
      bootPremiseF (GF := GF) (addrsFree addrs) N ps bootLog ctxs dir token name Uok id := by
  iintro #Hpkg
  iunfold bootPremiseF
  imodintro
  iintro %cfg %U %γ %Hp
  obtain ⟨hc, hu, hvs, -, hboot⟩ := Hp
  have hsh := hshape U hu
  obtain ⟨hplain, hps, hctxs, hdir, hid, ⟨bl, hbl, hbl0⟩, hnp, hune, hiok⟩ := hfacts U hu
  obtain ⟨hname, -, htok, -⟩ := hc
  have hid' : bootGo.id cfg U = id := by unfold bootGo.id; rw [htok, hname]; exact hid
  rw [← hname] at hsh
  subst hps hctxs hdir hid' hboot htok
  have hmem : memBoot γ.boot = bootGo.memMap U cfg.InitialClusterToken' := by
    rw [hbl0]; exact memBoot_bootLog U _ bl hplain hnp hbl
  iapply (letI : MemStorReg GF := ⟨γ.reg⟩
    bootstrapContractF_of_specUnserved hb cfg U γ N addrs hsh (by unfold bootGo.idRaftOk; exact hidr) hune
      hplain hfips hiok hvs ⟨bl, hbl, hbl0⟩ hmem)
  iexact Hpkg

end bridge

end etcdstart
end EtcdGrove
end Perennial
