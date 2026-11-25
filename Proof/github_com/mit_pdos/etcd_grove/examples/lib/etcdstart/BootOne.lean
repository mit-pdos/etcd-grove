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
its directory `dir1 peer id`, the entry's member id `id`, and the URLs plain, not empty and fitting
(`bootURLsPlain`, `urlsNe`, `initMapOk`). (2026-11-25: until then also the log's members, `memBoot
(LogEntry.toEntries boot 0) = bootGo.memMap U name`, stated through `membership.ccMemberOf`, opaque
when it was written; it is now derived, `memBoot_one`, from the log, the contexts and the member's plain
name and URLs.) -/
structure BootGo1 (name peer client : GoString) (id : w64) (ctxs : List (List w8))
    (boot : List LogEntry) : Prop where
  idRaft : id ≠ W64 18446744073709551615 ∧ id ≠ W64 18446744073709551614
  log : BootLog [id] ctxs boot
  go : ∀ U : BootURLs, urls1 name peer client U →
    bootGo.bootURLsPlain U ∧ bootGo.ps U name = [id] ∧ bootGo.ctxs U name = ctxs ∧
      bootGo.dir U name = dir1 peer id ∧ (bootGo.memberOf U name name).id = id ∧
      bootGo.urlsNe U ∧ bootGo.initMapOk U name

/-- A byte a plain URL host keeps (`http.hostByteNoEscape`) is one `encoding/json` writes as it is. -/
theorem plainEnc_of_hostByte (c : w8) (h : http.hostByteNoEscape c) : JsonScan.plainEnc c := by
  unfold http.hostByteNoEscape at h
  omega

/-- The string of a plain root URL (`http://host`) is plain JSON string bytes. -/
theorem urlStr_plainEnc (u : _root_.Perennial.net.url.URL) (h : http.urlRootPlain u) :
    ∀ c ∈ bootGo.urlStr u, JsonScan.plainEnc c := by
  intro c hc
  unfold bootGo.urlStr at hc
  rcases List.mem_append.1 hc with hc | hc
  · have hs : ∀ c ∈ (go!"http://" : GoString), JsonScan.plainEnc c := by decide
    exact hs c hc
  · exact plainEnc_of_hostByte c (h.2.2.2.2.2.2.2.2.2.2.2 c hc)

/-- **The bootstrap log's members are the cluster's, at one member** (2026-11-25; until then a
conjunct of `BootGo1`): the log of the one peer `id` with the contexts Go computes (`bootGo.ctxs`, the
JSON of the members) decodes (`memBoot`, through `ccMemberOf`'s definition) to the cluster's map, when
the member's name and URLs are plain (`ccMemberOf_memberJSON`). -/
theorem memBoot_one (U : BootURLs) (name : GoString) (id : w64) (ctxs : List (List w8))
    (boot : List LogEntry) (hname : ∀ c ∈ name, JsonScan.plainEnc c)
    (hmap : ∃ sl : GoSlice, U.initMap = GMap.insert name sl ∅)
    (hplain : bootGo.bootURLsPlain U)
    (hps : bootGo.ps U name = [id]) (hctxs : bootGo.ctxs U name = ctxs)
    (hlog : BootLog [id] ctxs boot) :
    memBoot (LogEntry.toEntries boot 0) = bootGo.memMap U name := by
  obtain ⟨sl, hsl⟩ := hmap
  -- the one member
  obtain ⟨m, hm, hmid⟩ : ∃ m, bootGo.members U name = [m] ∧ m.id = id := by
    unfold bootGo.ps at hps
    exact List.map_eq_singleton_iff.1 hps
  have hmem : m ∈ U.initMap.domList.map (bootGo.memberOf U name) := by
    have h1 : m ∈ bootGo.members U name := by rw [hm]; exact List.mem_singleton_self m
    unfold bootGo.members at h1
    exact List.mem_mergeSort.1 h1
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hmem
  have hkS : (U.initMap.lookup k).isSome := (GMap.mem_dom_list _ k).1 hk
  have hk' : k = name := by
    have h2 := hkS
    rw [hsl] at h2
    rcases (GMap.lookup_insert_is_Some _ _ _ _).1 h2 with h | ⟨_, h⟩
    · exact h.symm
    · simp at h
  subst hk'
  have hpl : membership.memberPlain (bootGo.memberOf U k k) := by
    refine ⟨hname, ?_, ?_⟩
    · intro u hu c hc
      simp only [bootGo.memberOf, List.mem_map] at hu
      obtain ⟨v, hv, rfl⟩ := hu
      exact urlStr_plainEnc v (hplain k hkS v hv) c hc
    · intro u hu
      simp [bootGo.memberOf] at hu
  -- the log's one entry
  obtain ⟨hlen, -, hents⟩ := hlog
  obtain ⟨e, rfl⟩ : ∃ e, boot = [e] := by
    rcases boot with _ | ⟨e, _ | ⟨f, t⟩⟩
    · simp at hlen
    · exact ⟨e, rfl⟩
    · simp at hlen
  obtain ⟨id', ctx, hid', hctx, -, -, hdec⟩ := hents 0 e rfl
  have hid'' : id' = id := by simpa using hid'.symm
  have hctx' : ctx = bootGo.memberJSON (bootGo.memberOf U k k) := by
    rw [← hctxs] at hctx
    unfold bootGo.ctxs at hctx
    rw [hm] at hctx
    simpa using hctx.symm
  subst hid'' hctx'
  have hdec' : ccDecodeV1 e.data =
      some ⟨W32 0, (bootGo.memberOf U k k).id, bootGo.memberJSON (bootGo.memberOf U k k), W64 0⟩ := by
    rw [hmid]; exact hdec
  unfold memBoot bootGo.memMap
  rw [hm]
  simp only [LogEntry.toEntries, List.mapIdx_cons, List.mapIdx_nil, List.foldl_cons, List.foldl_nil,
    LogEntry.toEntryM, hdec', membership.ccMemberAt, bootGo.ccMemberOf_memberJSON _ hpl]

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
    (hnp : ∀ c ∈ name, JsonScan.plainEnc c)
    (hfips : crypto.fips140.GodebugFips140Off) (hf : BootGo1 name peer client id ctxs boot) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ⊢
      premises (GF := GF) name peer client N id ctxs boot := by
  iintro #Hpkg
  iunfold premises
  imodintro
  iintro %cfg %U %γ %Hp
  obtain ⟨hc, hu, hvs, -, hboot⟩ := Hp
  obtain ⟨hname, -, htok, -, -, -, hnf⟩ := hc
  obtain ⟨hplain, hps, hctxs, hdir, hid, hune, hiok⟩ := hf.go U hu
  obtain ⟨-, -, ⟨sl, hsl⟩, hiu⟩ := hu
  have hmem : memBoot (LogEntry.toEntries boot 0) = bootGo.memMap U name :=
    memBoot_one U name id ctxs boot hnp ⟨sl, hsl⟩ hplain hps hctxs hf.log
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
