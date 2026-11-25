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

/-! ## The boot log's members, decoded (claim #34's final stage, 2026-11-25, B2)

With the JSON round trip (`bootGo.ccMemberOf_memberJSON`, `ccContextOf_memberJSON`: #24 J2, lean
`74c7458210`), the members the bootstrap log's conf changes add are Go's (`bootGo.memMap`), and each
of its entries is a conf change the server takes (`BootCore.cc`), when the initial cluster's URLs are
plain (`bootGo.bootURLsPlain`) and so are its names (`bootNamesPlain`). Pure, at any `U`. -/

section pure
variable [GooseExts]

/-- **The initial cluster's names are plain** (`JsonScan.plainEnc` bytes, which encoding/json writes as
they are): with plain URLs, what makes each member's JSON decode back to it. -/
def bootNamesPlain (U : BootURLs) : Prop :=
  ∀ k, (U.initMap.lookup k).isSome → ∀ c ∈ k, JsonScan.plainEnc c

theorem hostByte_plainEnc (c : w8) (h : http.hostByteNoEscape c) : JsonScan.plainEnc c := by
  unfold http.hostByteNoEscape at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem httpPfx_plainEnc : ∀ c ∈ (go!"http://" : List w8), JsonScan.plainEnc c := by
  decide

/-- **A member of the initial cluster is plain** (`membership.memberPlain`): its name by
`bootNamesPlain`, its peer URLs `http://` and a host of `hostByteNoEscape` bytes, no client URL. -/
theorem memberPlain_memberOf (U : BootURLs) (token name : GoString)
    (hpl : bootGo.bootURLsPlain U) (hk : (U.initMap.lookup name).isSome)
    (hn : ∀ c ∈ name, JsonScan.plainEnc c) :
    membership.memberPlain (bootGo.memberOf U token name) := by
  unfold membership.memberPlain
  refine ⟨hn, ?_, ?_⟩
  · intro s hs c hc
    have hs' : s ∈ (U.initURLs name).map bootGo.urlStr := hs
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hs'
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hh⟩ := hpl name hk u hu
    have hc' : c ∈ (go!"http://" : List w8) ++ u.Host' := hc
    rcases List.mem_append.1 hc' with hc'' | hc''
    · exact httpPfx_plainEnc c hc''
    · exact hostByte_plainEnc c (hh c hc'')
  · intro s hs
    have hs' : s ∈ ([] : List GoString) := hs
    simp at hs'

/-- The members are the initial cluster's entries'. -/
theorem mem_members (U : BootURLs) (token : GoString) (m : apply.MemberM)
    (hm : m ∈ bootGo.members U token) :
    ∃ k, (U.initMap.lookup k).isSome ∧ m = bootGo.memberOf U token k := by
  unfold bootGo.members at hm
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ((List.mergeSort_perm _ _).mem_iff.1 hm)
  exact ⟨k, (GMap.mem_dom_list _ _).1 hk, rfl⟩

theorem members_plain (U : BootURLs) (token : GoString) (hpl : bootGo.bootURLsPlain U)
    (hnp : bootNamesPlain U) : ∀ m ∈ bootGo.members U token, membership.memberPlain m := by
  intro m hm
  obtain ⟨k, hk, rfl⟩ := mem_members U token m hm
  exact memberPlain_memberOf U token k hpl hk (hnp k hk)

/-- The bootstrap log's conf change for member `m`. -/
abbrev bootCC (m : apply.MemberM) : ConfChangeM := ⟨W32 0, m.id, bootGo.memberJSON m, W64 0⟩

/-- **The bootstrap log decodes to the members' conf changes**, in `ps` order (`BootLog`'s
`MarshalsConfChange`, at Go's peers and contexts). -/
theorem bootLog_decode (U : BootURLs) (token : GoString) (bl : List LogEntry)
    (hbl : BootLog (bootGo.ps U token) (bootGo.ctxs U token) bl) :
    (LogEntry.toEntries bl 0).map (fun e => ccDecodeV1 e.Data') =
      (bootGo.members U token).map (fun m => some (bootCC m)) := by
  obtain ⟨hlen, -, hent⟩ := hbl
  apply List.ext_getElem
  · simp only [LogEntry.toEntries, List.length_map, List.length_mapIdx, hlen, bootGo.ps]
  · intro i h1 h2
    have hi : i < bl.length := by simpa [LogEntry.toEntries] using h1
    have hi' : i < (bootGo.members U token).length := by simpa using h2
    obtain ⟨id, ctx, hid, hctx, -, -, hm⟩ := hent i bl[i] (List.getElem?_eq_getElem hi)
    simp only [bootGo.ps, bootGo.ctxs, List.getElem?_map, List.getElem?_eq_getElem hi',
      Option.map_some, Option.some.injEq] at hid hctx
    subst hid hctx
    simpa [LogEntry.toEntries, LogEntry.toEntryM, MarshalsConfChange, bootCC] using hm

/-- `memBoot`'s step on a decoded entry. -/
def memBootStep (mem : GMap w64 apply.MemberM) (o : Option ConfChangeM) :
    GMap w64 apply.MemberM :=
  match o with
  | some cc => mem.insert cc.nodeId (membership.ccMemberAt cc)
  | none => mem

theorem memBoot_eq_step (l : List EntryM) :
    memBoot l = (l.map (fun e => ccDecodeV1 e.Data')).foldl memBootStep ∅ := by
  rw [List.foldl_map]; rfl

theorem foldl_congr_mem {α β : Type} (f g : β → α → β) :
    ∀ (l : List α) (b : β), (∀ a ∈ l, ∀ x, f x a = g x a) → l.foldl f b = l.foldl g b
  | [], _, _ => rfl
  | a :: l, b, h => by
      simp only [List.foldl_cons]
      rw [h a (by simp) b]
      exact foldl_congr_mem f g l _ (fun a' ha' => h a' (by simp [ha']))

/-- **The bootstrap log's members are Go's** (`bootstrap.spec`'s `Hmem`): at Go's peers and contexts,
with plain URLs and names. -/
theorem memBoot_bootLog (U : BootURLs) (token : GoString) (bl : List LogEntry)
    (hpl : bootGo.bootURLsPlain U) (hnp : bootNamesPlain U)
    (hbl : BootLog (bootGo.ps U token) (bootGo.ctxs U token) bl) :
    memBoot (LogEntry.toEntries bl 0) = bootGo.memMap U token := by
  have hplain := members_plain U token hpl hnp
  rw [memBoot_eq_step, bootLog_decode U token bl hbl, List.foldl_map]
  unfold bootGo.memMap
  refine foldl_congr_mem _ _ _ _ (fun m hm x => ?_)
  show x.insert m.id (membership.ccMemberAt (bootCC m)) = x.insert m.id m
  have hc : membership.ccMemberAt (bootCC m) = m :=
    (congrArg (fun r : apply.MemberM => { r with id := m.id })
      (bootGo.ccMemberOf_memberJSON m (hplain m hm))).trans rfl
  rw [hc]

/-- **Each bootstrap entry is a conf change the server takes** (`BootCore.cc`): at Go's peers and
contexts, with plain URLs and names. -/
theorem bootCC_ok (U : BootURLs) (token : GoString) (bl : List LogEntry)
    (hpl : bootGo.bootURLsPlain U) (hnp : bootNamesPlain U)
    (hbl : BootLog (bootGo.ps U token) (bootGo.ctxs U token) bl) :
    ∀ e ∈ LogEntry.toEntries bl 0, ccIdOf e.Data' = W64 0 ∧
      ccBootOk (GMap.listToSet (bootGo.ps U token)) e.Data' := by
  intro e he
  have hd := List.mem_map_of_mem (f := fun e : EntryM => ccDecodeV1 e.Data') he
  rw [bootLog_decode U token bl hbl] at hd
  obtain ⟨m, hm, hme⟩ := List.mem_map.1 hd
  have hdec : ccDecodeV1 e.Data' = some (bootCC m) := hme.symm
  have hmp := members_plain U token hpl hnp m hm
  refine ⟨by simp only [ccIdOf, hdec, bootCC], ?_⟩
  unfold ccBootOk
  intro c hc
  rw [hdec, Option.some.injEq] at hc
  subst hc
  obtain ⟨k, -, rfl⟩ := mem_members U token m hm
  unfold ccApplyOk
  refine ⟨rfl, ?_, bootGo.ccContextOf_memberJSON _ hmp, ?_⟩
  · exact (GMap.elem_of_list_to_set _ _).2 (List.mem_map_of_mem (f := (·.id)) hm)
  · exact (congrArg (fun r : apply.MemberM => r.isLearner)
      (bootGo.ccMemberOf_memberJSON _ hmp)).trans rfl

end pure

section bridge
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`bootstrapContract` at Go's values, from `bootstrap.spec`**: for raft names `γ` meeting the
spec's conditions, the contract's triple is the spec's with `isPkgInit` framed from the context.
(Claim #34's final stage, 2026-11-25) The spec's premise `cfg.UnsafeNoFsync' = false` comes from the
contract's precondition (`bootCfgOk`'s last conjunct since that day). -/
theorem bootstrapContract_of_spec [ThreadBoundLe GF (2 ^ 29)] [ReceiptBoundLe GF (2 ^ 60)]
    [MemStorReg GF]
    (hb : _root_.Perennial.EtcdGrove.bootstrap.spec (GF := GF) (hG := hG))
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft) (N : Nat)
    (hidr : bootGo.idRaftOk cfg U) (hune : bootGo.urlsNe U)
    (hplain : bootGo.bootURLsPlain U) (hfips : crypto.fips140.GodebugFips140Off)
    (hiok : bootGo.initMapOk U cfg.InitialClusterToken')
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
  icases Hpre with ⟨%Hpure, Hrest⟩
  have hnf : cfg.UnsafeNoFsync' = false := by
    obtain ⟨⟨-, -, -, -, -, -, h⟩, -⟩ := Hpure; exact h
  iapply (hb cfg U γ N hnf hidr hune hplain hfips hiok hvs hbl hmem) $$ [Hrest] HΦ
  isplitr
  · iexact Hpkg
  · isplitr
    · ipureintro; exact Hpure
    · iexact Hrest

/-- **`bootPremise` from `bootstrap.spec`** (see the file header): for member `name` of the cluster
with token `token`, at the peers `ps`, bootstrap log `bootLog`, contexts `ctxs`, directory `dir` and
id `id`, when, for every URLs `U` the example admits (`Uok`), these are Go's (`bootGo.*` at `token`
and `name`), the initial cluster's URLs are plain, the bootstrap log is the node API's log of `ps`
and `ctxs` (`BootLog`), and the initial cluster's names are plain (`bootNamesPlain`: then the log's
members are the cluster's, `memBoot_bootLog`, the spec's `Hmem`; until 2026-11-25, B2, `Hmem` itself); and (claim #34
stages 2 and 4, 2026-11-25, `bootstrap.spec`'s newer premises) the URLs' facts `urlsNe`/`initMapOk`, the id
not one of raft's local targets, and the `fips140` GODEBUG setting off. (Until 2026-11-25 also `UnsafeNoFsync` off at every
configuration the example admits, `hnf`; now the contract's precondition says it, `bootCfgOk`.) -/
theorem bootPremise_of_spec [ThreadBoundLe GF (2 ^ 29)] [ReceiptBoundLe GF (2 ^ 60)]
    (hb : ∀ [MemStorReg GF], _root_.Perennial.EtcdGrove.bootstrap.spec (GF := GF) (hG := hG))
    (N : Nat) (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8))
    (dir : w64 → List GoString) (token name : GoString) (Uok : BootURLs → Prop) (id : w64)
    (hfips : crypto.fips140.GodebugFips140Off)
    (hidr : id ≠ W64 18446744073709551615 ∧ id ≠ W64 18446744073709551614)
    (hfacts : ∀ U, Uok U →
      bootGo.bootURLsPlain U ∧ bootGo.ps U token = ps ∧ bootGo.ctxs U token = ctxs ∧
        bootGo.dir U token = dir ∧ (bootGo.memberOf U token name).id = id ∧
        (∃ bl : List LogEntry, BootLog ps ctxs bl ∧ bootLog = LogEntry.toEntries bl 0) ∧
        bootNamesPlain U ∧ bootGo.urlsNe U ∧ bootGo.initMapOk U token) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ⊢
      bootPremise (GF := GF) N ps bootLog ctxs dir token name Uok id := by
  iintro #Hpkg
  iunfold bootPremise
  imodintro
  iintro %cfg %U %γ %Hp
  obtain ⟨hc, hu, hvs, -, hboot⟩ := Hp
  obtain ⟨hplain, hps, hctxs, hdir, hid, ⟨bl, hbl, hbl0⟩, hnp, hune, hiok⟩ := hfacts U hu
  obtain ⟨hname, -, htok, -⟩ := hc
  have hid' : bootGo.id cfg U = id := by unfold bootGo.id; rw [htok, hname]; exact hid
  subst hps hctxs hdir hid' hboot htok
  have hmem : memBoot γ.boot = bootGo.memMap U cfg.InitialClusterToken' := by
    rw [hbl0]; exact memBoot_bootLog U _ bl hplain hnp hbl
  iapply (letI : MemStorReg GF := ⟨γ.reg⟩
    bootstrapContract_of_spec hb cfg U γ N (by unfold bootGo.idRaftOk; exact hidr) hune hplain hfips hiok
      hvs ⟨bl, hbl, hbl0⟩ hmem)
  iexact Hpkg

end bridge

end etcdstart
end EtcdGrove
end Perennial
