/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/leader/MainCfg.lean (241f27e).
-/
/-
(stage 4, package leader, internal) The leader's `mainOwnAt` split for its log appends: the parts
`dispatchLogs` uses (`srvOwn`, `lastLog`, `lastApplied`, `logPend`), the rest (`mainRest`) and the
configurations part (`confOwn`: the `configurations` field, its facts, the commitment's
configuration half, the commit facts). An append of entries that are not configurations keeps
`confOwn` (`confOwn_append_noCfg`); `appendConfigurationEntry` rebuilds it for the new latest
configuration.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.leader.Defs
public import Dsverify.Proof.github_com.hashicorp.raft.leader.DurView

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.hashicorp.raft

open proto gprot

section pure
variable [GooseExts]

theorem take_append_le' (L es : RLog) (n : Nat) (h : n ≤ L.length) : (L ++ es).take n = L.take n := by
  rw [List.take_append_of_le_length h]

/-- Appending entries that are not configurations keeps the latest configuration's servers. -/
theorem cfgIdsOf_append_noCfg (S : List SID) (L es : RLog) (h : ∀ e ∈ es, e.kind ≠ kConfig) :
    cfgIdsOf S (L ++ es) = cfgIdsOf S L := by
  unfold cfgIdsOf
  rw [lastCfgIdx_append_noCfg L es h,
    proto.ent_append_left L es _ (lastCfgIdx_spec L).1]

theorem replCover_append_noCfg (S : List SID) (i : SID) (L es : RLog) (h : ∀ e ∈ es, e.kind ≠ kConfig)
    (m : GMap SID Loc) : replCover S i L m → replCover S i (L ++ es) m := by
  unfold replCover; rw [cfgIdsOf_append_noCfg S L es h]; exact id

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

theorem cfgAtIs_le (γ : GNames) (L : RLog) (p : Nat) (c : Configuration) :
    cfgAtIs (GF := GF) γ L p c ⊢ ⌜p ≤ L.length⌝ := by
  unfold cfgAtIs
  iintro (⟨%hp, -⟩ | ⟨%ss, %e, -, %h⟩)
  · ipureintro; omega
  · ipureintro; exact (proto.ent_le_length h.2.1).2

theorem cfgAtIs_append (γ : GNames) (L es : RLog) (p : Nat) (c : Configuration) :
    cfgAtIs (GF := GF) γ L p c ⊢ cfgAtIs γ (L ++ es) p c := by
  unfold cfgAtIs
  iintro (⟨%hp, #Hs⟩ | ⟨%ss, %e, #Hv, %h⟩)
  · ileft; iframe #; ipureintro; exact hp
  · iright; iexists ss, e; iframe #; ipureintro
    obtain ⟨h1, he, hk, hd⟩ := h
    exact ⟨h1, by rw [proto.ent_append_left _ _ _ (proto.ent_le_length he).2]; exact he, hk, hd⟩

theorem leaderOwnM_mono (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat)
    (P P' : GMap SID Loc → Prop) (L : Nat) (h : ∀ m, P m → P' m) :
    leaderOwnM r γ rc i T P L ⊢ leaderOwnM r γ rc i T P' L := by
  unfold leaderOwnM
  iintro ⟨%cc, %cm, %infl, %fs, %rs, %rmap, %nt, %sd, %n0, H1, H2, H3, H4, H5, H6, H7, H8,
    H9, %H10, H11, H12, H13, H14, H15, H16, H17, H18, %H19, H20⟩
  iexists cc, cm, infl, fs, rs, rmap, nt, sd, n0
  iframe
  ipureintro; exact ⟨H10, h _ H19⟩

/-- `mainOwnAt` of a leader without the parts `dispatchLogs` uses and the configurations part
(hraft_robust: the stable store's view with the staged commit index; no `durView`, which is in `srvDurInv`). -/
def mainRest (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (a : Nat) : IProp GF :=
  iprop(∃ (sst : StableAbs) (lch : Loc) (γl : ChanNames) (bs : List Bool) (c : Nat),
    (∃ g : w64, stVS rc sst g ∗ ⌜uint.nat g ≤ s.dur.1⌝) ∗ ⌜voteMatches sst s⌝ ∗
    ghostVar rc.names.state (1 : Qp).half stLeader ∗
    (∃ m : Nat, pubOwn γ i s.term m ∗ ⌜m ≤ a⌝) ∗
    verifyRegistry γ rc i ∗ fsmProd γ rc a ∗
    ghostVar rc.dur.pend (1 : Qp).half (none : Option (Nat × Nat × GoString)) ∗
    monoNatAuthOwn rc.dur.comp (1 : Qp).half c ∗ ⌜c ≤ a⌝ ∗
    r.[Raft, go!"leaderCh"] ↦□ lch ∗ isChan lch γl Bool ∗ ownChan γl Bool (.Buffered bs) ∗
    ⌜sint.Z γl.chanCap = 1 ∧ bs.length ≤ 1⌝)

/-- The configurations part of a leader's `mainOwnAt` (with the commitment's configuration half and
the commit facts). -/
def confOwn (r : Loc) (γ : GNames) (i : SID) (s : SState) (a : Nat) : IProp GF :=
  iprop(∃ (cfg ccfg : Configuration) (cidx li : w64),
    r.[Raft, go!"configurations"] ↦ configurations.mk ccfg cidx cfg li ∗
    cfgAtIs γ s.log (uint.nat li) cfg ∗ cfgAtIs γ s.log (uint.nat cidx) ccfg ∗
    ⌜uint.nat li = lastCfgIdx s.log ∧
      (cidx = li ∨ (uint.nat cidx = lastCfgIdx (s.log.take (uint.nat li - 1)) ∧ a < uint.nat li))⌝ ∗
    cmtIdx γ s.term s.log (uint.nat cidx) ∗
    ccfgOwn γ i s.term (lastCfgIdx s.log) ∗
    ∃ n0 : Nat, len0Is γ s.term n0 ∗
      (⌜s.cidx ≤ n0⌝ ∨ ∃ k p : Nat, commitIs γ s.term k p ∗ ⌜s.cidx ≤ k⌝) ∗
      (⌜cidx ≠ li ∨ uint.nat li ≤ n0⌝ ∨ ∃ k p : Nat, commitIs γ s.term k p ∗ ⌜uint.nat li ≤ k⌝))

theorem mainRest_log (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (a : Nat)
    (L : RLog) : mainRest r γ rc i { s with log := L } a ⊣⊢ mainRest r γ rc i s a := .rfl

/-- (hraft_robust R4b) The stable store's view (with the staged commit index, durable) out of
`mainRest` and back with another staged index, durable too. -/
theorem mainRest_stV (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (a : Nat) :
    mainRest r γ rc i s a ⊢ ∃ (D : StableAbs) (g : w64), stVS rc D g ∗ ⌜uint.nat g ≤ s.dur.1⌝ ∗
      (∀ g' : w64, stVS rc D g' -∗ ⌜uint.nat g' ≤ s.dur.1⌝ -∗ mainRest r γ rc i s a) := by
  unfold mainRest
  iintro ⟨%sst, %lch, %γl, %bs, %c, ⟨%g, Hst, %Hg⟩, H⟩
  iexists sst, g
  iframe Hst
  isplitr; · ipureintro; exact Hg
  iintro %g' Hst %Hg'
  iexists sst, lch, γl, bs, c
  isplitl [Hst]; · iexists g'; iframe; ipureintro; exact Hg'
  iexact H

/-- (hraft_robust R4b) A leader's `mainOwnAt`, opened: its view `srvV`, `lastLog`, `lastApplied`, `leaderIs`,
the rest and the configurations part. -/
theorem mainOwnAt_lopen (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) :
    mainOwnAt r γ rc i s stLeader ⊢ ∃ a : Nat, srvV rc s ∗ ghostVar rc.dur.pw 1 (none : Option Pend) ∗
      ghostVar rc.names.lastLog (1 : Qp).half (s.log.length, lastTerm s.log) ∗
      monoNatAuthOwn rc.dur.applied (1 : Qp).half a ∗ ⌜a ≤ s.dur.1 ∧ s.cidx ≤ a⌝ ∗
      leaderIs γ s.term i ∗ mainRest r γ rc i s a ∗ confOwn r γ i s a := by
  unfold mainOwnAt mainRest confOwn
  iintro ⟨%a, %sst, %cfg, %ccfg, %cidx, %li, %lch, %γl, %bs, %c, Hsrv, Hpw, HownS, %Hvm, HlastLog,
    Hst, Hldr0, -, Hreg, Happ, %Ha, Hprod, Hpdn, Hcomp, %Hcp, Hconf, #Hcfg, #Hccfg, %Hli,
    #Hcmt, #Hlch, #Hlchan, Hlown, %Hlcap⟩
  icases Hldr0 with (%Hc | ⟨#Hldr, Hpub, Hcc, %n0, #Hn0, Hcix, Hcl⟩)
  · exact absurd rfl Hc
  iexists a
  iframe Hsrv Hpw HlastLog Happ
  isplitr; · ipureintro; exact Ha
  isplitr; · iexact Hldr
  isplitl [HownS Hst Hpub Hreg Hprod Hpdn Hcomp Hlown]
  · iexists sst, lch, γl, bs, c
    iframe; iframe #; ipureintro; exact ⟨Hvm, Hcp, Hlcap⟩
  iexists cfg, ccfg, cidx, li
  iframe; iframe #
  ipureintro; exact Hli

theorem mainOwnAt_lclose (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (a : Nat) :
    srvV rc s ∗ ghostVar rc.dur.pw 1 (none : Option Pend) ∗
      ghostVar rc.names.lastLog (1 : Qp).half (s.log.length, lastTerm s.log) ∗
      monoNatAuthOwn rc.dur.applied (1 : Qp).half a ∗ ⌜a ≤ s.dur.1 ∧ s.cidx ≤ a⌝ ∗
      leaderIs γ s.term i ∗ mainRest r γ rc i s a ∗ confOwn r γ i s a ⊢
      mainOwnAt r γ rc i s stLeader := by
  unfold mainOwnAt mainRest confOwn
  iintro ⟨Hsrv, Hpw, HlastLog, Happ, %Ha, #Hldr,
    ⟨%sst, %lch, %γl, %bs, %c, HownS, %Hvm, Hst, Hpub, Hreg, Hprod, Hpdn, Hcomp, %Hcp, #Hlch,
      #Hlchan, Hlown, %Hlcap⟩,
    ⟨%cfg, %ccfg, %cidx, %li, Hconf, #Hcfg, #Hccfg, %Hli, #Hcmt, Hcc, %n0, #Hn0, Hcix, Hcl⟩⟩
  iexists a, sst, cfg, ccfg, cidx, li, lch, γl, bs, c
  iframe Hsrv Hpw HownS HlastLog Hst Hreg Happ Hprod Hpdn Hcomp Hconf Hlown
  iframe #
  isplitr; · ipureintro; exact Hvm
  isplitl [Hpub Hcc Hcix Hcl]
  · iright; iframe
  ipureintro; exact ⟨Ha, Hcp, Hli, Hlcap⟩

theorem confOwn_intro (r : Loc) (γ : GNames) (i : SID) (s : SState) (a : Nat)
    (cfg ccfg : Configuration) (cidx li : w64) (n0 : Nat)
    (hli : uint.nat li = lastCfgIdx s.log ∧
      (cidx = li ∨ (uint.nat cidx = lastCfgIdx (s.log.take (uint.nat li - 1)) ∧ a < uint.nat li)))
    :
    r.[Raft, go!"configurations"] ↦ configurations.mk ccfg cidx cfg li ∗
      cfgAtIs γ s.log (uint.nat li) cfg ∗ cfgAtIs γ s.log (uint.nat cidx) ccfg ∗
      cmtIdx γ s.term s.log (uint.nat cidx) ∗ ccfgOwn γ i s.term (lastCfgIdx s.log) ∗
      len0Is γ s.term n0 ∗ (⌜s.cidx ≤ n0⌝ ∨ ∃ k p : Nat, commitIs γ s.term k p ∗ ⌜s.cidx ≤ k⌝) ∗
      (⌜cidx ≠ li ∨ uint.nat li ≤ n0⌝ ∨ ∃ k p : Nat, commitIs γ s.term k p ∗ ⌜uint.nat li ≤ k⌝) ⊢
      confOwn (GF := GF) r γ i s a := by
  unfold confOwn
  iintro ⟨Hconf, #Hcfg, #Hccfg, #Hcmt, Hcc, #Hn0, Hcix, Hcl⟩
  iexists cfg, ccfg, cidx, li
  iframe Hconf Hcc
  iframe #
  isplitr; · ipureintro; exact hli
  iframe

/-- An append of entries that are not configurations keeps the configurations part. -/
theorem confOwn_append_noCfg (r : Loc) (γ : GNames) (i : SID) (s : SState) (a : Nat) (es : RLog)
    (hes : ∀ e ∈ es, e.kind ≠ kConfig) :
    confOwn (GF := GF) r γ i s a ⊢ confOwn r γ i { s with log := s.log ++ es } a := by
  unfold confOwn
  iintro ⟨%cfg, %ccfg, %cidx, %li, Hconf, #Hcfg, #Hccfg, %Hli, #Hcmt, Hcc, %n0, #Hn0, Hcix, Hcl⟩
  ihave %Hcle := cfgAtIs_le γ s.log _ ccfg $$ Hccfg
  iexists cfg, ccfg, cidx, li
  iframe Hconf
  simp only
  rw [lastCfgIdx_append_noCfg s.log es hes]
  iframe Hcc
  isplitr; · iapply cfgAtIs_append $$ Hcfg
  isplitr; · iapply cfgAtIs_append $$ Hccfg
  isplitr
  · ipureintro
    refine ⟨Hli.1, ?_⟩
    rw [take_append_le' _ _ _ (by have := (lastCfgIdx_spec s.log).1; omega)]
    exact Hli.2
  isplitr
  · iapply (cmtIdx_mono γ s.term s.term s.log (s.log ++ es) (uint.nat cidx) (Nat.le_refl _)
      (proto.ent_append_left _ _ _ Hcle)) $$ Hcmt
  iframe; iframe #

theorem cfgAtIs_servers (γ : GNames) (L : RLog) (p : Nat) (c : Configuration) :
    cfgAtIs (GF := GF) γ L p c ⊢ ∃ ss : List Server, c.Servers' ↦*□ ss := by
  unfold cfgAtIs cfgVal
  iintro (⟨-, #Hs⟩ | ⟨%ss, %e, ⟨#Hs, -⟩, -⟩)
  · iexists []; iexact Hs
  · iexists ss; iexact Hs

/-- A leader's log has a configuration entry (its commitment's configuration is one of its log's).
(hraft_robust R4b: through the crash invariant, `durFact`.) -/
theorem mainOwnAt_leader_cfg [hRB : ReceiptBoundLe GF (2 ^ 62)] (r : Loc) (γ : GNames) (rc : RCtx GF)
    (i : SID) (s : SState) :
    Inv γ ∗ srvDurInv γ rc i ∗ mainOwnAt r γ rc i s stLeader ⊢ |NC={⊤}=>
      mainOwnAt r γ rc i s stLeader ∗ ⌜1 ≤ lastCfgIdx s.log⌝ := by
  iintro ⟨#HInv, #Hdur, Hm⟩
  ihave ⟨%a, Hsrv, Hpw, HlastLog, Happ, %Ha, #Hldr, Hrest, Hconf⟩ := mainOwnAt_lopen r γ rc i s $$ Hm
  iunfold confOwn at Hconf
  icases Hconf with ⟨%cfg, %ccfg, %cidx, %li, Hconfs, #Hcfg, #Hccfg, %Hli, #Hcmt, Hcc, %n0, #Hn0, Hcix, Hcl⟩
  iapply ncfupd_fupd_l
  imod ccfgOwn_entry γ ⊤ (by solve_ndisj) i s.term (lastCfgIdx s.log) $$ [Hcc] with ⟨Hcc, %e0, #He0, %He0k⟩
  · iframe; iframe #
  imodintro
  iapply ncfupd_wand
  isplitl [Hsrv]
  · iapply durFact γ rc i (E := ⊤) (by solve_ndisj) s iprop(Inv γ ∗ leaderIs γ s.term i ∗ llogIdx γ s.term (lastCfgIdx s.log) e0)
      iprop(⌜ent s.log (lastCfgIdx s.log) = some e0⌝)
    · iintro ⟨⟨#HI, #Hl, #Hx⟩, Hs⟩
      iapply llogIdx_leader γ (⊤ \ ↑durN) gprotN_diff_durN i s (lastCfgIdx s.log) e0
      iframe; iframe #
    iframe; iframe #
  iintro ⟨Hsrv, %Hent0⟩
  isplitl
  · iapply mainOwnAt_lclose r γ rc i s a
    iframe Hsrv Hpw HlastLog Happ Hrest
    iframe #
    isplitr; · ipureintro; exact Ha
    iapply confOwn_intro r γ i s a cfg ccfg cidx li n0 Hli
    iframe; iframe #
  ipureintro; exact (proto.ent_le_length Hent0).1

/-- (HUB-REQUEST L1, proposed) The configurations part of a leader's `mainOwnAt` when its latest
configuration is the committed one (`configurations.committedIndex = latestIndex`, what
`configurationChangeChIfStable` checks). -/
def confOwnSt (r : Loc) (γ : GNames) (i : SID) (s : SState) (a : Nat) : IProp GF :=
  iprop(∃ (cfg ccfg : Configuration) (li : w64),
    r.[Raft, go!"configurations"] ↦ configurations.mk ccfg li cfg li ∗
    cfgAtIs γ s.log (uint.nat li) cfg ∗ cfgAtIs γ s.log (uint.nat li) ccfg ∗
    ⌜uint.nat li = lastCfgIdx s.log⌝ ∗
    cmtIdx γ s.term s.log (uint.nat li) ∗
    ccfgOwn γ i s.term (lastCfgIdx s.log) ∗
    ∃ n0 : Nat, len0Is γ s.term n0 ∗
      (⌜s.cidx ≤ n0⌝ ∨ ∃ k p : Nat, commitIs γ s.term k p ∗ ⌜s.cidx ≤ k⌝) ∗
      (⌜uint.nat li ≤ n0⌝ ∨ ∃ k p : Nat, commitIs γ s.term k p ∗ ⌜uint.nat li ≤ k⌝))

theorem confOwnSt_confOwn (r : Loc) (γ : GNames) (i : SID) (s : SState) (a : Nat) :
    confOwnSt (GF := GF) r γ i s a ⊢ confOwn r γ i s a := by
  unfold confOwnSt confOwn
  iintro ⟨%cfg, %ccfg, %li, Hconf, #Hcfg, #Hccfg, %Hli, #Hcmt, Hcc, %n0, #Hn0, Hcix, Hcl⟩
  iexists cfg, ccfg, li, li
  iframe Hconf Hcc
  iframe #
  isplitr; · ipureintro; exact ⟨Hli, Or.inl rfl⟩
  iframe
  icases Hcl with (%h | Hk)
  · ileft; ipureintro; right; exact h
  · iright; iexact Hk

theorem mainOwnAtSt_open (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) :
    mainOwnAtSt r γ rc i s ⊢ ∃ a : Nat, srvV rc s ∗ ghostVar rc.dur.pw 1 (none : Option Pend) ∗
      ghostVar rc.names.lastLog (1 : Qp).half (s.log.length, lastTerm s.log) ∗
      monoNatAuthOwn rc.dur.applied (1 : Qp).half a ∗ ⌜a ≤ s.dur.1 ∧ s.cidx ≤ a⌝ ∗
      leaderIs γ s.term i ∗ mainRest r γ rc i s a ∗ confOwnSt r γ i s a := by
  unfold mainOwnAtSt mainRest confOwnSt
  iintro ⟨%a, %sst, %cfg, %ccfg, %li, %lch, %γl, %bs, %c, Hsrv, Hpw, HownS, %Hvm, HlastLog,
    Hst, ⟨#Hldr, Hpub, Hcc, %n0, #Hn0, Hcix, Hcl⟩, -, Hreg, Happ, %Ha, Hprod, Hpdn, Hcomp, %Hcp,
    Hconf, #Hcfg, #Hccfg, %Hli, #Hcmt, #Hlch, #Hlchan, Hlown, %Hlcap⟩
  iexists a
  iframe Hsrv Hpw HlastLog Happ
  isplitr; · ipureintro; exact Ha
  isplitr; · iexact Hldr
  isplitl [HownS Hst Hpub Hreg Hprod Hpdn Hcomp Hlown]
  · iexists sst, lch, γl, bs, c
    iframe; iframe #; ipureintro; exact ⟨Hvm, Hcp, Hlcap⟩
  iexists cfg, ccfg, li
  iframe; iframe #
  ipureintro; exact Hli

theorem mainOwnAtSt_close (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (a : Nat) :
    srvV rc s ∗ ghostVar rc.dur.pw 1 (none : Option Pend) ∗
      ghostVar rc.names.lastLog (1 : Qp).half (s.log.length, lastTerm s.log) ∗
      monoNatAuthOwn rc.dur.applied (1 : Qp).half a ∗ ⌜a ≤ s.dur.1 ∧ s.cidx ≤ a⌝ ∗
      leaderIs γ s.term i ∗ mainRest r γ rc i s a ∗ confOwnSt r γ i s a ⊢ mainOwnAtSt r γ rc i s := by
  unfold mainOwnAtSt mainRest confOwnSt
  iintro ⟨Hsrv, Hpw, HlastLog, Happ, %Ha, #Hldr,
    ⟨%sst, %lch, %γl, %bs, %c, HownS, %Hvm, Hst, Hpub, Hreg, Hprod, Hpdn, Hcomp, %Hcp, #Hlch,
      #Hlchan, Hlown, %Hlcap⟩,
    ⟨%cfg, %ccfg, %li, Hconf, #Hcfg, #Hccfg, %Hli, #Hcmt, Hcc, %n0, #Hn0, Hcix, Hcl⟩⟩
  iexists a, sst, cfg, ccfg, li, lch, γl, bs, c
  iframe Hsrv Hpw HownS HlastLog Hst Hreg Happ Hprod Hpdn Hcomp Hconf Hlown
  iframe #
  isplitr; · ipureintro; exact Hvm
  isplitl [Hpub Hcc Hcix Hcl]
  · iframe
  ipureintro; exact ⟨Ha, Hcp, Hli, Hlcap⟩

theorem mainOwnAtSt_mainOwnAt (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) :
    mainOwnAtSt r γ rc i s ⊢ mainOwnAt r γ rc i s stLeader := by
  iintro Hm
  ihave ⟨%a, Hsrv, Hpw, HlastLog, Happ, %Ha, #Hldr, Hrest, Hconf⟩ := mainOwnAtSt_open r γ rc i s $$ Hm
  ihave Hconf := confOwnSt_confOwn r γ i s a $$ Hconf
  iapply mainOwnAt_lclose r γ rc i s a
  iframe; iframe #; ipureintro; exact Ha

end defs

end github_com.hashicorp.raft

end Perennial
