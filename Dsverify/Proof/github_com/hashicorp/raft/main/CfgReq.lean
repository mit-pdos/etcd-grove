/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/main/CfgReq.lean (241f27e).
-/
/-
(stage 3) The main loop's answer to a configurations request (`configurationsCh`, takeSnapshot's
`configurationsFuture`): `c.configurations = r.configurations.Clone(); c.respond(nil)`, in
`runFollower`, `runCandidate` and `leaderLoop`. The answer's facts (`cfgReqQ`): the committed
configuration is the bootstrap one at index 1 (the request's position `x ≥ 1` is the end of an item
sent on `fsmMutateCh`, so `x ≤ lastApplied` and the committed configuration is set), `x` is durable
and at most `lastApplied`, and the compaction frontier is raised to `x`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Configuration__Clone
public import Dsverify.Spec.github_com.hashicorp.raft.deferError__respond
public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws
public import Dsverify.Proof.github_com.hashicorp.raft.DurHelpers

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft

open proto gprot

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- An item end `x` the FSM producer sent is at most its position (an unfold of `fsmProd`). -/
theorem fsmProd_batchEnd_le (γ : GNames) (rc : RCtx GF) (a m x : Nat) :
    fsmProd γ rc a ∗ batchEnd rc m x ⊢ fsmProd γ rc a ∗ ⌜x ≤ a⌝ := by
  unfold fsmProd batchEnd
  iintro ⟨⟨%sent, %M, %e, Hp, Ha, %Hf, Hl, Hn⟩, #Hb⟩
  ihave %Hm := ghost_map_lookup $$ Ha Hb
  isplitl
  · iexists sent, M, e; iframe; ipureintro; exact Hf
  ipureintro
  have := Hf.2.2 m x Hm
  omega

/-- `respond` through `*configurationsFuture` (promoted). -/
theorem deferError.respond_cfgFuture
    (wp_respond : github_com.hashicorp.raft.deferError.respond.spec (GF := GF) (hG := hG))
    (f : Loc) (Q : GoInterface → IProp GF) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
       ((deferResp (f.[configurationsFuture, go!"deferError"]) Q ∗ Q err) ∨
        deferDone (f.[configurationsFuture, go!"deferError"])) }}
      (App (Val (f @!! go.GoType.PointerType configurationsFuture.ty @!! go!"respond")) (Val #err))
    {{ RET #(); deferDone (f.[configurationsFuture, go!"deferError"]) }} := by
  have h := wp_respond (f.[configurationsFuture, go!"deferError"]) Q err
  wp_start as Hpre
  wp_method_call
  have e := MethodUnfold.method_unfold (t := go.GoType.PointerType deferError.ty) (m := go!"respond")
    #(f.[configurationsFuture, go!"deferError"])
  simp only [e] at h
  iapply h $$ [$Hpkg $Hpre] HΦ

/-- `(*configurations).Clone()`: a copy whose configurations' servers are fresh copies. -/
theorem configurations.wp_Clone
    (wp_Clone : github_com.hashicorp.raft.Configuration.Clone.spec (GF := GF) (hG := hG))
    (p : Loc) (cc lc : Configuration) (ci li : w64) (s1 s2 : List Server) (d1 d2 : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
       p ↦ configurations.mk cc ci lc li ∗ cc.Servers' ↦*{d1} s1 ∗ lc.Servers' ↦*{d2} s2 }}
      (App (Val (p @!! go.GoType.PointerType configurations.ty @!! go!"Clone")) (Val #()))
    {{ (cf : configurations), RET #cf; p ↦ configurations.mk cc ci lc li ∗ cc.Servers' ↦*{d1} s1 ∗
        lc.Servers' ↦*{d2} s2 ∗ cf.committed'.Servers' ↦* s1 ∗ ⌜cf.committedIndex' = ci⌝ }} := by
  wp_start as ⟨Hp, Hs1, Hs2⟩
  wp_auto
  icases (configurations.configurations_access_load_committed (GF := GF) _
    (configurations.mk cc ci lc li) (DFrac.own 1)).access_strict $$ Hp with ⟨Hcm, Hcl⟩
  wp_apply wp_Clone $$ [$Hcm $Hs1] as %c1 ⟨Hcm, Hs1, Hc1⟩
  ihave Hp := Hcl $$ Hcm
  wp_auto
  icases (configurations.configurations_access_load_latest (GF := GF) _
    (configurations.mk cc ci lc li) (DFrac.own 1)).access_strict $$ Hp with ⟨Hlt, Hcl⟩
  wp_apply wp_Clone $$ [$Hlt $Hs2] as %c2 ⟨Hlt, Hs2, Hc2⟩
  ihave Hp := Hcl $$ Hlt
  wp_auto
  wp_end

/-- **The answer's facts** from the main goroutine's resources, for a request at `x ≥ 1` (the end of
an item sent on `fsmMutateCh`): `x ≤ lastApplied ≤ dur` and (stage 4) the committed configuration, a
valid one (`x ≥ 1` is past the bootstrap), the committed log's at `x` unless its index is above `x`
(`snapCfg`: `gprot.srvOwn_CLb`, the committed configuration is the latest or its parent while
`lastApplied` is below the latest's index; stage 3: the bootstrap configuration at index 1); the
compaction authority is raised to `max c x ≤ lastApplied`. -/
theorem mainOwnAt_cfgReq [hRB : ReceiptBoundLe GF (2 ^ 62)] (r : Loc) (γ : GNames) (rc : RCtx GF)
    (i : SID) (s : SState) (st : w32) (m x : Nat) (hx : 1 ≤ x) :
    Inv γ ∗ srvDurInv γ rc i ∗ batchEnd rc m x ∗ mainOwnAt r γ rc i s st ⊢ |NC={⊤}=>
      ∃ (ccfg cfg : Configuration) (cidx li : w64) (ss : List Server),
        r.[Raft, go!"configurations"] ↦ configurations.mk ccfg cidx cfg li ∗
        cfgVal γ ccfg ss ∗ cfgOpt γ cfg ∗ (⌜x < uint.nat cidx⌝ ∨ snapCfg γ x (uint.nat cidx) ss) ∗
        durLb γ i x ∗ applLb rc x ∗ compLb rc x ∗
        (r.[Raft, go!"configurations"] ↦ configurations.mk ccfg cidx cfg li -∗
          mainOwnAt r γ rc i s st) := by
  iintro ⟨#HI, #Hdur, #Hb, Hm⟩ Hnc
  unfold mainOwnAt
  icases Hm with ⟨%a, %sst, %cfg, %ccfg, %cidx, %li, %lch, %γl, %bs, %c, Hs, Hpw, HS, %Hvm, Hll, Hst,
    Hstl, -, Hvreg, Happ, %Ha, Hprod, Hpnd, Hcomp, %Hcmp, Hcfgs, #Hli, #Hci, %Hcf, #Hcmt, #Hlch,
    #Hlchan, Hlown, %Hcap⟩
  ihave ⟨Hprod, %Hxa⟩ := fsmProd_batchEnd_le γ rc a m x $$ [$Hprod $Hb]
  ihave H1 := srvOwn_facts_R γ rc i gd_top s $$ [$HI $Hdur $Hs]
  imod H1 $$ Hnc with ⟨Hnc, Hs, -, %Hf⟩
  ihave H2 := srvOwn_CLb_R γ rc i gd_top s $$ [$HI $Hdur $Hs]
  imod H2 $$ Hnc with ⟨Hnc, Hs, #HCL⟩
  imod genesis_facts γ ⊤ (by simp) $$ HI with %Hgen
  -- the log holds the genesis at 1 (`x ≥ 1` is applied, so durable)
  have hlen : x ≤ s.log.length := by have := Hf.2.1; omega
  have hent1 : ent s.log 1 = some γ.g := by
    rcases Hf.1 with h | h
    · rw [h] at hlen; simp at hlen; omega
    · exact h
  have hentk : ∀ y, 1 ≤ y → y ≤ s.log.length → ∃ e, ent s.log y = some e := by
    intro y h1 h2
    unfold ent; rw [if_neg (by omega)]
    exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
  -- the committed configuration's index is positive, and no configuration follows it up to `a`
  have hP : 1 ≤ uint.nat cidx ∧ ∀ y e, uint.nat cidx < y → y ≤ a → ent s.log y = some e →
      e.kind ≠ kConfig := by
    obtain ⟨hli, hc⟩ := Hcf
    rcases hc with heq | ⟨hpar, hal⟩
    · subst heq
      have hsp := lastCfgIdx_spec s.log
      refine ⟨?_, fun y e h1 _ h3 => hsp.2.2 y e (by omega) h3⟩
      apply Nat.pos_of_ne_zero; intro h0
      exact hsp.2.2 1 γ.g (by omega) hent1 Hgen.2.1
    · have hsp := lastCfgIdx_spec (s.log.take (uint.nat li - 1))
      refine ⟨?_, fun y e h1 h2 h3 => hsp.2.2 y e (by omega)
        (by rw [ent_take _ _ _ (by omega)]; exact h3)⟩
      apply Nat.pos_of_ne_zero; intro h0
      exact hsp.2.2 1 γ.g (by omega) (by rw [ent_take _ _ _ (by omega)]; exact hent1) Hgen.2.1
  -- the committed configuration's value
  ihave Hci2 := Hci
  iunfold cfgAtIs at Hci2
  icases Hci2 with (⟨%h0, -⟩ | ⟨%ss, %e, Hval, %He⟩)
  · exfalso; omega
  ihave #Hval' := Hval
  iunfold cfgVal at Hval'
  icases Hval' with ⟨#Hss, %Hok⟩
  ihave #Hopt := cfgOpt_of_cfgAtIs γ s.log (uint.nat li) cfg $$ Hli
  ihave H3 := srvOwn_durLb_R γ rc i gd_top s $$ [$HI $Hdur $Hs]
  imod H3 $$ Hnc with ⟨Hnc, Hs, #Hd⟩
  ihave #Hdx := durLb_mono γ i _ x (by omega) $$ Hd
  ihave #Hal := monoNatLbOwn_get _ _ _ $$ Happ
  ihave #Hax := monoNatLbOwn_le x Hxa $$ Hal
  imod mono_nat_own_update (Nat.max c x) (Nat.le_max_left _ _) $$ Hcomp with ⟨Hcomp, #Hcl⟩
  ihave #Hcx := monoNatLbOwn_le x (Nat.le_max_right _ _) $$ Hcl
  imodintro
  iframe Hnc
  iexists ccfg, cfg, cidx, li, ss
  iframe Hcfgs
  iframe #
  isplitr
  · by_cases hxc : x < uint.nat cidx
    · ileft; ipureintro; exact hxc
    iright
    unfold snapCfg
    isplitr
    · ipureintro; exact ⟨hP.1, by omega, Hok⟩
    isplitr
    · iexists e
      isplitr
      · iapply CLb_idx (γ := γ) (s.log.take s.dur.1) (uint.nat cidx) e
          (by rw [ent_take _ _ _ (by omega)]; exact He.2.1) $$ HCL
      · ipureintro; exact ⟨He.2.2.1, He.2.2.2⟩
    unfold noCfgBetween
    iapply (BigSepL.bigSepL_intro (P := iprop(□ CLb γ (s.log.take s.dur.1))) ?_) $$ HCL
    intro k y hk
    iintro #H
    have hy := List.mem_range'.1 (List.mem_of_getElem? hk)
    obtain ⟨e', he'⟩ := hentk y (by omega) (by omega)
    iexists e'
    isplitr
    · iapply CLb_idx (γ := γ) (s.log.take s.dur.1) y e'
        (by rw [ent_take _ _ _ (by omega)]; exact he') $$ H
    · ipureintro; exact hP.2 y e' (by omega) (by omega) he'
  isplitr; · unfold applLb; iexact Hax
  isplitr; · unfold compLb; iexact Hcx
  iintro Hcfgs
  iexists a, sst, cfg, ccfg, cidx, li, lch, γl, bs, Nat.max c x
  iframe
  iframe #
  ipureintro
  exact ⟨Hvm, Ha, Nat.max_le.2 ⟨Hcmp, Hxa⟩, Hcf, Hcap⟩

end lemmas

end github_com.hashicorp.raft

end Perennial
