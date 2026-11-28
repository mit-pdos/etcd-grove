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
    Inv γ ∗ batchEnd rc m x ∗ mainOwnAt r γ rc i s st ⊢ |={⊤}=>
      ∃ (ccfg cfg : Configuration) (cidx li : w64) (ss : List Server),
        r.[Raft, go!"configurations"] ↦ configurations.mk ccfg cidx cfg li ∗
        cfgVal γ ccfg ss ∗ cfgOpt γ cfg ∗ (⌜x < uint.nat cidx⌝ ∨ snapCfg γ x (uint.nat cidx) ss) ∗
        durLb γ i x ∗ applLb rc x ∗ compLb rc x ∗
        (r.[Raft, go!"configurations"] ↦ configurations.mk ccfg cidx cfg li -∗
          mainOwnAt r γ rc i s st) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

end lemmas

end github_com.hashicorp.raft

end Perennial
