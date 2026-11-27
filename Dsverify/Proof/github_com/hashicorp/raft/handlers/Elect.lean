/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/handlers/Elect.lean (241f27e).
-/
/-
Shared lemmas of the election-path proofs (stage 4: preElectSelf, electSelf, runCandidate,
runFollower, requestVote, requestPreVote): access to the latest configuration's servers at any
latest index, and the facts of a configuration that is empty or valid.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws
public import Dsverify.Spec.github_com.hashicorp.raft.deferError__respond

@[expose] public section

set_option linter.unusedVariables false

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

/-- Access to `r.configurations.latest.Servers` in the `configurations` field (any latest index). -/
theorem cfgsServers_acc' (r : Loc) (ccfg cfg : Configuration) (cidx li : w64) (dq : DFrac) :
    (r.[Raft, go!"configurations"] ↦{dq} configurations.mk ccfg cidx cfg li : IProp GF) ⊢
      r.[Raft, go!"configurations"].[configurations, go!"latest"].[Configuration, go!"Servers"] ↦{dq}
        cfg.Servers' ∗
      (r.[Raft, go!"configurations"].[configurations, go!"latest"].[Configuration, go!"Servers"] ↦{dq}
        cfg.Servers' -∗
        r.[Raft, go!"configurations"] ↦{dq} configurations.mk ccfg cidx cfg li) := by
  iintro H
  icases (configurations.configurations_access_load_latest (GF := GF) _
    (configurations.mk ccfg cidx cfg li) dq).access_strict $$ H with ⟨H1, Hc1⟩
  icases (Configuration.Configuration_access_load_Servers (GF := GF) _ cfg dq).access_strict $$ H1
    with ⟨H2, Hc2⟩
  iframe H2
  iintro H2
  iapply Hc1
  iapply Hc2 $$ H2

/-- The facts of an empty-or-valid configuration's servers the election loops use. -/
def srvsFacts (γ : GNames) (ss : List Server) : Prop :=
  (∀ sv ∈ ss, sv.ID' ∈ γ.srvs ∧ sv.Address' = sv.ID') ∧ ss.length < 2 ^ 32 ∧ (srvIds ss).Nodup

theorem srvsFacts_of (γ : GNames) (ss : List Server) (h : ss = [] ∨ srvsOk γ ss) :
    srvsFacts γ ss := by
  rcases h with h | h
  · subst h; exact ⟨by simp, by simp, by simp [srvIds]⟩
  · refine ⟨fun sv hsv => ⟨h.2.1 _ (List.mem_map_of_mem hsv), (h.2.2.1 sv hsv).2.1⟩, h.2.2.2.2, h.1⟩

/-- The latest configuration (`cfgAtIs`) as an empty-or-valid list of servers. -/
theorem cfgAtIs_srvs (γ : GNames) (L : RLog) (p : Nat) (c : Configuration) :
    cfgAtIs (GF := GF) γ L p c ⊢ ∃ ss : List Server, c.Servers' ↦*□ ss ∗ ⌜srvsFacts γ ss⌝ := by
  iintro #H
  ihave #Ho := cfgOpt_of_cfgAtIs γ L p c $$ H
  unfold cfgOpt
  icases Ho with ⟨%ss, #Hs, %Hok⟩
  iexists ss; iframe #; ipureintro; exact srvsFacts_of γ ss Hok

/-- The latest configuration (`cfgAtIs` at `lastCfgIdx L`): its servers, empty or valid, whose voters
are the protocol's `cfgOfC γ.cv L`. -/
theorem cfgAtIs_srvsV (γ : GNames) (L : RLog) (p : Nat) (c : Configuration) (hcv : γ.cv = cfgDec γ.srvs)
    (hp : p = lastCfgIdx L) :
    cfgAtIs (GF := GF) γ L p c ⊢
      ∃ ss : List Server, c.Servers' ↦*□ ss ∗ ⌜srvsFacts γ ss ∧ cfgOfC γ.cv L = srvVoters ss⌝ := by
  subst hp
  iintro #H
  icases cfgAtIs_voters γ L _ c hcv $$ H with ⟨%ss, #Hs, %Hok⟩
  iexists ss; iframe #; ipureintro
  refine ⟨srvsFacts_of γ ss ?_, Hok.1⟩
  rcases Nat.eq_zero_or_pos (lastCfgIdx L) with h | h
  · exact Or.inl (Hok.2.1 h)
  · exact Or.inr (Hok.2.2 h)

theorem srvVoters_take_succ (ss : List Server) (k : Nat) (sv : Server) (h : ss[k]? = some sv) (j : SID) :
    j ∈ srvVoters (ss.take (k + 1)) ↔ j ∈ srvVoters (ss.take k) ∨ (sv.Suffrage' = W64 0 ∧ j = sv.ID') := by
  unfold srvVoters
  rw [List.take_add_one, h]
  simp only [Option.toList_some, List.filter_append, List.map_append, List.mem_append]
  constructor
  · rintro (h1 | h1)
    · exact Or.inl h1
    · right
      by_cases hs : sv.Suffrage' = W64 0
      · simp [hs] at h1; exact ⟨hs, h1⟩
      · exfalso; simp [hs] at h1; obtain ⟨a, ⟨rfl, h2⟩, -⟩ := h1; exact hs h2
  · rintro (h1 | ⟨hs, rfl⟩)
    · exact Or.inl h1
    · right; simp [hs]

theorem srvVoters_take_succ_not (ss : List Server) (k : Nat) (sv : Server) (h : ss[k]? = some sv)
    (hs : sv.Suffrage' ≠ W64 0) (j : SID) :
    j ∈ srvVoters (ss.take (k + 1)) ↔ j ∈ srvVoters (ss.take k) := by
  rw [srvVoters_take_succ ss k sv h]
  constructor
  · rintro (h1 | ⟨h1, -⟩); exact h1; exact absurd h1 hs
  · intro h1; exact Or.inl h1

theorem srvVoters_sub_ids (ss : List Server) (j : SID) (h : j ∈ srvVoters ss) : j ∈ srvIds ss := by
  unfold srvVoters at h; unfold srvIds
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
  exact List.mem_map_of_mem ((List.mem_filter.1 hx).1)

/-- A voter of a protocol configuration (decoded by `γ.cv = cfgDec γ.srvs`) is a server. -/
theorem mem_cfgOfC_srvs (γ : GNames) (hcv : γ.cv = cfgDec γ.srvs) (L : RLog) (j : SID)
    (h : j ∈ cfgOfC γ.cv L) : j ∈ γ.srvs := by
  unfold cfgOfC cfgAtC at h
  split at h
  · rename_i e _
    rw [hcv] at h
    obtain ⟨ss, hd, hok⟩ := cfgDec_valid γ.srvs e.data (List.ne_nil_of_mem h)
    rw [hd, cfgDec_encode _ _ hok] at h
    exact hok.2.1 _ (srvVoters_sub_ids _ _ h)
  · simp at h

theorem srvVoters_length_le (ss : List Server) : (srvVoters ss).length ≤ ss.length := by
  unfold srvVoters; rw [List.length_map]; exact List.length_filter_le _ _

theorem srvVoters_not_take (ss : List Server) (k : Nat) (sv : Server) (hnd : (srvIds ss).Nodup)
    (h : ss[k]? = some sv) : (sv.ID' : SID) ∉ srvVoters (ss.take k) := by
  intro hm
  have h1 := srvVoters_sub_ids _ _ hm
  have hk : (srvIds ss)[k]? = some (sv.ID' : SID) := by
    unfold srvIds; rw [List.getElem?_map, h]; rfl
  have h2 : (sv.ID' : SID) ∈ (srvIds ss).take k := by
    unfold srvIds at h1 ⊢; rw [← List.map_take]; exact h1
  have hm2 : (sv.ID' : SID) ∈ (srvIds ss).drop k := by
    rw [List.mem_iff_getElem?]; exact ⟨0, by rw [List.getElem?_drop]; simpa using hk⟩
  have hnd' := hnd
  rw [← List.take_append_drop k (srvIds ss), List.nodup_append] at hnd'
  exact hnd'.2.2 _ h2 _ hm2 rfl

theorem srvVoters_mem (ss : List Server) (k : Nat) (sv : Server) (h : ss[k]? = some sv)
    (hs : sv.Suffrage' = W64 0) : (sv.ID' : SID) ∈ srvVoters ss := by
  unfold srvVoters
  exact List.mem_map_of_mem (List.mem_filter.2 ⟨List.mem_of_getElem? h, by simp [hs]⟩)


/-- `respond` through `*configurationChangeFuture` (promoted twice: its `logFuture`'s
`deferError`). -/
theorem deferError.respond_ccFuture
    (wp_respond : github_com.hashicorp.raft.deferError.respond.spec (GF := GF) (hG := hG))
    (f : Loc) (Q : GoInterface → IProp GF) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
       ((deferResp ((f.[configurationChangeFuture, go!"logFuture"]).[logFuture, go!"deferError"]) Q ∗ Q err) ∨
        deferDone ((f.[configurationChangeFuture, go!"logFuture"]).[logFuture, go!"deferError"])) }}
      (App (Val (f @!! go.GoType.PointerType configurationChangeFuture.ty @!! go!"respond")) (Val #err))
    {{ RET #(); deferDone ((f.[configurationChangeFuture, go!"logFuture"]).[logFuture, go!"deferError"]) }} := by
  have h := wp_respond ((f.[configurationChangeFuture, go!"logFuture"]).[logFuture, go!"deferError"]) Q err
  wp_start as Hpre
  wp_method_call
  wp_pures
  wp_method_call
  have e := MethodUnfold.method_unfold (t := go.GoType.PointerType deferError.ty) (m := go!"respond")
    #((f.[configurationChangeFuture, go!"logFuture"]).[logFuture, go!"deferError"])
  simp only [e] at h
  iapply h $$ [$Hpkg $Hpre] HΦ


end lemmas

end github_com.hashicorp.raft

end Perennial
