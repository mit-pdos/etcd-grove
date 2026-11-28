/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__appendEntries.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).appendEntries`: the protocol steps of a follower handling a valid
AppendEntries request — `setTerm` (at the `currentTerm` store), `truncate` (at the log store's
`DeleteRange`), `followerStore` (at `StoreLogs`), `ack` (before responding success),
`learnCommit` + `setCidx` (at `setCommitIndex`, up to the last index the request vouches for).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__appendEntries
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__getRPCHeader
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getCurrentTerm
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastIndex
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getState
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setState
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setCurrentTerm
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setLeader
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastEntry
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastLog
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__setLastLog
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__tryStageCommitIndex
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__processConfigurationLogEntry
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getCommitIndex
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__setCommitIndex
public import Dsverify.Spec.github_com.hashicorp.raft.min
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setCommittedConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setLatestConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__processLogs
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setLastContact
public import Dsverify.Spec.github_com.hashicorp.raft.RPC__Respond
public import Dsverify.Proof.github_com.hashicorp.raft.handlers.Base
public import Dsverify.Proof.github_com.hashicorp.raft.handlers.CfgLog
public import Perennial.Spec.sync.atomic.Bool__Load

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft proto gprot

namespace github_com.hashicorp.raft
namespace aeCfg

/-- The leader arm of `mainOwnAt` (state `st`, term `T`, log `L`, commit index `c`, FSM position
`a`, the configurations' indexes `cidx`, `li`). -/
def stArm (γ : GNames) (i : SID) (st : w32) (T : Nat) (L : RLog) (c a : Nat) (cidx li : w64) :
    IProp GF :=
  iprop(⌜st ≠ stLeader⌝ ∨ leaderIs γ T i ∗ (∃ m : Nat, pubOwn γ i T m ∗ ⌜m ≤ a⌝) ∗
      ccfgOwn γ i T (lastCfgIdx L) ∗
      ∃ n0 : Nat, len0Is γ T n0 ∗
        (⌜c ≤ n0⌝ ∨ ∃ k p : Nat, commitIs γ T k p ∗ ⌜c ≤ k⌝) ∗
        (⌜cidx ≠ li ∨ uint.nat li ≤ n0⌝ ∨ ∃ k p : Nat, commitIs γ T k p ∗ ⌜uint.nat li ≤ k⌝))

/-- The persistent facts of the `configurations` field over the log `L` scanned up to `n`
(`mainOwnAt`'s at `n = |L|`). -/
def cfgFacts (γ : GNames) (L : RLog) (n a T : Nat) (cfg ccfg : Configuration) (cidx li : w64) :
    IProp GF :=
  iprop(cfgAtIs γ L (uint.nat li) cfg ∗ cfgAtIs γ L (uint.nat cidx) ccfg ∗
    ⌜uint.nat li = lastCfgIdx (L.take n) ∧
      (cidx = li ∨ (uint.nat cidx = lastCfgIdx (L.take (uint.nat li - 1)) ∧ a < uint.nat li))⌝ ∗
    cmtIdx γ T L (uint.nat cidx))

instance cfgFacts_persistent γ L n a T cfg ccfg cidx li :
    Persistent (cfgFacts (GF := GF) γ L n a T cfg ccfg cidx li) := by
  unfold cfgFacts; infer_instance

theorem cfgAtIs_congr (γ : GNames) (L L2 : RLog) (p : Nat) (c : Configuration)
    (h : ent L2 p = ent L p) : cfgAtIs (GF := GF) γ L p c ⊢ cfgAtIs γ L2 p c := by
  unfold cfgAtIs
  iintro (H | ⟨%ss, %e, Hv, %He⟩)
  · ileft; iexact H
  · iright; iexists ss, e; iframe Hv; ipureintro; rw [h]; exact He

theorem cfgAtIs_le (γ : GNames) (L : RLog) (p : Nat) (c : Configuration) :
    cfgAtIs (GF := GF) γ L p c ⊢ ⌜p ≤ L.length⌝ := by
  unfold cfgAtIs
  iintro (⟨%H, -⟩ | ⟨%ss, %e, -, %He⟩)
  · ipureintro; omega
  · ipureintro
    have h := He.2.1
    unfold ent at h; split at h
    · simp at h
    · have := (List.getElem?_eq_some_iff.1 h).1; omega

/-- The initial facts (`mainOwnAt`'s, at the request's term `T ≥ s.term`). -/
theorem cfgFacts_init (γ : GNames) (L : RLog) (a T T0 : Nat) (cfg ccfg : Configuration) (cidx li : w64)
    (hT : T0 ≤ T)
    (hcc : uint.nat li = lastCfgIdx L ∧
      (cidx = li ∨ (uint.nat cidx = lastCfgIdx (L.take (uint.nat li - 1)) ∧ a < uint.nat li))) :
    cfgAtIs (GF := GF) γ L (uint.nat li) cfg ∗ cfgAtIs γ L (uint.nat cidx) ccfg ∗
      cmtIdx γ T0 L (uint.nat cidx) ⊢ cfgFacts γ L L.length a T cfg ccfg cidx li := by
  iintro ⟨#H1, #H2, #H3⟩
  unfold cfgFacts
  iframe H1 H2
  isplitr
  · ipureintro; rw [List.take_length]; exact hcc
  iapply cmtIdx_mono γ T0 T L L _ hT rfl $$ H3

/-- Everything is unchanged in a later term. -/
theorem cfgFacts_term (γ : GNames) (L : RLog) (n a T T' : Nat) (cfg ccfg : Configuration) (cidx li : w64)
    (hT : T ≤ T') :
    cfgFacts (GF := GF) γ L n a T cfg ccfg cidx li ⊢ cfgFacts γ L n a T' cfg ccfg cidx li := by
  unfold cfgFacts
  iintro ⟨#H1, #H2, %H, #H3⟩
  iframe H1 H2
  isplitr; · ipureintro; exact H
  iapply cmtIdx_mono γ T T' L L _ hT rfl $$ H3

/-- Appending entries after the scanned prefix. -/
theorem cfgFacts_append (γ : GNames) (L X : RLog) (a T : Nat) (cfg ccfg : Configuration) (cidx li : w64) :
    cfgFacts (GF := GF) γ L L.length a T cfg ccfg cidx li ⊢
      cfgFacts γ (L ++ X) L.length a T cfg ccfg cidx li := by
  unfold cfgFacts
  iintro ⟨#H1, #H2, %H, #H3⟩
  ihave %hl1 := cfgAtIs_le γ L _ cfg $$ H1
  ihave %hl2 := cfgAtIs_le γ L _ ccfg $$ H2
  isplitr
  · iapply cfgAtIs_congr γ L _ _ cfg (ent_append_of_le L X _ hl1) $$ H1
  isplitr
  · iapply cfgAtIs_congr γ L _ _ ccfg (ent_append_of_le L X _ hl2) $$ H2
  isplitr
  · ipureintro
    rw [List.take_left' rfl]
    refine ⟨by rw [List.take_length] at H; exact H.1, ?_⟩
    rcases H.2 with h | ⟨h1, h2⟩
    · left; exact h
    · right; refine ⟨?_, h2⟩
      rw [h1, List.take_append_of_le_length (by omega)]
  iapply cmtIdx_mono γ T T L (L ++ X) _ (Nat.le_refl _) (ent_append_of_le L X _ hl2) $$ H3

/-- A truncation above the latest configuration. -/
theorem cfgFacts_trunc (γ : GNames) (L : RLog) (m a T : Nat) (cfg ccfg : Configuration) (cidx li : w64)
    (hm : uint.nat li ≤ m) :
    cfgFacts (GF := GF) γ L L.length a T cfg ccfg cidx li ⊢
      cfgFacts γ (L.take m) (L.take m).length a T cfg ccfg cidx li := by
  unfold cfgFacts
  iintro ⟨#H1, #H2, %H, #H3⟩
  rw [List.take_length] at H
  have hci : uint.nat cidx ≤ uint.nat li := by
    rcases H.2 with h | ⟨h1, -⟩
    · exact Nat.le_of_eq (congrArg _ h)
    · rw [h1, H.1]
      have := lastCfgIdx_le_length (L.take (lastCfgIdx L - 1))
      simp only [List.length_take] at this; omega
  isplitr
  · iapply cfgAtIs_congr γ L _ _ cfg (ent_take_of_le L m _ hm) $$ H1
  isplitr
  · iapply cfgAtIs_congr γ L _ _ ccfg (ent_take_of_le L m _ (by omega)) $$ H2
  isplitr
  · ipureintro
    rw [List.take_length]
    refine ⟨by rw [lastCfgIdx_take_of_le L m (by rw [← H.1]; exact hm)]; exact H.1, ?_⟩
    rcases H.2 with h | ⟨h1, h2⟩
    · left; exact h
    · right; refine ⟨?_, h2⟩
      rw [h1, List.take_take, Nat.min_eq_left (by omega)]
  iapply cmtIdx_mono γ T T L (L.take m) _ (Nat.le_refl _) (ent_take_of_le L m _ (by omega)) $$ H3

/-- The rollback: a truncation at `m` in `[cidx, li)`; the latest becomes the committed one. -/
theorem cfgFacts_rollback (γ : GNames) (L : RLog) (m a T : Nat) (cfg ccfg : Configuration) (cidx li : w64)
    (hc : uint.nat cidx ≤ m) (hm : m < uint.nat li) :
    cfgFacts (GF := GF) γ L L.length a T cfg ccfg cidx li ⊢
      cfgFacts γ (L.take m) (L.take m).length a T ccfg ccfg cidx cidx := by
  unfold cfgFacts
  iintro ⟨#H1, #H2, %H, #H3⟩
  rw [List.take_length] at H
  have hne : cidx ≠ li := by intro h; rw [h] at hc; omega
  have h1 : uint.nat cidx = lastCfgIdx (L.take (lastCfgIdx L - 1)) := by
    rcases H.2 with h | ⟨h1, -⟩
    · exact absurd h hne
    · rw [h1, H.1]
  isplitr
  · iapply cfgAtIs_congr γ L _ _ ccfg (ent_take_of_le L m _ hc) $$ H2
  isplitr
  · iapply cfgAtIs_congr γ L _ _ ccfg (ent_take_of_le L m _ hc) $$ H2
  isplitr
  · ipureintro
    rw [List.take_length]
    refine ⟨?_, Or.inl rfl⟩
    rw [lastCfgIdx_take_rollback L m (by rw [← h1]; exact hc) (by rw [← H.1]; exact hm), h1]
  iapply cmtIdx_mono γ T T L (L.take m) _ (Nat.le_refl _) (ent_take_of_le L m _ hc) $$ H3

/-- The scan of an entry that is no configuration entry. -/
theorem cfgFacts_step_other (γ : GNames) (L : RLog) (n a T : Nat) (cfg ccfg : Configuration)
    (cidx li : w64) (e : Entry) (he : ent L (n + 1) = some e) (hk : e.kind ≠ kConfig) :
    cfgFacts (GF := GF) γ L n a T cfg ccfg cidx li ⊢ cfgFacts γ L (n + 1) a T cfg ccfg cidx li := by
  unfold cfgFacts
  iintro ⟨#H1, #H2, %H, #H3⟩
  iframe H1 H2 H3
  ipureintro
  rw [lastCfgIdx_take_succ L n e he, if_neg hk]
  exact H

/-- The scan of a configuration entry at `n + 1` (`processConfigurationLogEntry`): the latest becomes
the committed configuration (committed by `cfgPrevCommitted`), the entry the latest. -/
theorem cfgFacts_step_cfg (γ : GNames) (L : RLog) (n a T : Nat) (cfg ccfg c : Configuration)
    (cidx li : w64) (e : Entry) (ss : List Server) (he : ent L (n + 1) = some e)
    (hk : e.kind = kConfig) (hd : e.data = encodeServers ss) (hss : srvsOk γ ss) (ha : a < n + 1)
    (hn : n + 1 < 2 ^ 64) :
    cfgFacts (GF := GF) γ L n a T cfg ccfg cidx li ∗ c.Servers' ↦*□ ss ∗
      cmtIdx γ T L (lastCfgIdx (L.take n)) ⊢
      cfgFacts γ L (n + 1) a T c cfg li (W64 (n + 1 : Nat)) := by
  unfold cfgFacts
  iintro ⟨⟨#H1, #H2, %H, #H3⟩, #Hc, #Hp⟩
  have hw : uint.nat (W64 (n + 1 : Nat)) = n + 1 := by word
  rw [hw]
  isplitr
  · unfold cfgAtIs
    iright
    iexists ss, e
    unfold cfgVal
    iframe Hc
    ipureintro; exact ⟨hss, by omega, he, hk, hd⟩
  iframe H1
  isplitr
  · ipureintro
    rw [lastCfgIdx_take_succ L n e he, if_pos hk]
    refine ⟨rfl, Or.inr ⟨?_, ha⟩⟩
    rw [Nat.add_sub_cancel]; exact H.1
  rw [H.1]; iexact Hp

/- hraft_robust L0: statement obsolete (its stage restates or deletes it)
/-- Reassembling `mainOwnAt` from the leader arm and the configurations' facts. -/
theorem mainOwnAt_ae (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (st : w32)
    (a : Nat) (sst : StableAbs) (cfg ccfg : Configuration) (cidx li : w64) (lch : Loc)
    (γl : ChanNames) (bs : List Bool) (c : Nat) (hvm : voteMatches sst s)
    (ha : a ≤ s.dur.1 ∧ s.cidx ≤ a) (hc : c ≤ a)
    (hcap : sint.Z γl.chanCap = 1 ∧ bs.length ≤ 1) :
    srvOwn γ i s ∗ durView γ i (1 : Qp).half s.dur.1 ∗ rc.ownS sst ∗
      ghostVar rc.names.lastLog (1 : Qp).half (s.log.length, lastTerm s.log) ∗
      ghostVar rc.names.state (1 : Qp).half st ∗ stArm γ i st s.term s.log s.cidx a cidx li ∗
      monoNatAuthOwn rc.dur.applied (1 : Qp).half a ∗
      fsmProd γ rc a ∗ r.[Raft, go!"configurations"] ↦ configurations.mk ccfg cidx cfg li ∗
      cfgFacts γ s.log s.log.length a s.term cfg ccfg cidx li ∗
      r.[Raft, go!"leaderCh"] ↦□ lch ∗ isChan lch γl Bool ∗
      ownChan γl Bool (.Buffered bs) ∗ ghostVar rc.names.logPend (1 : Qp).half ([] : RLog) ∗
      verifyRegistry γ rc i ∗
      ghostVar rc.dur.pend (1 : Qp).half (none : Option (Nat × Nat × GoString)) ∗
      monoNatAuthOwn rc.dur.comp 1 c ⊢ mainOwnAt r γ rc i s st := by
  iintro ⟨Hs, Hdv, HS, Hll, Hst, Hstl, Happ, Hprod, Hcfgs, Hcf, #Hlch, #Hlchan, Hlown, Hpend, Hvreg, Hpd,
    Hcomp⟩
  unfold cfgFacts stArm
  icases Hcf with ⟨#H1, #H2, %H, #H3⟩
  rw [List.take_length] at H
  iapply mainOwnAt_intro' r γ rc i s st a sst cfg ccfg cidx li lch γl bs c hvm ha hc H hcap
  iframe
  iframe #
-/

/-- A later FSM position (`processLogs`), below the latest configuration if it is not committed. -/
theorem cfgFacts_mono_a (γ : GNames) (L : RLog) (n a a' T : Nat) (cfg ccfg : Configuration)
    (cidx li : w64) (h : a < uint.nat li → a' < uint.nat li) :
    cfgFacts (GF := GF) γ L n a T cfg ccfg cidx li ⊢ cfgFacts γ L n a' T cfg ccfg cidx li := by
  unfold cfgFacts
  iintro ⟨#H1, #H2, %H, #H3⟩
  iframe H1 H2 H3
  ipureintro
  refine ⟨H.1, ?_⟩
  rcases H.2 with h1 | ⟨h1, h2⟩
  · left; exact h1
  · right; exact ⟨h1, h h2⟩

theorem cfgFacts_cmt (γ : GNames) (L : RLog) (n a T : Nat) (cfg ccfg : Configuration) (cidx li : w64) :
    cfgFacts (GF := GF) γ L n a T cfg ccfg cidx li ⊢ cmtIdx γ T L (uint.nat cidx) := by
  unfold cfgFacts
  iintro ⟨-, -, -, #H3⟩
  iexact H3

theorem cfgFacts_pure (γ : GNames) (L : RLog) (n a T : Nat) (cfg ccfg : Configuration) (cidx li : w64) :
    cfgFacts (GF := GF) γ L n a T cfg ccfg cidx li ⊢ ⌜uint.nat li = lastCfgIdx (L.take n) ∧
      (cidx = li ∨ (uint.nat cidx = lastCfgIdx (L.take (uint.nat li - 1)) ∧ a < uint.nat li))⌝ := by
  unfold cfgFacts
  iintro ⟨-, -, %H, -⟩
  ipureintro; exact H

/-- The committed configuration's servers (the rollback's `setLatestConfiguration`). -/
theorem cfgFacts_ccfg (γ : GNames) (L : RLog) (n a T : Nat) (cfg ccfg : Configuration) (cidx li : w64) :
    cfgFacts (GF := GF) γ L n a T cfg ccfg cidx li ⊢
      ∃ ss : List Server, ccfg.Servers' ↦*□ ss ∗ ⌜ss = [] ∨ srvsOk γ ss⌝ := by
  unfold cfgFacts cfgAtIs
  iintro ⟨-, (⟨-, #H⟩ | ⟨%ss, %e, #Hv, -⟩), -, -⟩
  · iexists []; iframe H; ipureintro; left; rfl
  · unfold cfgVal
    icases Hv with ⟨#Hv, %Hss⟩
    iexists ss; iframe Hv; ipureintro; right; exact Hss

theorem len_eq_of_break' (L : RLog) (prev pt : Nat) (ents : RLog) (k : Nat)
    (hp : prevMatch L prev pt) (hm : matchedUpTo L prev ents k) (hlt : L.length < prev + 1 + k) :
    L.length = prev + k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rcases hp with hp | ⟨hp, _⟩ <;> omega
  · have := (hm.2 (k - 1) (by omega)).1; omega

/-- The commit index reaching the latest configuration (`setCommittedConfiguration(latest)`). -/
theorem cfgFacts_commit (γ : GNames) (L : RLog) (n a a' T : Nat) (cfg ccfg : Configuration)
    (cidx li : w64) :
    cfgFacts (GF := GF) γ L n a T cfg ccfg cidx li ∗ cmtIdx γ T L (uint.nat li) ⊢
      cfgFacts γ L n a' T cfg cfg li li := by
  unfold cfgFacts
  iintro ⟨⟨#H1, #H2, %H, #H3⟩, #H4⟩
  iframe H1 H4
  ipureintro
  exact ⟨H.1, Or.inl rfl⟩

/-- The leader arm after `appendEntries`: unchanged unless the server is the leader of the request's
term `T` (then the request is its own, its log is unchanged, the new commit index `c'` is covered by
the request's `lciOk`). -/
theorem stArm_final (γ : GNames) (i ℓ : SID) (st : w32) (T : Nat) (L L' : RLog) (c c' a a' lci : Nat)
    (cidx li cidx' li' : w64)
    (hL : st ≠ stFollower → ℓ = i → L' = L ∧ li' = li) (ha : a ≤ a') (hc : c' = c ∨ c' ≤ lci)
    (hcl : (st ≠ stFollower → ℓ = i → cidx' = cidx) ∨ uint.nat li' ≤ c') :
    Inv (GF := GF) γ ∗ leaderIs γ T ℓ ∗ lciOk γ T lci ∗ stArm γ i st T L c a cidx li ⊢ |={⊤}=>
      stArm γ i st T L' c' a' cidx' li' := by
  iintro ⟨#HI, #Hl, #Hlci, Harm⟩
  by_cases hst : st = stLeader
  rotate_left
  · unfold stArm; imodintro; ileft; ipureintro; exact hst
  unfold stArm
  icases Harm with (%h | ⟨#Hli, ⟨%m, Hp, %hm⟩, Hcc, %n0, #Hn0, Hcm, Hcl⟩)
  · exact absurd hst h
  ihave %hℓ := leaderIs_agree γ T ℓ i $$ [$Hl $Hli]
  have hsf : st ≠ stFollower := by rw [hst]; decide
  obtain ⟨hL', hli'⟩ := hL hsf hℓ
  subst hL' hli'
  iright
  iframe Hli Hcc
  isplitl [Hp]
  · iexists m; iframe; ipureintro; omega
  iexists n0
  iframe Hn0
  -- the commit index
  ihave Hcm' : (|={⊤}=> ⌜c' ≤ n0⌝ ∨ ∃ k p : Nat, commitIs γ T k p ∗ ⌜c' ≤ k⌝) $$ [Hcm]
  · rcases hc with hc | hc
    · subst hc; imodintro; iexact Hcm
    · by_cases hn : c' ≤ n0
      · imodintro; ileft; ipureintro; exact hn
      · imod lci_commit γ ⊤ (by simp) T c' lci n0 ℓ (by omega) hc $$ [$HI $Hl $Hn0 $Hlci]
          with ⟨%k', %p', %hk', #Hk'⟩
        imodintro; iright; iexists k', p'; iframe Hk'; ipureintro; exact hk'
  imod Hcm' with #Hcm'
  imodintro
  iframe Hcm'
  rcases hcl with h1 | h1
  · have h1 := h1 hsf hℓ
    subst h1
    iexact Hcl
  · icases Hcm' with (%h2 | ⟨%k, %p, #Hk, %hk⟩)
    · ileft; ipureintro; right; omega
    · iright; iexists k, p; iframe Hk; ipureintro; omega

theorem aeValid_lciOk (γ : GNames) (T prev pt : Nat) (ents : RLog) (lci : Nat) :
    aeValid (GF := GF) γ T prev pt ents lci ⊢ lciOk γ T lci := by
  unfold aeValid
  iintro ⟨-, -, -, #H⟩
  iexact H

end aeCfg
end github_com.hashicorp.raft

open github_com.hashicorp.raft.aeCfg in
set_option maxHeartbeats 4000000 in
theorem github_com.hashicorp.raft.Raft.appendEntries.wp_proof
    (wp_getRPCHeader : github_com.hashicorp.raft.Raft.getRPCHeader.spec (GF := GF) (hG := hG))
    (wp_getCurrentTerm : github_com.hashicorp.raft.raftState.getCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_getLastIndex : github_com.hashicorp.raft.raftState.getLastIndex.spec (GF := GF) (hG := hG))
    (wp_getState : github_com.hashicorp.raft.raftState.getState.spec (GF := GF) (hG := hG))
    (wp_setState : github_com.hashicorp.raft.Raft.setState.spec (GF := GF) (hG := hG))
    (wp_setCurrentTerm : github_com.hashicorp.raft.Raft.setCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_setLeader : github_com.hashicorp.raft.Raft.setLeader.spec (GF := GF) (hG := hG))
    (wp_getLastEntry : github_com.hashicorp.raft.raftState.getLastEntry.spec (GF := GF) (hG := hG))
    (wp_getLastLog : github_com.hashicorp.raft.raftState.getLastLog.spec (GF := GF) (hG := hG))
    (wp_setLastLog : github_com.hashicorp.raft.raftState.setLastLog.spec (GF := GF) (hG := hG))
    (wp_tryStageCommitIndex : github_com.hashicorp.raft.Raft.tryStageCommitIndex.spec (GF := GF) (hG := hG))
    (wp_processConfigurationLogEntry :
      github_com.hashicorp.raft.Raft.processConfigurationLogEntry.spec (GF := GF) (hG := hG))
    (wp_getCommitIndex : github_com.hashicorp.raft.raftState.getCommitIndex.spec (GF := GF) (hG := hG))
    (wp_setCommitIndex : github_com.hashicorp.raft.raftState.setCommitIndex.spec (GF := GF) (hG := hG))
    (wp_min : github_com.hashicorp.raft.min.spec (GF := GF) (hG := hG))
    (wp_setCommittedConfiguration :
      github_com.hashicorp.raft.Raft.setCommittedConfiguration.spec (GF := GF) (hG := hG))
    (wp_setLatestConfiguration :
      github_com.hashicorp.raft.Raft.setLatestConfiguration.spec (GF := GF) (hG := hG))
    (wp_processLogs : github_com.hashicorp.raft.Raft.processLogs.spec (GF := GF) (hG := hG))
    (wp_setLastContact : github_com.hashicorp.raft.Raft.setLastContact.spec (GF := GF) (hG := hG))
    (wp_Respond : github_com.hashicorp.raft.RPC.Respond.spec (GF := GF) (hG := hG))
    (wp_Bool_Load : sync.atomic.Bool.Load.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.appendEntries.spec (GF := GF) (hG := hG) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)
