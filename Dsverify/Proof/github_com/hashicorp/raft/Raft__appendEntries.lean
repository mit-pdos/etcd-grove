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

/-- Reassembling `mainOwnAt` from the leader arm and the configurations' facts. -/
theorem mainOwnAt_ae (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (st : w32)
    (a : Nat) (sst : StableAbs) (cfg ccfg : Configuration) (cidx li : w64) (lch : Loc)
    (γl : ChanNames) (bs : List Bool) (c : Nat) (hvm : voteMatches sst s)
    (ha : a ≤ s.dur.1 ∧ s.cidx ≤ a) (hc : c ≤ a)
    (hcap : sint.Z γl.chanCap = 1 ∧ bs.length ≤ 1) :
    srvOwn γ i s ∗ durView γ i (1 : Qp).half s.dur.1 ∗ rc.ownS sst ∗
      ghostVar rc.names.lastLog (1 : Qp).half (s.log.length, lastTerm s.log) ∗
      ghostVar rc.names.state (1 : Qp).half st ∗ stArm γ i st s.term s.log s.cidx a cidx li ∗
      monoNatAuthOwn rc.names.applied (1 : Qp).half a ∗
      fsmProd γ rc a ∗ r.[Raft, go!"configurations"] ↦ configurations.mk ccfg cidx cfg li ∗
      cfgFacts γ s.log s.log.length a s.term cfg ccfg cidx li ∗
      r.[Raft, go!"leaderCh"] ↦□ lch ∗ isChan lch γl Bool ∗
      ownChan γl Bool (.Buffered bs) ∗ ghostVar rc.names.logPend (1 : Qp).half ([] : RLog) ∗
      verifyRegistry γ rc i ∗
      ghostVar rc.names.pend (1 : Qp).half (none : Option (Nat × Nat × GoString)) ∗
      monoNatAuthOwn rc.names.comp 1 c ⊢ mainOwnAt r γ rc i s st := by
  iintro ⟨Hs, Hdv, HS, Hll, Hst, Hstl, Happ, Hprod, Hcfgs, Hcf, #Hlch, #Hlchan, Hlown, Hpend, Hvreg, Hpd,
    Hcomp⟩
  unfold cfgFacts stArm
  icases Hcf with ⟨#H1, #H2, %H, #H3⟩
  rw [List.take_length] at H
  iapply mainOwnAt_intro' r γ rc i s st a sst cfg ccfg cidx li lch γl bs c hvm ha hc H hcap
  iframe
  iframe #

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
    github_com.hashicorp.raft.Raft.appendEntries.spec (GF := GF) (hG := hG) :=
  fun r γ rc i rpc p rq snd T prev pt ents lci ss γc s st tid => by
  wp_start as ⟨#Hr, Hm, Htok, Hp, Hreq, #Hbag⟩
  unfold mainOwnAt
  icases Hm with ⟨%a, %sst, %cfg, %ccfg, %cidx, %cli, %lch, %γl, %bs, %cmp, Hs, Hdv, HS, %Hvm, Hll, Hst, Hstl,
    Hpend, Hvreg, Happ, %Ha, Hprod, Hpnd, Hcomp, %Hcmp, Hcfgs, #Hcfl, #Hcfc, %Hccfg, #Hcmi, #Hlch, #Hlchan,
    Hlown, %Hcap⟩
  unfold aeReq
  icases Hreq with ⟨%Hnums, #Hhdr, #Hlead, ⟨%ptrs, #Hents, %Hplen, #Hptrs⟩, #Hae, #Hss⟩
  obtain ⟨HTe, Hpreve, Hpte, Hlcie⟩ := Hnums
  ihave ⟨#HI, #Hvi⟩ := isRaft_proto r γ rc i $$ Hr
  ihave #Htc := isRaft_termCell r γ rc i $$ Hr
  ihave #Hcc := isRaft_cidxCell r γ rc i $$ Hr
  ihave #Hlc := isRaft_logCell r γ rc i $$ Hr
  ihave #Hsc := isRaft_stateCell r γ rc i $$ Hr
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply wp_getRPCHeader r γ rc i $$ [$Hr] as %h0 #Hh0
  wp_apply wp_getCurrentTerm.1 r γ i s $$ [$HI $Htc $Hs] as Hs
  wp_apply wp_getLastIndex.1 r γ rc i s a $$ [$Hr $Hll $Hs $Happ] as %li ⟨%Hli, Hll, Hs, Happ⟩
  · ipureintro; exact Ha.1
  irename «$r0» => Hrsp
  imod termLb_of_srv γ r i s $$ [$HI $Htc $Hs] with ⟨Hs, #Htlb0⟩
  imod srvOwn_facts γ ⊤ (by simp) i s $$ [$HI $Hs] with ⟨Hs, -, %Hsf⟩
  have Hst62 : s.term < 2 ^ 62 := Hsf.2.2.2.2.2.1
  wp_apply wp_getCurrentTerm.1 r γ i s $$ [$HI $Htc $Hs] as Hs
  wp_if_destruct
  · wp_apply wp_Respond rpc_ptr rpc γc _ _ _ $$ [$rpc $Hbag Hrsp] as rpc
    · iapply aeRespP_intro $$ [$Hrsp]
      iframe Hh0
      isplitr
      · iapply termOk_of_termLb γ i _ s.term (by word) $$ [$Hvi $Htlb0]
      ileft; ipureintro; rfl
    wp_end
    iexists s, st
    iframe Htok
    isplitl
    · iexists a, sst, cfg, ccfg, cidx, cli, lch, γl, bs, cmp
      iframe # ∗
      ipureintro; exact ⟨Hvm, Ha, Hcmp, Hccfg, Hcap⟩
    ileft; ipureintro; right; exact ⟨rfl, rfl, rfl⟩
  ipersist r
  ipersist a
  ipersist resp
  ipersist Hp
  iStructNamed Hp
  ihave Hrsp : (∃ rv0 : AppendEntriesResponse, «$r0_ptr» ↦ rv0 ∗
      ⌜rv0.RPCHeader' = h0 ∧ rv0.Success' = false⌝ ∗ termOk γ (uint.nat rv0.Term')) $$ [Hrsp]
  · iexists _; iframe Hrsp; isplitr; · ipureintro; exact ⟨rfl, rfl⟩
    iapply termOk_of_termLb γ i _ s.term (by word) $$ [$Hvi $Htlb0]
  icases Hrsp with ⟨%rv0, Hrsp, %Hrv0, #Hrv0t⟩
  have HT : s.term ≤ T := by
    rw [← HTe]; have : uint.Z (W64 (s.term : Int)) = s.term := by word
    simp only [uint.nat]; word
  ihave ⟨%ℓ, #Hlead_l⟩ := aeValid_leader γ T prev pt ents lci $$ Hae
  wp_join iprop(∃ (st1 : w32) (sst1 : StableAbs) (rv : AppendEntriesResponse),
      srvOwn γ i { s with term := T } ∗ ghostVar rc.names.state (1 : Qp).half st1 ∗
      ⌜st1 = stFollower ∨ (st1 = st ∧ T = s.term ∧ st ≠ stFollower ∧ (ℓ ≠ i → st = stCandidate))⌝ ∗
      stArm γ i st1 T s.log s.cidx a cidx cli ∗
      rc.ownS sst1 ∗ ⌜voteMatches sst1 { s with term := T }⌝ ∗ «$r0_ptr» ↦ rv ∗
      ⌜rv.RPCHeader' = h0 ∧ rv.Success' = false⌝ ∗ termOk γ (uint.nat rv.Term') ∗ termLb γ i T ∗
      rtok tid) at next with [Hs Hst Hstl HS Hrsp Htok]
    as ⟨%st1, %sst1, %rv, Hs, Hst, %Hcase, Hstl, HS, %Hvm1, Hrsp, %Hrv, #Hrvt, #HtlbT, Htok⟩
  · wp_apply wp_getCurrentTerm.1 r γ i s $$ [$HI $Htc $Hs] as Hs
    wp_if_destruct
    · -- a newer term
      rw [show (Follower : val) = #stFollower from rfl]
      wp_apply wp_setState r γ rc i _ stFollower s $$ [$Hr $Hst $Htok] as ⟨Hst, -, Htok⟩
      · isplitr; · ipureintro; left; rfl
        iapply obsArg_state γ i s stFollower (by decide)
      ihave #HokT := termOk_of_aeValid γ T prev pt ents lci $$ Hae
      ihave Hupd := setTerm_step γ i s T HT $$ [$HI $Hs $HokT]
      wp_apply wp_setCurrentTerm r γ rc i sst rq.Term'
        iprop(srvOwn γ i { s with term := T } ∗ termLb γ i T) $$ [$Hr $HS Hupd] as ⟨HS, Hs, #HtlbT⟩
      · rw [HTe]; iexact Hupd
      wp_join_done
      iexists stFollower, _, { rv0 with Term' := rq.Term' }
      iframe
      rw [HTe]
      iframe HtlbT
      isplitr
      · ipureintro; left; rfl
      isplitr
      · unfold stArm; ileft; ipureintro; decide
      isplitr
      · ipureintro; exact voteMatches_term sst s rq.Term' T Hvm
      isplitr
      · ipureintro; exact ⟨Hrv0.1, Hrv0.2⟩
      iapply termOk_of_termLb γ i T T (Nat.le_refl _) $$ [$Hvi $HtlbT]
    · -- the same term: become a follower unless already one (or a transfer candidate)
      have HTs : T = s.term := by
        rw [← HTe]; have : uint.Z (W64 (s.term : Int)) = s.term := by word
        simp only [uint.nat]; word
      wp_apply wp_getState.1 r rc st $$ [$Hsc $Hst] as Hst
      wp_if_destruct
      · -- already a follower
        wp_join_done
        iexists _, sst, rv0
        have hs : { s with term := T } = s := by rw [HTs]
        rw [hs]
        iframe
        isplitr
        · ipureintro; left; rfl
        isplitl [Hstl]
        · unfold stArm; rw [HTs]; iexact Hstl
        rw [HTs]
        iframe Htlb0 Hrv0t
        ipureintro; exact ⟨Hvm, Hrv0⟩
      · ihave #Hcft := isRaft_cells r γ rc i $$ Hr
        unfold raftCells
        icases Hcft with ⟨-, -, -, -, -, #Hcft, -⟩
        wp_apply wp_Bool_Load
        unfold cftCell
        iinv Hcft with ⟨%b, Hb⟩ Hclose
        all_goals first | exact Iris.CoPset.subseteq_top | skip
        imod fupd_mask_subseteq (E1 := ⊤ \ ↑cftN) (E2 := ∅) Iris.Std.LawfulSet.empty_subset with Hmask
        imodintro
        inext
        iexists b
        iframe Hb
        iintro Hb
        imod Hmask
        imod Hclose $$ [Hb] with -
        · inext; iexists b; iexact Hb
        imodintro
        wp_auto
        cases b
        · -- step down
          simp only [Bool.not_false]
          wp_auto
          rw [show (Follower : val) = #stFollower from rfl]
          wp_apply wp_setState r γ rc i _ stFollower s $$ [$Hr $Hst $Htok] as ⟨Hst, -, Htok⟩
          · isplitr; · ipureintro; left; rfl
            iapply obsArg_state γ i s stFollower (by decide)
          ihave #HokT := termOk_of_aeValid γ T prev pt ents lci $$ Hae
          ihave Hupd := setTerm_step γ i s T HT $$ [$HI $Hs $HokT]
          wp_apply wp_setCurrentTerm r γ rc i sst rq.Term'
            iprop(srvOwn γ i { s with term := T } ∗ termLb γ i T) $$ [$Hr $HS Hupd] as ⟨HS, Hs, #HtlbT⟩
          · rw [HTe]; iexact Hupd
          wp_join_done
          iexists stFollower, _, { rv0 with Term' := rq.Term' }
          iframe
          rw [HTe]
          iframe HtlbT
          isplitr
          · ipureintro; left; rfl
          isplitr
          · unfold stArm; ileft; ipureintro; decide
          isplitr
          · ipureintro; exact voteMatches_term sst s rq.Term' T Hvm
          isplitr
          · ipureintro; exact ⟨Hrv0.1, Hrv0.2⟩
          iapply termOk_of_termLb γ i T T (Nat.le_refl _) $$ [$Hvi $HtlbT]
        · -- a candidate from a leadership transfer: no step down
          imod stateCell_val r rc st $$ [$Hsc $Hst] with ⟨Hst, %Hsv⟩
          simp only [Bool.not_true]
          wp_auto
          ihave %Hcand : ⌜ℓ ≠ i → st = stCandidate⌝ $$ [Hstl]
          · icases Hstl with (%Hnl | ⟨#Hli, -⟩)
            · ipureintro; intro _
              rcases Hsv with h | h | h
              · exact absurd h Hif
              · exact h
              · exact absurd h Hnl
            · rw [← HTs]
              ihave %Heq := leaderIs_agree γ T ℓ i $$ [$Hlead_l $Hli]
              ipureintro; intro h; exact absurd Heq h
          wp_join_done
          iexists st, sst, rv0
          have hs : { s with term := T } = s := by rw [HTs]
          rw [hs]
          iframe
          isplitr
          · ipureintro; right; exact ⟨rfl, HTs, Hif, Hcand⟩
          isplitl [Hstl]
          · unfold stArm; rw [HTs]; iexact Hstl
          rw [HTs]
          iframe Htlb0 Hrv0t
          ipureintro; exact ⟨Hvm, Hrv0⟩
  ihave #Hcf0 := cfgFacts_init γ s.log a T s.term cfg ccfg cidx cli HT Hccfg $$ [$Hcfl $Hcfc $Hcmi]
  ihave #Hconf := isRaft_conf r γ rc i $$ Hr
  unfold raftConf
  icases Hconf with ⟨%cc0, -, -, #HlcI⟩
  -- save the leader
  iStructNamed RPCHeader
  ihave ⟨%xtr, %rpcCh, #Htr, #Hrpcf, #Htrans⟩ := isRaft_transport r γ rc i $$ Hr
  unfold isTransport
  icases Htrans with ⟨-, -, -, -, #Hdec, -⟩
  unfold hdrOk
  icases Hhdr with ⟨%Hpv, #Hid, #Haddr⟩
  wp_auto
  wp_join with [Htok]
  · wp_apply Hdec $$ Haddr
    iintro Haddr'
    wp_auto
    wp_apply wp_bytes_to_string $$ Hid as Hid'
    wp_apply wp_setLeader r γ rc i _ _ $$ [$Hr $Htok] as Htok
    wp_join_done
  · wp_apply Hdec $$ Hlead
    iintro Hlead'
    wp_auto
    wp_apply wp_bytes_to_string $$ Hid as Hid'
    wp_apply wp_setLeader r γ rc i _ _ $$ [$Hr $Htok] as Htok
    wp_join_done
  -- the previous entry
  ihave ⟨%xls, #Hlsf, #Hls, -⟩ := isRaft_logStore r γ rc i $$ Hr
  unfold isLogStore
  icases Hls with ⟨-, -, #HgetLog, #HstoreLogs, -, #HdelRange⟩
  wp_join (Q := fun v => iprop(
      (⌜v = executeVal⌝ ∗ srvOwn γ i { s with term := T } ∗ ghostVar rc.names.logPend (1 : Qp).half ([] : RLog) ∗
        ghostVar rc.names.lastLog (1 : Qp).half (s.log.length, lastTerm s.log) ∗
        monoNatAuthOwn rc.names.applied (1 : Qp).half a ∗
        «$r0_ptr» ↦ rv ∗ rtok tid ∗ ⌜prevMatch s.log prev pt⌝) ∨
      (⌜v = returnVal #()⌝ ∗ srvOwn γ i { s with term := T } ∗ ghostVar rc.names.logPend (1 : Qp).half ([] : RLog) ∗
        ghostVar rc.names.lastLog (1 : Qp).half (s.log.length, lastTerm s.log) ∗
        monoNatAuthOwn rc.names.applied (1 : Qp).half a ∗
        «$r0_ptr» ↦ { rv with NoRetryBackoff' := true } ∗ rtok tid)))
    at next with [Hs Hpend Hll Hrsp Htok Happ]
  · wp_if_destruct
    · -- prev > 0
      wp_apply wp_getLastEntry r γ rc i { s with term := T } a $$ [$Hr $Hll $Hs $Happ]
        as %lx %ly ⟨%Hlxy, Hll, Hs, Happ⟩
      · ipureintro; exact Ha.1
      simp only at Hlxy
      wp_if_destruct
      · -- prev is the last index
        wp_if_destruct
        · q_exec
          iframe
          ipureintro
          right
          constructor
          · have := Hlxy.1; omega
          · rw [← Hpreve, Hlxy.1, ← Hpte, Hlxy.2]; rfl
        · q_ret; iframe
      · -- read the previous entry from the store
        wp_apply_core HgetLog $$ prevLog Htok
        iapply logCell_read γ rc i { s with term := T }
        iframe HI Hlc Hs Hpend
        iintro %A %HA
        unfold getLogPost
        split
        · -- found
          rename_i e he
          iintro Hs Hpend %err ⟨%Herr, %lv, Hplv, #Hlv⟩ Htok
          unfold logIs
          icases Hlv with ⟨%Hlvf, #Hlvd⟩
          rw [Herr]
          wp_auto
          wp_if_destruct
          · q_exec
            iframe
            ipureintro
            right
            have he' : ent s.log prev = some e := by rw [← Hpreve]; exact HA _ _ he
            refine ⟨(ent_some_bound _ _ _ he').2, ?_⟩
            rw [termAt_of_ent he', ← Hpte, ← Hlvf.2.1, Hif]
          · q_ret; iframe
        · -- not found
          iintro Hs Hpend %err ⟨%Herr, -, %lv, Hplv⟩ Htok
          cases err with
          | nil => exact absurd rfl Herr
          | ok ee =>
            wp_auto
            q_ret; iframe
    · -- prev = 0
      q_exec
      iframe
      ipureintro
      left
      rw [← Hpreve]; word
  rename_i v
  iintro (⟨%Hv, Hs, Hpend, Hll, Happ, Hrsp, Htok, %Hpm⟩ | ⟨%Hv, Hs, Hpend, Hll, Happ, Hrsp, Htok⟩)
  rotate_left
  · -- the previous entry did not match: respond (failure)
    subst Hv
    wp_auto
    wp_apply wp_Respond rpc_ptr rpc γc _ _ _ $$ [$rpc $Hbag Hrsp] as rpc
    · iapply aeRespP_intro $$ [$Hrsp]
      iframe Hrvt
      isplitr
      · ileft; ipureintro; exact Hrv.2
      rw [Hrv.1]; unfold hdrOk; iexact Hh0
    iapply HΦ
    iexists { s with term := T }, st1
    iframe Htok
    isplitl [Hs Hdv HS Hll Hst Hstl Happ Hprod Hcfgs Hlown Hpend Hvreg Hpnd Hcomp]
    · ihave Hmo := mainOwnAt_ae r γ rc i { s with term := T } st1 a sst1 cfg ccfg cidx cli lch γl bs cmp Hvm1
        Ha Hcmp Hcap $$ [Hs Hdv HS Hll Hst Hstl Happ Hprod Hcfgs Hlown Hpend Hvreg Hpnd Hcomp]
      · iframe; iframe #
      unfold mainOwnAt
      iexact Hmo
    iapply ae_post γ i ℓ st st1 s { s with term := T } T Hcase rfl (fun _ _ => rfl) $$ Hlead_l
  subst Hv
  -- the new entries
  ihave %Hentslen := ownSlice_len _ _ _ $$ Hents
  wp_auto
  wp_join (Q := fun v => iprop(
      (⌜v = executeVal⌝ ∗ ∃ (L' : RLog) (cfg' ccfg' : Configuration) (cidx' li' : w64),
        srvOwn γ i { s with term := T, log := L' } ∗ ghostVar rc.names.logPend (1 : Qp).half ([] : RLog) ∗
        ghostVar rc.names.lastLog (1 : Qp).half (L'.length, lastTerm L') ∗
        «$r0_ptr» ↦ rv ∗ rtok tid ∗ durView γ i (1 : Qp).half s.dur.1 ∗
        r.[Raft, go!"configurations"] ↦ configurations.mk ccfg' cidx' cfg' li' ∗
        cfgFacts γ L' L'.length a T cfg' ccfg' cidx' li' ∗
        ⌜prevMatch L' prev pt ∧ matchedUpTo L' prev ents ents.length ∧
          (st1 ≠ stFollower → ℓ = i → L' = s.log ∧ cidx' = cidx ∧ li' = cli)⌝) ∨
      (⌜v = returnVal #()⌝ ∗ ∃ (L' : RLog) (cfg' ccfg' : Configuration) (cidx' li' : w64),
        srvOwn γ i { s with term := T, log := L' } ∗ ghostVar rc.names.logPend (1 : Qp).half ([] : RLog) ∗
        ghostVar rc.names.lastLog (1 : Qp).half (L'.length, lastTerm L') ∗
        «$r0_ptr» ↦ rv ∗ rtok tid ∗ durView γ i (1 : Qp).half s.dur.1 ∗
        r.[Raft, go!"configurations"] ↦ configurations.mk ccfg' cidx' cfg' li' ∗
        cfgFacts γ L' L'.length a T cfg' ccfg' cidx' li' ∗
        ⌜st1 ≠ stFollower → ℓ = i → L' = s.log ∧ cidx' = cidx ∧ li' = cli⌝)))
    at next with [Hs Hpend Hll Hrsp Htok Hdv Hcfgs]
  · wp_if_destruct
    · wp_apply wp_getLastLog.1 r γ rc i _ _ $$ [$Hr $Hll] as %lx %ly ⟨%Hlxy, Hll⟩
      rename_i newEntries_ptr i_ptr gi_ptr
      ihave %Hentswf := ownSlice_wf _ _ _ $$ Hents
      wp_join (Q := fun v => iprop(
          (⌜v = executeVal⌝ ∗ ∃ ns : GoSlice, newEntries_ptr ↦ ns ∗ rtok tid ∗
            durView γ i (1 : Qp).half s.dur.1 ∗
            ghostVar rc.names.logPend (1 : Qp).half ([] : RLog) ∗
            ((⌜ns = slice.nil⌝ ∗ srvOwn γ i { s with term := T } ∗
               ⌜matchedUpTo s.log prev ents ents.length⌝ ∗
               r.[Raft, go!"configurations"] ↦ configurations.mk ccfg cidx cfg cli) ∨
             (∃ (j : Nat) (L' : RLog) (cfg' ccfg' : Configuration) (cidx' li' : w64),
                ⌜ns = slice.slice rq.Entries' Loc (W64 j) rq.Entries'.len ∧
                j < ents.length ∧ L'.length = prev + j ∧ prevMatch L' prev pt ∧
                matchedUpTo L' prev ents j ∧ s.dur.1 < prev + 1 + j ∧
                ¬ (st1 ≠ stFollower ∧ ℓ = i)⌝ ∗
                srvOwn γ i { s with term := T, log := L' } ∗
                r.[Raft, go!"configurations"] ↦ configurations.mk ccfg' cidx' cfg' li' ∗
                cfgFacts γ L' L'.length a T cfg' ccfg' cidx' li'))) ∨
          (⌜v = returnVal #()⌝ ∗ srvOwn γ i { s with term := T } ∗ ghostVar rc.names.logPend (1 : Qp).half ([] : RLog) ∗ rtok tid ∗
            durView γ i (1 : Qp).half s.dur.1 ∗
            r.[Raft, go!"configurations"] ↦ configurations.mk ccfg cidx cfg cli)))
        at next with [-Hll Hrsp]
      · irename : (gi_ptr ↦ (Perennial.zero_val w64 : w64) : IProp GF) => Hgi
        ihave HI : (∃ (k : w64) (ev : Loc) (gv : w64), "i" ∷ i_ptr ↦ k ∗ "entry" ∷ entry_ptr ↦ ev ∗
            "Hgi" ∷ gi_ptr ↦ gv ∗
            "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z rq.Entries'.len ∧
              matchedUpTo s.log prev ents (sint.nat k)⌝ : IProp GF) $$ [i entry Hgi]
        · iexists W64 0, _, _
          iframe
          ipureintro
          refine ⟨by decide, by word, ?_⟩
          exact matched_zero _ _ _
        wp_for HI
        wp_if_destruct
        · simp only [Hk.1, Hif, _root_.and_self, ↓reduceIte]
          have hkl : sint.nat k < ptrs.length := by rw [Hentslen.1]; word
          obtain ⟨pk, Hpk_lookup⟩ : ∃ pk, ptrs[sint.nat k]? = some pk :=
            ⟨_, List.getElem?_eq_getElem hkl⟩
          wp_apply wp_load_slice_index rq.Entries' (sint.Z k) ptrs _ pk Hk.1 $$ [Hents] as -
          · iframe Hents; ipureintro
            rw [show (sint.Z k).toNat = sint.nat k from by word]; exact Hpk_lookup
          ihave Hpk := BigSepL.bigSepL_lookup Hpk_lookup $$ Hptrs
          icases Hpk with ⟨%e, %He, #Hlp⟩
          unfold logPtr
          icases Hlp with ⟨%lv, #Hlv, #Hlvi⟩
          unfold logIs
          icases Hlvi with ⟨%Hlvf, #Hlvd, #Hlve⟩
          iStructNamedSuffix Hlv "_e"
          wp_auto
          wp_if_destruct
          · -- past the end of the log: store from here
            simp only [show (0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z rq.Entries'.len ∧
                sint.Z rq.Entries'.len ≤ sint.Z rq.Entries'.cap) from ⟨Hk.1, Hk.2.1, Hentswf.2⟩,
              _root_.and_self, ↓reduceIte]
            by_cases Hns : st1 ≠ stFollower ∧ ℓ = i
            · obtain ⟨Hsc1, rfl⟩ := Hns
              ihave #Hli : leaderIs γ ({ s with term := T } : SState).term ℓ $$ [Hlead_l]
              · iexact Hlead_l
              imod aeValid_self γ ⊤ (by simp) ℓ { s with term := T } prev pt ents lci (sint.nat k) e He
                $$ [$HI $Hs $Hli $Hae] with ⟨-, %Hent⟩
              have hb := (ent_some_bound _ _ _ Hent).2
              exfalso; have h1 := Hlvf.1; have h2 := Hlxy.1; simp only at hb; word
            wp_auto
            wp_for_post
            q_exec
            iexists _
            iframe newEntries Htok Hdv Hpend
            iright
            iexists sint.nat k, s.log, cfg, ccfg, cidx, cli
            iframe Hs Hcfgs Hcf0
            ipureintro
            have hlen := len_eq_of_break' s.log prev pt ents (sint.nat k) Hpm Hk.2.2
              (by have := Hlvf.1; rw [← Hlxy.1]; word)
            refine ⟨by congr 1; word, by rw [← Hplen, Hentslen.1]; word, hlen, Hpm, Hk.2.2, ?_, Hns⟩
            have := Hsf.2.1; omega
          · -- an entry the log may have: compare terms
            rename_i storeEntry_ptr
            wp_apply_core HgetLog $$ storeEntry Htok
            iapply logCell_read γ rc i { s with term := T }
            iframe HI Hlc Hs Hpend
            iintro %A %HA
            unfold getLogPost
            split
            · rename_i e2 he2
              iintro Hs Hpend %err ⟨%Herr, %lv2, Hplv2, #Hlv2⟩ Htok
              unfold logIs
              icases Hlv2 with ⟨%Hlv2f, #Hlv2d, #Hlv2e⟩
              rw [Herr]
              wp_auto
              wp_if_destruct
              · -- same term: continue
                wp_for_post
                iframe
                iexists k + W64 1, _, _
                iframe
                ipureintro
                have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by
                  have := Hentslen.1; word
                refine ⟨by word, by word, ?_⟩
                rw [hk1]
                have he2' : ent s.log (prev + 1 + sint.nat k) = some e2 := by
                  rw [← Hlvf.1]; exact HA _ _ he2
                apply matched_step _ _ _ _ Hk.2.2 (by rw [← Hplen, Hentslen.1]; word)
                  (ent_some_bound _ _ _ he2').2
                rw [termAt_of_ent he2']
                have hee : ent ents (sint.nat k + 1) = some e := by
                  simp only [ent]; simp [He]
                rw [termAt_of_ent hee, ← Hlv2f.2.1, ← Hlvf.2.1]
                rw [Hif]
              · -- a conflict at prev+1+k: truncate
                have he2' : ent s.log (prev + 1 + sint.nat k) = some e2 := by
                  rw [← Hlvf.1]; exact HA _ _ he2
                have hb := (ent_some_bound _ _ _ he2').2
                have hee : ent ents (sint.nat k + 1) = some e := by
                  simp only [ent]; simp [He]
                have hne : termAt s.log (prev + 1 + sint.nat k) ≠ termAt ents (sint.nat k + 1) := by
                  rw [termAt_of_ent he2', termAt_of_ent hee, ← Hlv2f.2.1, ← Hlvf.2.1]
                  intro h; apply Hif; apply BitVec.eq_of_toNat_eq; exact h.symm
                have hklen : sint.nat k < ents.length := by rw [← Hplen, Hentslen.1]; word
                have hpre : prevMatch s.log prev pt ∧ matchedUpTo s.log prev ents (sint.nat k) ∧
                    sint.nat k < ents.length ∧ prev + 1 + sint.nat k ≤ s.log.length ∧
                    termAt s.log (prev + 1 + sint.nat k) ≠ termAt ents (sint.nat k + 1) :=
                  ⟨Hpm, Hk.2.2, hklen, hb, hne⟩
                by_cases Hns : st1 ≠ stFollower ∧ ℓ = i
                · obtain ⟨Hsc1, rfl⟩ := Hns
                  ihave #Hli : leaderIs γ ({ s with term := T } : SState).term ℓ $$ [Hlead_l]
                  · iexact Hlead_l
                  imod aeValid_self γ ⊤ (by simp) ℓ { s with term := T } prev pt ents lci (sint.nat k) e He
                    $$ [$HI $Hs $Hli $Hae] with ⟨-, %Hent⟩
                  exfalso; apply hne
                  simp only at Hent
                  rw [termAt_of_ent Hent, termAt_of_ent hee]
                imod truncate_gt_dur γ ⊤ (by simp) i { s with term := T } prev pt ents lci (sint.nat k)
                  hpre $$ [$HI $Hs $Hae] with ⟨Hs, %Hgt⟩
                -- the truncation point is above the committed configuration's index (cmtIdx_llog)
                ihave #Hle : llogIdx γ ({ s with term := T } : SState).term (prev + 1 + sint.nat k) e $$ []
                · iapply aeValid_ent γ T prev pt ents lci (sint.nat k) e He $$ Hae
                ihave #Hcm0 : cmtIdx γ ({ s with term := T } : SState).term ({ s with term := T } : SState).log
                    (uint.nat cidx) $$ []
                · iapply cfgFacts_cmt γ s.log s.log.length a T cfg ccfg cidx cli $$ Hcf0
                ihave %Hcf0p := cfgFacts_pure γ s.log s.log.length a T cfg ccfg cidx cli $$ Hcf0
                by_cases hci : prev + 1 + sint.nat k ≤ uint.nat cidx
                · imod cmtIdx_llog γ ⊤ (by simp) i { s with term := T } (uint.nat cidx) (prev + 1 + sint.nat k) e hci
                    $$ [$HI $Hs $Hcm0 $Hle] with ⟨-, %Hent⟩
                  exfalso; apply hne
                  simp only at Hent
                  rw [termAt_of_ent Hent, termAt_of_ent hee]
                have Hcix : uint.nat cidx < prev + 1 + sint.nat k := by omega
                ihave Hmn : (⌜uint.nat lx < 2 ^ 64 - 1⌝ : IProp GF) $$ []
                · ipureintro; have := Hsf.2.2.2.2.2.2.1; rw [Hlxy.1]; omega
                wp_apply_core HdelRange $$ Hmn
                iapply logCell_truncate γ rc i { s with term := T } prev pt ents lci (sint.nat k)
                  lv.Index' lx hpre Hlvf.1 Hlxy.1
                iframe HI Hlc Hs Hpend Hae
                iintro Hs Hpend
                wp_auto
                wp_join iprop(∃ (cfg' ccfg' : Configuration) (cidx' li' : w64),
                    r.[Raft, go!"configurations"] ↦ configurations.mk ccfg' cidx' cfg' li' ∗
                    cfgFacts γ (s.log.take (prev + sint.nat k)) (s.log.take (prev + sint.nat k)).length a T
                      cfg' ccfg' cidx' li') with [Hcfgs] as ⟨%cfg', %ccfg', %cidx', %li', Hcfgs, #Hcf1⟩
                · -- the rollback: the latest configuration becomes the committed one
                  ihave ⟨%ssc, #Hssc, %Hssc⟩ := cfgFacts_ccfg γ s.log s.log.length a T cfg ccfg cidx cli $$ Hcf0
                  wp_apply wp_setLatestConfiguration false r γ ccfg cfg cidx cli ccfg cidx ssc DFrac.discard null
                    $$ [$Hcfgs $Hssc] as ⟨Hcfgs, -, -⟩
                  · simp only [Bool.false_eq_true, ↓reduceIte]; iframe HlcI; ipureintro; exact Hssc
                  wp_join_done
                  iexists ccfg, ccfg, cidx, cidx
                  iframe Hcfgs
                  iapply cfgFacts_rollback γ s.log (prev + sint.nat k) a T cfg ccfg cidx cli (by omega)
                    (by have := Hlvf.1; word) $$ Hcf0
                · iexists cfg, ccfg, cidx, cli
                  iframe Hcfgs
                  iapply cfgFacts_trunc γ s.log (prev + sint.nat k) a T cfg ccfg cidx cli
                    (by have := Hlvf.1; word) $$ Hcf0
                simp only [show (0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z rq.Entries'.len ∧
                    sint.Z rq.Entries'.len ≤ sint.Z rq.Entries'.cap) from ⟨Hk.1, Hk.2.1, Hentswf.2⟩,
                  _root_.and_self, ↓reduceIte]
                wp_auto
                wp_for_post
                q_exec
                iexists _
                iframe newEntries Htok Hdv Hpend
                iright
                iexists sint.nat k, s.log.take (prev + sint.nat k), cfg', ccfg', cidx', li'
                iframe Hs Hcfgs Hcf1
                ipureintro
                obtain ⟨h1, h2, h3⟩ := matched_trunc s.log prev pt ents (sint.nat k) Hpm Hk.2.2 hb
                exact ⟨by congr 1; word, hklen, h3, h1, h2, Hgt, Hns⟩
            · iintro Hs Hpend %err ⟨%Herr, -, %lv2, Hplv2⟩ Htok
              cases err with
              | nil => exact absurd rfl Herr
              | ok ee =>
                wp_auto
                wp_for_post
                q_ret
                iframe
        · -- every entry was already in the log
          q_exec
          iexists _
          iframe newEntries Htok Hdv Hpend
          ileft
          iframe Hs Hcfgs
          isplitr
          · ipureintro; rfl
          ipureintro
          have : sint.nat k = ents.length := by rw [← Hplen, Hentslen.1]; word
          rw [← this]; exact Hk.2.2
      rename_i v2
      iintro (⟨%Hv2, %ns, newEntries, Htok, Hdv, Hpend, Hns⟩ | ⟨%Hv2, Hs, Hpend, Htok, Hdv, Hcfgs⟩)
      rotate_left
      · subst Hv2
        wp_auto
        q_ret
        iexists s.log, cfg, ccfg, cidx, cli
        iframe Hcf0
        iframe
        ipureintro; exact fun _ _ => ⟨rfl, rfl, rfl⟩
      subst Hv2
      icases Hns with (⟨%Hns, Hs, %Hmf, Hcfgs⟩ |
        ⟨%j, %L', %cfg', %ccfg', %cidx', %li', ⟨%Hns, %Hj, %HL', %HpL, %HmL, %Hdj, %Hnself⟩, Hs, Hcfgs, #Hcf'⟩)
      · subst Hns
        wp_auto
        q_exec
        iexists s.log, cfg, ccfg, cidx, cli
        iframe Hcf0
        iframe
        ipureintro; exact ⟨Hpm, Hmf, fun _ _ => ⟨rfl, rfl, rfl⟩⟩
      subst Hns
      ihave Hsub := (ownSlice_slice (W64 j) rq.Entries'.len rq.Entries' DFrac.discard ptrs
        ⟨by word, by word, by word⟩).1 $$ Hents
      icases Hsub with ⟨-, #Hsub, -⟩
      have Hjl : j < ptrs.length := by rw [Hplen]; exact Hj
      have hjw : sint.nat (W64 (j : Int)) = j := by rw [Hentslen.1] at Hjl; word
      have hss : subslice (sint.nat (W64 (j : Int))) (sint.nat rq.Entries'.len) ptrs = ptrs.drop j := by
        rw [hjw, ← Hentslen.1]; simp [subslice]
      ihave #Hsub2 : (slice.slice rq.Entries' Loc (W64 (j : Int)) rq.Entries'.len ↦*□ ptrs.drop j : IProp GF) $$ []
      · rw [← hss]; iexact Hsub
      have hsslen : (slice.slice rq.Entries' Loc (W64 (j : Int)) rq.Entries'.len).len =
          rq.Entries'.len - W64 (j : Int) := rfl
      wp_auto
      wp_if_destruct
      rotate_left
      · exfalso; rw [Hentslen.1] at Hjl; apply Hif; word
      have Hlen' := Hentslen.1
      rw [Hplen] at Hlen'
      have hb1 : 0 ≤ sint.Z (rq.Entries'.len - W64 (j : Int) - W64 1) ∧
          sint.Z (rq.Entries'.len - W64 (j : Int) - W64 1) < sint.Z (rq.Entries'.len - W64 (j : Int)) := by
        constructor <;> word
      rw [if_pos hb1]
      have hNj : (sint.Z (rq.Entries'.len - W64 (j : Int) - W64 1)).toNat = ents.length - 1 - j := by word
      obtain ⟨pL, HpLk⟩ : ∃ pL, ptrs[ents.length - 1]? = some pL :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      wp_apply wp_load_slice_index _ _ (ptrs.drop j) _ pL hb1.1 $$ [Hsub2] as -
      · iframe Hsub2; ipureintro; rw [hNj, List.getElem?_drop, ← HpLk]; congr 1; omega
      ihave HpLp := BigSepL.bigSepL_lookup HpLk $$ Hptrs
      icases HpLp with ⟨%eL, %HeL, #HlpL⟩
      unfold logPtr
      icases HlpL with ⟨%lvL, #HlvL, #HlviL⟩
      unfold logIs
      icases HlviL with ⟨%HlvLf, #HlvLd, #HlvLe⟩
      iStructNamedSuffix HlvL "_L"
      wp_auto
      wp_apply wp_min
      wp_apply wp_tryStageCommitIndex r γ rc i _ $$ [$Hr]
      ihave #Hpd := ptrs_drop ptrs ents prev j $$ [Hptrs]
      · unfold logPtr logIs; iexact Hptrs
      unfold logPtr logIs
      imod srvOwn_facts γ ⊤ (by simp) i _ $$ [$HI $Hs] with ⟨Hs, -, %HsfL⟩
      have hLb : L'.length < 2 ^ 62 := HsfL.2.2.2.2.2.2.1
      have hEb : ents.length < 2 ^ 63 := by rw [← Hplen, Hentslen.1]; word
      ihave Hpre : (⌜(ptrs.drop j).length = (ents.drop j).length ∧
          prev + 1 + j + (ents.drop j).length < 2 ^ 64⌝ : IProp GF) $$ []
      · ipureintro; simp [Hplen]; omega
      wp_apply_core HstoreLogs $$ Hpre Hsub2 Hpd
      iapply logCell_store γ rc i { s with term := T, log := L' } prev pt ents lci j ⟨HpL, HmL, Hj, HL'⟩
      iframe HI Hlc Hs Hpend Hae
      iintro Hs Hpend -
      imod srvOwn_facts γ ⊤ (by simp) i _ $$ [$HI $Hs] with ⟨Hs, -, %Hsf2⟩
      wp_auto
      ihave %Hsub2len := ownSlice_len _ _ _ $$ Hsub2
      ihave %Hcv := isRaft_cv r γ rc i $$ Hr
      ihave HI2 : (∃ (m : w64) (ne : Loc) (cfgm ccfgm : Configuration) (cidxm lim : w64),
          "i" ∷ i_ptr ↦ m ∗ "newEntry" ∷ newEntry_ptr ↦ ne ∗
          "Hcfgs" ∷ r.[Raft, go!"configurations"] ↦ configurations.mk ccfgm cidxm cfgm lim ∗
          "#Hcfm" ∷ cfgFacts γ (L' ++ ents.drop j) (prev + j + sint.nat m) a T cfgm ccfgm cidxm lim ∗
          "%Hm" ∷ ⌜0 ≤ sint.Z m ∧ sint.Z m ≤ sint.Z (rq.Entries'.len - W64 (j : Int))⌝ : IProp GF)
          $$ [i newEntry Hcfgs]
      · iexists W64 0, _, cfg', ccfg', cidx', li'
        iframe
        isplitr
        · rw [show prev + j + sint.nat (W64 0) = L'.length by rw [HL']; rfl]
          iapply cfgFacts_append γ L' (ents.drop j) a T cfg' ccfg' cidx' li' $$ Hcf'
        ipureintro; constructor <;> word
      wp_for HI2
      wp_if_destruct
      · have hm1 : 0 ≤ sint.Z m ∧ sint.Z m < sint.Z (rq.Entries'.len - W64 (j : Int)) := ⟨Hm.1, Hif⟩
        rw [if_pos hm1]
        have hml : j + sint.nat m < ptrs.length := by rw [Hplen, Hlen']; word
        obtain ⟨pm, Hpm_lookup⟩ : ∃ pm, ptrs[j + sint.nat m]? = some pm :=
          ⟨_, List.getElem?_eq_getElem hml⟩
        wp_apply wp_load_slice_index _ _ (ptrs.drop j) _ pm hm1.1 $$ [Hsub2] as -
        · iframe Hsub2; ipureintro
          rw [show (sint.Z m).toNat = sint.nat m from by word, List.getElem?_drop]; exact Hpm_lookup
        ihave Hpmp := BigSepL.bigSepL_lookup Hpm_lookup $$ Hptrs
        icases Hpmp with ⟨%em, %Hem, %lvm, #Hlvm, %Hlvmf, #Hlvmd, #Hlvme⟩
        have Hent := ent_store L' ents prev j (sint.nat m) HL'
        rw [Hem] at Hent
        have hkind2 := Hsf2.2.2.2.2.2.2.2.2 _ em Hent
        have hn1 : prev + 1 + j + sint.nat m = (prev + j + sint.nat m) + 1 := by omega
        rw [hn1] at Hent
        have hnL := (ent_some_bound _ _ _ Hent).2
        have hnb : prev + j + sint.nat m + 1 < 2 ^ 64 := by have := Hsf2.2.2.2.2.2.2.1; simp only at hnL this; omega
        have hm1' : sint.nat (m + W64 1) = sint.nat m + 1 := by word
        have ht := Hlvmf.2.2
        have hty23 : lvm.Type' ≠ W8 2 ∧ lvm.Type' ≠ W8 3 := by
          simp only [kCommand, kNoop, kBarrier, kConfig] at hkind2
          refine ⟨?_, ?_⟩ <;> intro h <;> rw [h] at ht <;> simp at ht <;> omega
        by_cases hk : em.kind = kConfig
        · -- a configuration entry: the latest becomes the committed configuration, the entry the latest
          have hcv := Hsf2.2.2.2.2.2.2.2.1 _ em Hent hk
          obtain ⟨ss, hd, hss⟩ := cfgDec_valid γ.srvs em.data (by rw [← Hcv]; exact hcv.1)
          wp_apply wp_processConfigurationLogEntry false r γ pm lvm DFrac.discard ccfgm cfgm cidxm lim null
            $$ [$Hlvm $Hcfgs] as ⟨-, Hpost⟩
          · isplitr; · ipureintro; exact hty23
            iright
            isplitr
            · iexists ss; rw [← hd]; iframe Hlvmd; ipureintro; exact hss
            simp only [Bool.false_eq_true, ↓reduceIte]; iexact HlcI
          icases Hpost with (⟨%Hne, -⟩ | ⟨%c, %ss', ⟨%Hty, %Hss'⟩, Hcfgs, #Hd', Hcs, -⟩)
          · exfalso; apply Hne; simp only [kConfig] at hk; rw [hk] at ht; word
          wp_for_post_core
          imod ownSlice_persist $$ Hcs with #Hcs
          ihave %hd' := ownSlice_agree _ _ _ _ _ $$ Hlvmd Hd'
          imod cfgPrevCommitted γ ⊤ (by simp) i { s with term := T, log := L' ++ ents.drop j }
            (prev + j + sint.nat m + 1) em Hent hk $$ [$HI $Hs] with ⟨Hs, #Hpc⟩
          ihave #Hcf2 := cfgFacts_step_cfg γ (L' ++ ents.drop j) (prev + j + sint.nat m) a T cfgm ccfgm c
            cidxm lim em ss' Hent hk hd' Hss' (by have := Ha.1; omega) hnb $$ [Hcfm Hcs Hpc]
          · iframe Hcfm Hcs
            simp only [Nat.add_sub_cancel]
            iexact Hpc
          have hix : lvm.Index' = W64 ((prev + j + sint.nat m + 1 : Nat) : Int) := by
            have := Hlvmf.1; word
          try wp_auto
          iframe
          iexists m + W64 1, _, c, cfgm, lim, lvm.Index'
          iframe
          rw [hm1', hix, show prev + j + (sint.nat m + 1) = prev + j + sint.nat m + 1 by omega]
          iframe Hcf2
          ipureintro; constructor <;> word
        · wp_apply wp_processConfigurationLogEntry false r γ pm lvm DFrac.discard ccfgm cfgm cidxm lim null
            $$ [$Hlvm $Hcfgs] as ⟨-, Hpost⟩
          · isplitr; · ipureintro; exact hty23
            ileft; ipureintro
            intro h; apply hk; rw [h] at ht; simp only [kConfig]; word
          icases Hpost with (⟨%Hne, Hcfgs⟩ | ⟨%c, %ss', ⟨%Hty, -⟩, -⟩)
          rotate_left
          · exfalso; apply hk; rw [Hty] at ht; simp only [kConfig]; word
          ihave #Hcf2 := cfgFacts_step_other γ (L' ++ ents.drop j) (prev + j + sint.nat m) a T cfgm ccfgm
            cidxm lim em Hent hk $$ Hcfm
          wp_for_post
          iframe
          iexists m + W64 1, _, cfgm, ccfgm, cidxm, lim
          iframe
          rw [hm1', show prev + j + (sint.nat m + 1) = prev + j + sint.nat m + 1 by omega]
          iframe Hcf2
          ipureintro; constructor <;> word
      · rw [if_pos hb1]
        wp_apply wp_load_slice_index _ _ (ptrs.drop j) _ pL hb1.1 $$ [Hsub2] as -
        · iframe Hsub2; ipureintro; rw [hNj, List.getElem?_drop, ← HpLk]; congr 1; omega
        wp_apply wp_setLastLog r γ rc i _ lvL.Index' lvL.Term' $$ [$Hr $Hll] as Hll
        q_exec
        iexists L' ++ ents.drop j, cfgm, ccfgm, cidxm, lim
        have hEL := ent_store L' ents prev j (ents.length - 1 - j) HL'
        rw [show j + (ents.length - 1 - j) = ents.length - 1 by omega, HeL] at hEL
        have hlenL : (L' ++ ents.drop j).length = prev + ents.length := by simp; omega
        have hlast : lastTerm (L' ++ ents.drop j) = eL.term := by
          unfold lastTerm; rw [hlenL]
          rw [show prev + ents.length = prev + 1 + j + (ents.length - 1 - j) by omega]
          exact termAt_of_ent hEL
        rw [show (uint.nat lvL.Index', uint.nat lvL.Term') = ((L' ++ ents.drop j).length,
            lastTerm (L' ++ ents.drop j)) by rw [hlenL, hlast, HlvLf.1, HlvLf.2.1]; congr 1; omega]
        have hmn : prev + j + sint.nat m = (L' ++ ents.drop j).length := by
          rw [hlenL]; have := Hm.2; have := Hlen'; word
        rw [hmn]
        iframe Hcfm
        iframe
        ipureintro
        exact ⟨(matched_store L' prev pt ents j HpL HmL HL' (by omega)).1,
          (matched_store L' prev pt ents j HpL HmL HL' (by omega)).2,
          fun h1 h2 => absurd ⟨h1, h2⟩ Hnself⟩
    · q_exec
      iexists s.log, cfg, ccfg, cidx, cli
      iframe Hcf0
      iframe
      ipureintro
      refine ⟨Hpm, ?_, fun _ _ => ⟨rfl, rfl, rfl⟩⟩
      have : ents.length = 0 := by rw [← Hplen, Hentslen.1]; word
      rw [this]; exact matched_zero _ _ _
  rename_i v3
  ihave #Hlciok := aeValid_lciOk γ T prev pt ents lci $$ Hae
  iintro (⟨%Hv3, %L5, %cfg5, %ccfg5, %cidx5, %li5, Hs, Hpend, Hll, Hrsp, Htok, Hdv, Hcfgs, #Hcf5, %Hm5⟩ |
    ⟨%Hv3, %L5, %cfg5, %ccfg5, %cidx5, %li5, Hs, Hpend, Hll, Hrsp, Htok, Hdv, Hcfgs, #Hcf5, %Hl5⟩)
  rotate_left
  · -- reading the store failed: respond (failure)
    subst Hv3
    wp_auto
    imod stArm_final γ i ℓ st1 T s.log L5 s.cidx s.cidx a a lci cidx cli cidx5 li5
      (fun h1 h2 => ⟨(Hl5 h1 h2).1, (Hl5 h1 h2).2.2⟩) (Nat.le_refl _) (Or.inl rfl)
      (Or.inl fun h1 h2 => (Hl5 h1 h2).2.1) $$ [$HI $Hlead_l $Hlciok $Hstl] with Hstl
    wp_apply wp_Respond rpc_ptr rpc γc _ _ _ $$ [$rpc $Hbag Hrsp] as rpc
    · iapply aeRespP_intro $$ [$Hrsp]
      iframe Hrvt
      isplitr
      · ileft; ipureintro; exact Hrv.2
      rw [Hrv.1]; unfold hdrOk; iexact Hh0
    iapply HΦ
    iexists { s with term := T, log := L5 }, st1
    iframe Htok
    isplitl [Hs Hdv HS Hll Hst Hstl Happ Hprod Hcfgs Hlown Hpend Hvreg Hpnd Hcomp]
    · ihave Hmo := mainOwnAt_ae r γ rc i { s with term := T, log := L5 } st1 a sst1 cfg5 ccfg5 cidx5 li5
        lch γl bs cmp Hvm1 Ha Hcmp Hcap $$ [Hs Hdv HS Hll Hst Hstl Happ Hprod Hcfgs Hlown Hpend Hvreg Hpnd Hcomp]
      · iframe; iframe #
      unfold mainOwnAt
      iexact Hmo
    iapply ae_post γ i ℓ st st1 s { s with term := T, log := L5 } T Hcase rfl (fun h1 h2 => (Hl5 h1 h2).1) $$ Hlead_l
  subst Hv3
  wp_auto
  wp_join iprop(∃ (d : Nat × Nat) (c : Nat) (a6 : Nat) (ccfg6 : Configuration) (cidx6 : w64),
      srvOwn γ i { s with term := T, log := L5, dur := d, cidx := c } ∗ durView γ i (1 : Qp).half d.1 ∗
      monoNatAuthOwn rc.names.applied (1 : Qp).half a6 ∗
      ⌜a6 ≤ d.1 ∧ a ≤ a6 ∧ c ≤ a6 ∧ (c = s.cidx ∨ c ≤ lci) ∧ (cidx6 = cidx5 ∨ uint.nat li5 ≤ c)⌝ ∗
      fsmProd γ rc a6 ∗
      r.[Raft, go!"configurations"] ↦ configurations.mk ccfg6 cidx6 cfg5 li5 ∗
      cfgFacts γ L5 L5.length a6 T cfg5 ccfg6 cidx6 li5 ∗
      rtok tid ∗ ghostVar rc.names.logPend (1 : Qp).half ([] : RLog) ∗ monoNatAuthOwn rc.names.comp 1 cmp)
    at next with [Hs Hdv Happ Hprod Hcfgs Htok Hpend Hcomp]
    as ⟨%d6, %c6, %a6, %ccfg6, %cidx6, Hs, Hdv, Happ, %Ha6, Hprod, Hcfgs, #Hcf6, Htok, Hpend, Hcomp⟩
  · imod srvOwn_facts γ ⊤ (by simp) i _ $$ [$HI $Hs] with ⟨Hs, -, %Hsf5⟩
    wp_if_destruct
    · wp_apply wp_getCommitIndex.1 r γ i { s with term := T, log := L5 } $$ [$HI $Hcc $Hs] as Hs
      wp_if_destruct
      · -- learn the commit index, up to the last index the request vouches for
        rename_i lastVouched_ptr
        wp_join iprop(∃ lvv : w64, lastVouched_ptr ↦ lvv ∗ ⌜uint.nat lvv = prev + ents.length⌝)
          with [lastVouched] as ⟨%lvv, lastVouched, %Hlvv⟩
        · have hl0 : 0 < ptrs.length := by rw [Hentslen.1]; word
          have hb1 : 0 ≤ sint.Z (rq.Entries'.len - W64 1) ∧ sint.Z (rq.Entries'.len - W64 1) < sint.Z rq.Entries'.len := by
            constructor <;> word
          rw [if_pos hb1]
          obtain ⟨pL, HpLk⟩ : ∃ pL, ptrs[ents.length - 1]? = some pL :=
            ⟨_, List.getElem?_eq_getElem (by omega)⟩
          wp_apply wp_load_slice_index _ _ ptrs _ pL hb1.1 $$ [Hents] as -
          · iframe Hents; ipureintro; rw [← HpLk]; congr 1; rw [← Hplen, Hentslen.1]; word
          ihave HpLp := BigSepL.bigSepL_lookup HpLk $$ Hptrs
          unfold logPtr logIs
          icases HpLp with ⟨%eL, %HeL, %lvL, #HlvL, %HlvLf, #HlvLd, #HlvLe⟩
          iStructNamedSuffix HlvL "_L"
          wp_auto
          wp_join_done
          iexists _
          iframe
          ipureintro; rw [HlvLf.1]; omega
        · iexists _
          iframe
          ipureintro; rw [Hpreve]
          have : ents.length = 0 := by rw [← Hplen, Hentslen.1]; word
          omega
        wp_apply wp_min
        have hidx : uint.nat (if uint.Z rq.LeaderCommitIndex' ≤ uint.Z lvv then rq.LeaderCommitIndex' else lvv) =
            Nat.min lci (prev + ents.length) := by
          rw [← Hlcie, ← Hlvv]; split <;> (simp only [Nat.min_def]; split <;> word)
        generalize hI : (if uint.Z rq.LeaderCommitIndex' ≤ uint.Z lvv then rq.LeaderCommitIndex' else lvv) = idx at hidx ⊢
        ihave Hlearn : (|={⊤}=> ∃ d : Nat × Nat, srvOwn γ i { s with term := T, log := L5, dur := d } ∗
            durView γ i (1 : Qp).half d.1 ∗ ⌜uint.nat idx ≤ d.1 ∧ s.dur.1 ≤ d.1⌝) $$ [Hs Hdv]
        · by_cases h0 : 0 < Nat.min lci (prev + ents.length)
          · imod learnCommitFollower γ ⊤ (by simp) i { s with term := T, log := L5 } prev pt ents lci
              (prev + ents.length) ⟨Hm5.1, Hm5.2.1, Nat.le_refl _, h0⟩ $$ [$HI $Hs $Hdv $Hae]
              with ⟨%d, Hs, Hdv, -, %Hd⟩
            imodintro
            iexists d
            iframe
            ipureintro; rw [hidx]
            simp only at Hd
            rw [Hd]; exact ⟨Nat.le_max_right _ _, Nat.le_max_left _ _⟩
          · imodintro
            iexists s.dur
            iframe
            ipureintro; rw [hidx]; exact ⟨by omega, Nat.le_refl _⟩
        imod Hlearn with ⟨%d, Hs, Hdv, %Hd⟩
        ihave Hupd := setCidx_step γ i { s with term := T, log := L5, dur := d } (uint.nat idx) Hd.1 $$ [$HI $Hs]
        wp_apply wp_setCommitIndex r γ i idx
          iprop(srvOwn γ i { s with term := T, log := L5, dur := d, cidx := uint.nat idx }) $$ [$Hcc $Hupd] as Hs
        ihave %Hcf5p := cfgFacts_pure γ L5 L5.length a T cfg5 ccfg5 cidx5 li5 $$ Hcf5
        wp_join iprop(∃ (ccfg6 : Configuration) (cidx6 : w64),
            srvOwn γ i { s with term := T, log := L5, dur := d, cidx := uint.nat idx } ∗
            r.[Raft, go!"configurations"] ↦ configurations.mk ccfg6 cidx6 cfg5 li5 ∗
            cfgFacts γ L5 L5.length (Max.max a (uint.nat idx)) T cfg5 ccfg6 cidx6 li5 ∗
            ⌜cidx6 = cidx5 ∨ uint.nat li5 ≤ uint.nat idx⌝)
          with [Hs Hcfgs] as ⟨%ccfg6, %cidx6, Hs, Hcfgs, #Hcf6, %Hcl6⟩
        · -- the commit index reaches the latest configuration: it is the committed one
          have hli : uint.nat li5 ≤ uint.nat idx := by word
          imod cmtIdx_dur γ ⊤ (by simp) i { s with term := T, log := L5, dur := d, cidx := uint.nat idx }
            (uint.nat li5) (by simp only; omega) $$ [$HI $Hs] with ⟨Hs, #Hcl⟩
          wp_apply wp_setCommittedConfiguration r ccfg5 cfg5 cidx5 li5 cfg5 li5 $$ [$Hcfgs] as Hcfgs
          wp_join_done
          iexists cfg5, li5
          iframe Hcfgs Hs
          isplitl
          · iapply cfgFacts_commit γ L5 L5.length a (Max.max a (uint.nat idx)) T cfg5 ccfg5 cidx5 li5
              $$ [$Hcf5 Hcl]
            iexact Hcl
          ipureintro; right; exact hli
        · iexists ccfg5, cidx5
          iframe Hcfgs Hs
          isplitl
          · iapply cfgFacts_mono_a γ L5 L5.length a (Max.max a (uint.nat idx)) T cfg5 ccfg5 cidx5 li5
              (fun h => by word) $$ Hcf5
          ipureintro; left; rfl
        wp_apply wp_processLogs r γ rc i idx _ ∅ _ a cmp tid $$ [$Hr $Hs $Hprod $Happ $Htok $Hpend $Hcomp]
          as ⟨Hs, Hprod, Happ, Hcomp, Htok, Hpend, -⟩
        · isplitr; · ipureintro; exact Hd.1
          isplitr; · ipureintro; exact Hcmp
          isplitr; · ileft; ipureintro; exact ⟨rfl, rfl⟩
          iapply BigSepM.bigSepM_empty.2; iempintro
        wp_join_done
        iexists d, uint.nat idx, Max.max a (uint.nat idx), ccfg6, cidx6
        iframe Hcf6
        iframe
        ipureintro
        refine ⟨Nat.max_le.2 ⟨by have := Ha.1; omega, Hd.1⟩, Nat.le_max_left _ _, Nat.le_max_right _ _,
          Or.inr (by rw [hidx]; exact Nat.min_le_left _ _), Hcl6⟩
      · wp_join_done
        iexists s.dur, s.cidx, a, ccfg5, cidx5
        iframe Hcf5
        iframe
        ipureintro; exact ⟨Ha.1, Nat.le_refl _, Ha.2, Or.inl rfl, Or.inl rfl⟩
    · wp_join_done
      iexists s.dur, s.cidx, a, ccfg5, cidx5
      iframe Hcf5
      iframe
      ipureintro; exact ⟨Ha.1, Nat.le_refl _, Ha.2, Or.inl rfl, Or.inl rfl⟩
  -- success: acknowledge, then respond
  imod stArm_final γ i ℓ st1 T s.log L5 s.cidx c6 a a6 lci cidx cli cidx6 li5
    (fun h1 h2 => ⟨(Hm5.2.2 h1 h2).1, (Hm5.2.2 h1 h2).2.2⟩) Ha6.2.1 Ha6.2.2.2.1
    (by rcases Ha6.2.2.2.2 with h | h
        · left; intro h1 h2; rw [h]; exact (Hm5.2.2 h1 h2).2.1
        · right; exact h) $$ [$HI $Hlead_l $Hlciok $Hstl] with Hstl
  wp_apply wp_setLastContact r γ rc i $$ [$Hr]
  imod ackFollower γ ⊤ (by simp) i { s with term := T, log := L5, dur := d6, cidx := c6 } prev pt ents lci
    ⟨Hm5.1, Hm5.2.1⟩ $$ [$HI $Hs $Hae] with ⟨Hs, #Hack⟩
  imod srvOwn_now γ ⊤ (by simp) i _ ss $$ [$HI $Hs $Hss] with ⟨Hs, %sq, #Hsq, %Hsq⟩
  wp_apply wp_Respond rpc_ptr rpc γc _ _ _ $$ [$rpc $Hbag Hrsp] as rpc
  · iapply aeRespP_intro $$ [$Hrsp]
    iframe Hrvt
    isplitr
    · iright
      isplitr
      · iright; iexact Hack
      unfold respWit
      iexists sq
      iframe Hsq
      ipureintro; exact ⟨Hsq.1, Hsq.2.1⟩
    rw [Hrv.1]; unfold hdrOk; iexact Hh0
  iapply HΦ
  iexists { s with term := T, log := L5, dur := d6, cidx := c6 }, st1
  iframe Htok
  isplitl [Hs Hdv HS Hll Hst Hstl Happ Hprod Hcfgs Hlown Hpend Hvreg Hpnd Hcomp]
  · ihave Hmo := mainOwnAt_ae r γ rc i { s with term := T, log := L5, dur := d6, cidx := c6 } st1 a6 sst1
      cfg5 ccfg6 cidx6 li5 lch γl bs cmp Hvm1 ⟨Ha6.1, Ha6.2.2.1⟩ (by omega) Hcap
      $$ [Hs Hdv HS Hll Hst Hstl Happ Hprod Hcfgs Hlown Hpend Hvreg Hpnd Hcomp]
    · iframe; iframe #
    unfold mainOwnAt
    iexact Hmo
  iapply ae_post γ i ℓ st st1 s { s with term := T, log := L5, dur := d6, cidx := c6 } T Hcase rfl
    (fun h1 h2 => (Hm5.2.2 h1 h2).1) $$ Hlead_l
