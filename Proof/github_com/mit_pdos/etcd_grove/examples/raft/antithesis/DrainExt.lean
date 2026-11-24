/-
Lean-first (no Rocq counterpart). #33 S4: **raft's facts grown by a drain's reports**
(`Cluster__drain.lean`'s `factsExt`): one fact at a time, each keeping `RaftLaws` from raft's
agreement lemmas between the new fact and those already in `raftFactsOwn`: a certified log
(`logRecs_agree`, `logMatch_of_recs`), a longer committed log (`isCommitted_agree`), a vote
(`isVote_agree`), a leader with its campaign log (`isLeader_unique`, `commitIn_camp` against every
recorded commit, `isCamp_ok`), a commit recorded in a term (`commitIn_camp` against every campaign).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainFacts
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainReports
public import Proof.go_etcd_io.raft.v3.Protocol.CommitCamp

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## Pure pieces -/

section pure
variable [GooseExts]

theorem logIdx_of_wf {l : List EntryM} (h : PlogWf base0 l) : AntSim.LogIdx l := by
  intro k e hk
  have := h k e hk
  rw [base0_index] at this
  push_cast at this
  omega

theorem logIdx_prefix {l l' : List EntryM} (h : AntSim.LogIdx l) (hp : l' <+: l) :
    AntSim.LogIdx l' := by
  obtain ⟨t, rfl⟩ := hp
  intro k e hk
  have hlt := (List.getElem?_eq_some_iff.1 hk).1
  exact h k e (by rw [List.getElem?_append_left hlt]; exact hk)

theorem plogWf_prefix {l l' : List EntryM} (h : PlogWf base0 l) (hp : l' <+: l) :
    PlogWf base0 l' := by
  obtain ⟨t, rfl⟩ := hp
  intro k e hk
  have hlt := (List.getElem?_eq_some_iff.1 hk).1
  exact h k e (by rw [List.getElem?_append_left hlt]; exact hk)

/-- A campaign log's entries are of earlier terms (`CampOk`). -/
theorem campTerms_of_ok {T : w64} {F : List EntryM} (h : CampOk T F) :
    ∀ e ∈ F, uint.Z e.Term' < uint.Z T := by
  intro e he
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 he
  have hk' : F[k]? = some F[k] := List.getElem?_eq_getElem hk
  have hlt := logIdx_lt (logIdx_of_wf h.1) hk'
  apply h.2 (pidx base0 (k + 1))
  rw [plogTermAt_base0_succ k hlt, hk']
  rfl

/-- `l'` a prefix of `l` of length at least `n`: their first `n` entries agree. -/
theorem take_of_prefix {l l' : List EntryM} {n : Nat} (hp : l' <+: l) (hn : n ≤ l'.length) :
    l.take n = l'.take n := by
  obtain ⟨t, rfl⟩ := hp
  rw [List.take_append_of_le_length hn]

/-! ### The facts, grown -/

def RaftFacts.addLog (G : AntSim.RaftFacts) (l : List EntryM) : AntSim.RaftFacts :=
  { G with logs := l :: G.logs }

def RaftFacts.addVote (G : AntSim.RaftFacts) (v : w64 × w64 × w64) : AntSim.RaftFacts :=
  { G with votes := v :: G.votes }

def RaftFacts.addLeader (G : AntSim.RaftFacts) (id T : w64) (F0 : List EntryM) :
    AntSim.RaftFacts :=
  { G with leaders := (id, T) :: G.leaders, camps := (T, F0) :: G.camps }

def RaftFacts.setCommitted (G : AntSim.RaftFacts) (L : List EntryM) : AntSim.RaftFacts :=
  { G with committed := L }

def RaftFacts.addCommit (G : AntSim.RaftFacts) (x : w64 × Nat) : AntSim.RaftFacts :=
  { G with commits := x :: G.commits }

theorem raftLaws_addLog {G : AntSim.RaftFacts} {l : List EntryM} (hL : AntSim.RaftLaws G)
    (hl : AntSim.LogIdx l) (hself : RecsAgree base0 l base0 l)
    (hag : ∀ b ∈ G.logs, RecsAgree base0 l base0 b ∧ RecsAgree base0 b base0 l ∧ AntSim.LogIdx b) :
    AntSim.RaftLaws (RaftFacts.addLog G l) ∧ RaftFacts.Le G (RaftFacts.addLog G l) := by
  obtain ⟨hld, hvt, hm, hcm, hcamp, hcmts, hct⟩ := hL
  refine ⟨⟨hld, hvt, ?_, List.mem_cons_of_mem _ hcm, fun p hp => List.mem_cons_of_mem _ (hcamp p hp),
    hcmts, hct⟩, fun _ h => h, fun _ h => h, fun _ h => List.mem_cons_of_mem _ h, fun _ h => h,
    List.prefix_refl _, fun _ h => h⟩
  intro a ha b hb
  simp only [RaftFacts.addLog, List.mem_cons] at ha hb
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · exact logMatch_of_recs hl hl hself
  · exact logMatch_of_recs hl (hag b hb).2.2 (hag b hb).1
  · exact logMatch_of_recs (hag a ha).2.2 hl (hag a ha).2.1
  · exact hm a ha b hb

theorem raftLaws_addVote {G : AntSim.RaftFacts} {v : w64 × w64 × w64} (hL : AntSim.RaftLaws G)
    (hag : ∀ b ∈ G.votes, b.1 = v.1 → b.2.1 = v.2.1 → b.2.2 = v.2.2) :
    AntSim.RaftLaws (RaftFacts.addVote G v) ∧ RaftFacts.Le G (RaftFacts.addVote G v) := by
  obtain ⟨hld, hvt, hm, hcm, hcamp, hcmts, hct⟩ := hL
  refine ⟨⟨hld, ?_, hm, hcm, hcamp, hcmts, hct⟩, fun _ h => h, fun _ h => List.mem_cons_of_mem _ h,
    fun _ h => h, fun _ h => h, List.prefix_refl _, fun _ h => h⟩
  intro a ha b hb h1 h2
  simp only [RaftFacts.addVote, List.mem_cons] at ha hb
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · rfl
  · exact (hag b hb h1.symm h2.symm).symm
  · exact hag a ha h1 h2
  · exact hvt a ha b hb h1 h2

theorem raftLaws_setCommitted {G : AntSim.RaftFacts} {L : List EntryM} (hL : AntSim.RaftLaws G)
    (hp : G.committed <+: L) (hLm : L ∈ G.logs) :
    AntSim.RaftLaws (RaftFacts.setCommitted G L) ∧ RaftFacts.Le G (RaftFacts.setCommitted G L) := by
  obtain ⟨hld, hvt, hm, hcm, hcamp, hcmts, hct⟩ := hL
  refine ⟨⟨hld, hvt, hm, hLm, hcamp, ?_, hct⟩, fun _ h => h, fun _ h => h, fun _ h => h,
    fun _ h => h, hp, fun _ h => h⟩
  intro x hx
  obtain ⟨hle, hc⟩ := hcmts x hx
  refine ⟨Nat.le_trans hle hp.length_le, fun p hpc hlt => ?_⟩
  simp only [RaftFacts.setCommitted]
  rw [take_of_prefix hp hle]
  exact hc p hpc hlt

theorem raftLaws_addLeader {G : AntSim.RaftFacts} {id T : w64} {F0 : List EntryM}
    (hL : AntSim.RaftLaws G) (hF0 : F0 ∈ G.logs) (hok : ∀ e ∈ F0, uint.Z e.Term' < uint.Z T)
    (hld' : ∀ b ∈ G.leaders, b.2 = T → b.1 = id)
    (hcmt : ∀ x ∈ G.commits, uint.Z x.1 < uint.Z T → G.committed.take x.2 <+: F0) :
    AntSim.RaftLaws (RaftFacts.addLeader G id T F0) ∧
      RaftFacts.Le G (RaftFacts.addLeader G id T F0) := by
  obtain ⟨hld, hvt, hm, hcm, hcamp, hcmts, hct⟩ := hL
  refine ⟨⟨?_, hvt, hm, hcm, ?_, ?_, ?_⟩, fun _ h => List.mem_cons_of_mem _ h, fun _ h => h,
    fun _ h => h, fun _ h => List.mem_cons_of_mem _ h, List.prefix_refl _, fun _ h => h⟩
  · intro a ha b hb h
    simp only [RaftFacts.addLeader, List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact (hld' b hb h.symm).symm
    · exact hld' a ha h
    · exact hld a ha b hb h
  · intro p hp
    simp only [RaftFacts.addLeader, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hF0
    · exact hcamp p hp
  · intro x hx
    obtain ⟨hle, hc⟩ := hcmts x hx
    refine ⟨hle, fun p hp hlt => ?_⟩
    simp only [RaftFacts.addLeader, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hcmt x hx hlt
    · exact hc p hp hlt
  · intro p hp
    simp only [RaftFacts.addLeader, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hok
    · exact hct p hp

theorem raftLaws_addCommit {G : AntSim.RaftFacts} {x : w64 × Nat} (hL : AntSim.RaftLaws G)
    (hle : x.2 ≤ G.committed.length)
    (hcmt : ∀ p ∈ G.camps, uint.Z x.1 < uint.Z p.1 → G.committed.take x.2 <+: p.2) :
    AntSim.RaftLaws (RaftFacts.addCommit G x) ∧ RaftFacts.Le G (RaftFacts.addCommit G x) := by
  obtain ⟨hld, hvt, hm, hcm, hcamp, hcmts, hct⟩ := hL
  refine ⟨⟨hld, hvt, hm, hcm, hcamp, ?_, hct⟩, fun _ h => h, fun _ h => h, fun _ h => h,
    fun _ h => h, List.prefix_refl _, fun _ h => List.mem_cons_of_mem _ h⟩
  intro y hy
  simp only [RaftFacts.addCommit, List.mem_cons] at hy
  rcases hy with rfl | hy
  · exact ⟨hle, hcmt⟩
  · exact hcmts y hy

end pure

/-! ## The facts' ghost side -/

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- A pure fact of every element of a list from a resource per element (persistent context `P`). -/
theorem bigSepL_pure_all {A : Type} {P : IProp GF} {Φ : A → IProp GF} (L : List A) (R : A → Prop)
    (h : ∀ a, a ∈ L → P ∗ Φ a ⊢ ⌜R a⌝) :
    P ∗ ([∗list] a ∈ L, Φ a) ⊢ ⌜∀ a ∈ L, R a⌝ := by
  by_cases H : ∀ a ∈ L, R a
  · iintro -; ipureintro; exact H
  · simp only [Classical.not_forall] at H
    obtain ⟨a, ha, hn⟩ := H
    iintro ⟨HP, Hl⟩
    ihave Ha := BigSepL.bigSepL_mem (Φ := Φ) ha $$ Hl
    ihave %Hr := h a ha $$ [HP Ha]
    · iframe HP Ha
    exact absurd Hr hn

/-- The same, the fact under an update (`commitIn_camp`). -/
theorem bigSepL_pure_all_upd {A : Type} {P : IProp GF} {Φ : A → IProp GF} (E : CoPset) (L : List A)
    (R : A → Prop) (h : ∀ a, a ∈ L → P ∗ Φ a ⊢ |={E}=> ⌜R a⌝) :
    P ∗ ([∗list] a ∈ L, Φ a) ⊢ |={E}=> ⌜∀ a ∈ L, R a⌝ := by
  by_cases H : ∀ a ∈ L, R a
  · iintro -; imodintro; ipureintro; exact H
  · simp only [Classical.not_forall] at H
    obtain ⟨a, ha, hn⟩ := H
    iintro ⟨HP, Hl⟩
    ihave Ha := BigSepL.bigSepL_mem (Φ := Φ) ha $$ Hl
    imod h a ha $$ [HP Ha] with %Hr
    · iframe HP Ha
    exact absurd Hr hn

/-! ### Pairwise agreement of single facts -/

theorem recs_pair (γ : RaftNames) (l b : List EntryM) :
    logRecs (GF := GF) γ base0 l ∗ iprop(logRecs γ base0 b ∗ ⌜AntSim.LogIdx b⌝) ⊢
      ⌜RecsAgree base0 l base0 b ∧ RecsAgree base0 b base0 l ∧ AntSim.LogIdx b⌝ := by
  iintro ⟨#Hl, #Hb, %Hi⟩
  ihave %H1 := logRecs_agree γ base0 l base0 b $$ Hl Hb
  ihave %H2 := logRecs_agree γ base0 b base0 l $$ Hb Hl
  ipureintro; exact ⟨H1, H2, Hi⟩

theorem vote_pair (γ : RaftNames) (v b : w64 × w64 × w64) :
    isVote (GF := GF) γ v.1 v.2.1 v.2.2 ∗ isVote γ b.1 b.2.1 b.2.2 ⊢
      ⌜b.1 = v.1 → b.2.1 = v.2.1 → b.2.2 = v.2.2⌝ := by
  obtain ⟨v1, v2, v3⟩ := v
  obtain ⟨b1, b2, b3⟩ := b
  by_cases h : b1 = v1 ∧ b2 = v2
  · obtain ⟨rfl, rfl⟩ := h
    iintro ⟨#H1, #H2⟩
    ihave %H := isVote_agree γ b1 b2 b3 v3 $$ H2 H1
    ipureintro; intro _ _; exact H
  · iintro -
    ipureintro; intro h1 h2; exact absurd ⟨h1, h2⟩ h

theorem leader_pair (γ : RaftNames) (id T : w64) (b : w64 × w64) :
    isLeader (GF := GF) γ id T ∗ isLeader γ b.1 b.2 ⊢ ⌜b.2 = T → b.1 = id⌝ := by
  obtain ⟨b1, b2⟩ := b
  by_cases h : b2 = T
  · subst h
    iintro ⟨#H1, #H2⟩
    ihave %H := isLeader_unique γ b1 id b2 $$ H2 H1
    ipureintro; intro _; exact H
  · iintro -
    ipureintro; intro h'; exact absurd h' h

/-- The commits' entries kept by a longer committed log. -/
theorem commits_mono (γ : RaftNames) (cs : List (w64 × Nat)) (C C' : List EntryM)
    (h : C <+: C') :
    ([∗list] x ∈ cs, ∃ F : List EntryM,
      commitIn (GF := GF) γ F (W64 (x.2 : Int)) x.1 ∗ logRecs γ base0 F ∗
      ⌜PlogWf base0 F ∧ x.2 ≤ F.length ∧ (x.2 : Int) < 2 ^ 64 ∧ F.take x.2 <+: C⌝) ⊢
    ([∗list] x ∈ cs, ∃ F : List EntryM,
      commitIn (GF := GF) γ F (W64 (x.2 : Int)) x.1 ∗ logRecs γ base0 F ∗
      ⌜PlogWf base0 F ∧ x.2 ≤ F.length ∧ (x.2 : Int) < 2 ^ 64 ∧ F.take x.2 <+: C'⌝) := by
  refine BigSepL.bigSepL_mono_of_forall (fun {k x} => ?_)
  iintro ⟨%F, #H1, #H2, %Hp⟩
  iexists F
  iframe H1 H2
  ipureintro
  exact ⟨Hp.1, Hp.2.1, Hp.2.2.1, Hp.2.2.2.trans h⟩

theorem w64_nat_cast {n : Nat} (h : (n : Int) < 2 ^ 64) : uint.nat (W64 (n : Int)) = n := by
  word

/-- **A recorded commit against a campaign of a later term** (`commitIn_camp`): the committed log's
prefix at the commit is within the campaign log. -/
theorem commit_camp_pair (γ : RaftNames) (C : List EntryM) (x : w64 × Nat) (id T : w64)
    (F0 : List EntryM) (hboot : γ.reBoot = []) :
    iprop(raftCommitInv (GF := GF) γ ∗ isLeader γ id T ∗ isCamp γ id T F0 ∗ logRecs γ base0 F0) ∗
      iprop(∃ F : List EntryM, commitIn γ F (W64 (x.2 : Int)) x.1 ∗ logRecs γ base0 F ∗
        ⌜PlogWf base0 F ∧ x.2 ≤ F.length ∧ (x.2 : Int) < 2 ^ 64 ∧ F.take x.2 <+: C⌝) ⊢
      |={↑(raftN γ)}=> ⌜uint.Z x.1 < uint.Z T → C.take x.2 <+: F0⌝ := by
  by_cases hlt : uint.Z x.1 < uint.Z T
  · iintro ⟨⟨#Hinv, #Hl, #Hc, #HrF0⟩, ⟨%F, #Hcm, #HrF, %Hp⟩⟩
    obtain ⟨hwf, hle, hlt64, hpre⟩ := Hp
    imod commitIn_camp γ F (W64 (x.2 : Int)) x.1 id T F0 F0 hboot hlt hwf (List.prefix_refl _)
      $$ Hinv Hcm HrF Hl Hc HrF0 with %H
    imodintro
    ipureintro
    intro _
    rw [w64_nat_cast hlt64] at H
    have hlen : (F.take x.2).length = x.2 := by simp [hle]
    have := List.prefix_iff_eq_take.1 hpre
    rw [hlen] at this
    rw [← this]; exact H
  · iintro -
    imodintro; ipureintro; intro h; exact absurd h hlt

/-! ### Each fact added -/

theorem raftFacts_addLog (γ : RaftNames) (G : AntSim.RaftFacts) (l : List EntryM)
    (hL : AntSim.RaftLaws G) (hl : AntSim.LogIdx l) :
    raftFactsOwn (GF := GF) γ G ∗ logRecs γ base0 l ⊢
      raftFactsOwn γ (RaftFacts.addLog G l) ∗
        ⌜AntSim.RaftLaws (RaftFacts.addLog G l) ∧ RaftFacts.Le G (RaftFacts.addLog G l)⌝ := by
  iintro ⟨#HF, #Hl⟩
  iunfold raftFactsOwn at HF
  icases HF with ⟨#Hld, #Hvt, #Hlogs, #Hcamps, #Hcm, #Hcmts⟩
  ihave %Hself := logRecs_agree γ base0 l base0 l $$ Hl Hl
  ihave %Hag := bigSepL_pure_all (P := logRecs γ base0 l)
      (Φ := fun b => iprop(logRecs γ base0 b ∗ ⌜AntSim.LogIdx b⌝)) G.logs
      (fun b => RecsAgree base0 l base0 b ∧ RecsAgree base0 b base0 l ∧ AntSim.LogIdx b)
      (fun b _ => recs_pair γ l b) $$ [Hl Hlogs]
  · iframe Hl Hlogs
  isplitl
  · iunfold raftFactsOwn
    simp only [RaftFacts.addLog]
    iframe Hld Hvt Hcamps Hcm Hcmts
    iapply BigSepL.bigSepL_cons.2
    iframe Hl Hlogs
    ipureintro; exact hl
  · ipureintro; exact raftLaws_addLog hL hl Hself Hag

theorem raftFacts_addVote (γ : RaftNames) (G : AntSim.RaftFacts) (v : w64 × w64 × w64)
    (hL : AntSim.RaftLaws G) :
    raftFactsOwn (GF := GF) γ G ∗ isVote γ v.1 v.2.1 v.2.2 ⊢
      raftFactsOwn γ (RaftFacts.addVote G v) ∗
        ⌜AntSim.RaftLaws (RaftFacts.addVote G v) ∧ RaftFacts.Le G (RaftFacts.addVote G v)⌝ := by
  iintro ⟨#HF, #Hv⟩
  iunfold raftFactsOwn at HF
  icases HF with ⟨#Hld, #Hvt, #Hlogs, #Hcamps, #Hcm, #Hcmts⟩
  ihave %Hag := bigSepL_pure_all (P := isVote γ v.1 v.2.1 v.2.2)
      (Φ := fun b => isVote γ b.1 b.2.1 b.2.2) G.votes
      (fun b => b.1 = v.1 → b.2.1 = v.2.1 → b.2.2 = v.2.2)
      (fun b _ => vote_pair γ v b) $$ [Hv Hvt]
  · iframe Hv Hvt
  isplitl
  · iunfold raftFactsOwn
    simp only [RaftFacts.addVote]
    iframe Hld Hlogs Hcamps Hcm Hcmts
    iapply BigSepL.bigSepL_cons.2
    iframe Hv Hvt
  · ipureintro; exact raftLaws_addVote hL Hag

/-- A longer committed log (or the same facts, when it is not longer). -/
theorem raftFacts_committed (γ : RaftNames) (G : AntSim.RaftFacts) (L : List EntryM)
    (hL : AntSim.RaftLaws G) (hLm : L ∈ G.logs) :
    raftFactsOwn (GF := GF) γ G ∗ isCommitted γ L ⊢
      ∃ G' : AntSim.RaftFacts, raftFactsOwn γ G' ∗
        ⌜AntSim.RaftLaws G' ∧ RaftFacts.Le G G' ∧ L <+: G'.committed⌝ := by
  iintro ⟨#HF, #HL⟩
  iunfold raftFactsOwn at HF
  icases HF with ⟨#Hld, #Hvt, #Hlogs, #Hcamps, #Hcm, #Hcmts⟩
  ihave %Hag := isCommitted_agree γ L G.committed $$ HL Hcm
  rcases Hag with hp | hp
  · iexists G
    iunfold raftFactsOwn
    iframe Hld Hvt Hlogs Hcamps Hcm Hcmts
    ipureintro; exact ⟨hL, RaftFacts.Le.refl G, hp⟩
  · iexists RaftFacts.setCommitted G L
    iunfold raftFactsOwn
    simp only [RaftFacts.setCommitted]
    iframe Hld Hvt Hlogs Hcamps HL
    isplitl
    · iapply commits_mono γ G.commits G.committed L hp $$ Hcmts
    · ipureintro
      obtain ⟨h1, h2⟩ := raftLaws_setCommitted hL hp hLm
      exact ⟨h1, h2, List.prefix_refl _⟩

theorem raftFacts_addLeader (γ : RaftNames) (G : AntSim.RaftFacts) (id T : w64)
    (F0 : List EntryM) (hL : AntSim.RaftLaws G) (hF0 : F0 ∈ G.logs) (hboot : γ.reBoot = []) :
    raftFactsOwn (GF := GF) γ G ∗ raftCommitInv γ ∗ isLeader γ id T ∗ isCamp γ id T F0 ⊢
      |={↑(raftN γ)}=> raftFactsOwn γ (RaftFacts.addLeader G id T F0) ∗
        ⌜AntSim.RaftLaws (RaftFacts.addLeader G id T F0) ∧
          RaftFacts.Le G (RaftFacts.addLeader G id T F0)⌝ := by
  iintro ⟨#HF, #Hinv, #Hl, #Hc⟩
  iunfold raftFactsOwn at HF
  icases HF with ⟨#Hld, #Hvt, #Hlogs, #Hcamps, #Hcm, #Hcmts⟩
  ihave ⟨#HrF0, -⟩ := BigSepL.bigSepL_mem
      (Φ := fun b => iprop(logRecs (GF := GF) γ base0 b ∗ ⌜AntSim.LogIdx b⌝)) hF0 $$ Hlogs
  ihave %Hld' := bigSepL_pure_all (P := isLeader γ id T)
      (Φ := fun (b : w64 × w64) => isLeader γ b.1 b.2) G.leaders
      (fun (b : w64 × w64) => b.2 = T → b.1 = id)
      (fun b _ => leader_pair (GF := GF) γ id T b) $$ [Hl Hld]
  · iframe Hl Hld
  ihave %Hok := isCamp_ok γ id T F0 $$ Hc
  have key := bigSepL_pure_all_upd (GF := GF)
      (P := iprop(raftCommitInv γ ∗ isLeader γ id T ∗ isCamp γ id T F0 ∗ logRecs γ base0 F0))
      (Φ := fun (x : w64 × Nat) => iprop(∃ F : List EntryM, commitIn γ F (W64 (x.2 : Int)) x.1 ∗
        logRecs γ base0 F ∗
        ⌜PlogWf base0 F ∧ x.2 ≤ F.length ∧ (x.2 : Int) < 2 ^ 64 ∧ F.take x.2 <+: G.committed⌝))
      ↑(raftN γ) G.commits (fun (x : w64 × Nat) => uint.Z x.1 < uint.Z T → G.committed.take x.2 <+: F0)
      (fun x _ => commit_camp_pair (GF := GF) γ G.committed x id T F0 hboot)
  imod key $$ [Hinv Hl Hc HrF0 Hcmts] with %Hcmt
  · isplitl [Hinv Hl Hc HrF0]
    · iframe Hinv Hl Hc HrF0
    · iexact Hcmts
  imodintro
  isplitl
  · iunfold raftFactsOwn
    simp only [RaftFacts.addLeader]
    iframe Hvt Hlogs Hcm Hcmts
    isplitl
    · iapply BigSepL.bigSepL_cons.2
      iframe Hl Hld
    · iapply BigSepL.bigSepL_cons.2
      iframe Hcamps
      iexists id
      iframe Hl Hc
  · ipureintro
    exact raftLaws_addLeader hL hF0 (campTerms_of_ok Hok) Hld' (fun x hx h => Hcmt x hx h)

/-- **A recorded commit** `(t, c)` at the log `L`, against every campaign of a later term. -/
theorem raftFacts_addCommit (γ : RaftNames) (G : AntSim.RaftFacts) (L : List EntryM) (t : w64)
    (c : Nat) (hL : AntSim.RaftLaws G) (hboot : γ.reBoot = []) (hwf : PlogWf base0 L)
    (hc : c ≤ L.length) (hc64 : (c : Int) < 2 ^ 64) (hpre : L.take c <+: G.committed) :
    raftFactsOwn (GF := GF) γ G ∗ raftCommitInv γ ∗ commitIn γ L (W64 (c : Int)) t ∗
        logRecs γ base0 L ⊢
      |={↑(raftN γ)}=> raftFactsOwn γ (RaftFacts.addCommit G (t, c)) ∗
        ⌜AntSim.RaftLaws (RaftFacts.addCommit G (t, c)) ∧
          RaftFacts.Le G (RaftFacts.addCommit G (t, c))⌝ := by
  iintro ⟨#HF, #Hinv, #Hcm', #HrL⟩
  iunfold raftFactsOwn at HF
  icases HF with ⟨#Hld, #Hvt, #Hlogs, #Hcamps, #Hcm, #Hcmts⟩
  have hcamp := hL.2.2.2.2.1
  imod bigSepL_pure_all_upd (P := iprop(raftCommitInv γ ∗ commitIn γ L (W64 (c : Int)) t ∗
      logRecs γ base0 L ∗ [∗list] l ∈ G.logs, logRecs γ base0 l ∗ ⌜AntSim.LogIdx l⌝))
      (Φ := fun p => iprop(∃ c : w64, isLeader γ c p.1 ∗ isCamp γ c p.1 p.2))
      ↑(raftN γ) G.camps (fun p => uint.Z t < uint.Z p.1 → G.committed.take c <+: p.2)
      (fun p hp => by
        iintro ⟨⟨#Hinv, #Hcm', #HrL, #Hlogs⟩, ⟨%cc, #Hl, #Hc⟩⟩
        ihave ⟨#Hr, -⟩ := BigSepL.bigSepL_mem
            (Φ := fun b => iprop(logRecs (GF := GF) γ base0 b ∗ ⌜AntSim.LogIdx b⌝)) (hcamp p hp)
            $$ Hlogs
        iapply commit_camp_pair γ G.committed (t, c) cc p.1 p.2 hboot $$ [Hinv Hl Hc Hr Hcm' HrL]
        isplitl [Hinv Hl Hc Hr]
        · iframe Hinv Hl Hc Hr
        iexists L
        iframe Hcm' HrL
        ipureintro; exact ⟨hwf, hc, hc64, hpre⟩)
      $$ [Hinv Hcm' HrL Hlogs Hcamps] with %Hcmt
  · iframe Hinv Hcm' HrL Hlogs Hcamps
  imodintro
  isplitl
  · iunfold raftFactsOwn
    simp only [RaftFacts.addCommit]
    iframe Hld Hvt Hlogs Hcamps Hcm
    iapply BigSepL.bigSepL_cons.2
    iframe Hcmts
    iexists L
    iframe Hcm' HrL
    ipureintro; exact ⟨hwf, hc, hc64, hpre⟩
  · ipureintro
    have hle : c ≤ G.committed.length := by
      have := hpre.length_le; simp at this; omega
    exact raftLaws_addCommit hL hle Hcmt

/-! ### A `ready` report's facts -/

/-- The vote, if any. -/
theorem raftFacts_optVote (γ : RaftNames) (G : AntSim.RaftFacts) (id t v : w64)
    (hL : AntSim.RaftLaws G) :
    raftFactsOwn (GF := GF) γ G ∗ □ (⌜v ≠ W64 0⌝ -∗ isVote γ id t v) ⊢
      ∃ G' : AntSim.RaftFacts, raftFactsOwn γ G' ∗
        ⌜AntSim.RaftLaws G' ∧ RaftFacts.Le G G' ∧ (v ≠ W64 0 → (id, t, v) ∈ G'.votes)⌝ := by
  iintro ⟨#HF, #Hv⟩
  by_cases hv : v ≠ W64 0
  · ihave #Hv' := Hv $$ %hv
    ihave ⟨HF', %H⟩ := raftFacts_addVote γ G (id, t, v) hL $$ [HF Hv']
    · iframe HF Hv'
    iexists RaftFacts.addVote G (id, t, v)
    iframe HF'
    ipureintro
    exact ⟨H.1, H.2, fun _ => List.mem_cons_self⟩
  · iexists G
    iframe HF
    ipureintro
    exact ⟨hL, RaftFacts.Le.refl G, fun h => absurd h hv⟩

/-- The leadership with its campaign log, if a leader. -/
theorem raftFacts_optLeader (γ : RaftNames) (G : AntSim.RaftFacts) (id t : w64) (L : List EntryM)
    (isL : Prop) [Decidable isL] (hL : AntSim.RaftLaws G) (hboot : γ.reBoot = [])
    (hLi : AntSim.LogIdx L) :
    raftFactsOwn (GF := GF) γ G ∗ raftCommitInv γ ∗ logRecs γ base0 L ∗
      □ (⌜isL⌝ -∗ isLeader γ id t ∗ ∃ F0 : List EntryM, isCamp γ id t F0 ∗ ⌜F0 <+: L⌝) ⊢
      |={↑(raftN γ)}=> ∃ G' : AntSim.RaftFacts, raftFactsOwn γ G' ∗
        ⌜AntSim.RaftLaws G' ∧ RaftFacts.Le G G' ∧
          (isL → (id, t) ∈ G'.leaders ∧ ∃ l0, (t, l0) ∈ G'.camps ∧ l0 <+: L)⌝ := by
  iintro ⟨#HF, #Hinv, #HrL, #Hld⟩
  by_cases hl : isL
  · ihave ⟨#Hl, %F0, #Hc, %Hp⟩ := Hld $$ %hl
    ihave #HrF0 := logRecs_take γ L F0.length $$ HrL
    rw [← List.prefix_iff_eq_take.1 Hp] at *
    ihave ⟨HF1, %H1⟩ := raftFacts_addLog γ G F0 hL (logIdx_prefix hLi Hp) $$ [HF HrF0]
    · iframe HF HrF0
    imod raftFacts_addLeader γ (RaftFacts.addLog G F0) id t F0 H1.1 List.mem_cons_self hboot
      $$ [HF1 Hinv Hl Hc] with ⟨HF2, %H2⟩
    · iframe HF1 Hinv Hl Hc
    imodintro
    iexists RaftFacts.addLeader (RaftFacts.addLog G F0) id t F0
    iframe HF2
    ipureintro
    exact ⟨H2.1, H1.2.trans H2.2, fun _ => ⟨List.mem_cons_self, F0, List.mem_cons_self, Hp⟩⟩
  · imodintro
    iexists G
    iframe HF
    ipureintro
    exact ⟨hL, RaftFacts.Le.refl G, fun h => absurd h hl⟩

/-- **What a `ready` report's facts are grown from** (persistent; `Cluster__drain.lean` reads them
from the node's laws after the `Ready`): the node's log certified and well formed, its commit within
it, the commit recorded in its term and committed, its leadership with its campaign log, its vote;
raft's commit invariant; the cluster without a bootstrap log, raft's namespace outside the harness's
invariant's. -/
def readySrc (γ : RaftNames) (id : w64) (ps : PState) : IProp GF :=
  iprop(raftCommitInv γ ∗ logRecs γ base0 ps.log ∗ commitIn γ ps.log ps.commit ps.term ∗
    isCommitted γ (ps.log.take (uint.nat ps.commit)) ∗
    □ (⌜ps.role = .leader⌝ -∗
      isLeader γ id ps.term ∗ ∃ F0 : List EntryM, isCamp γ id ps.term F0 ∗ ⌜F0 <+: ps.log⌝) ∗
    □ (⌜ps.vote ≠ W64 0⌝ -∗ isVote γ id ps.term ps.vote) ∗
    ⌜PlogWf base0 ps.log ∧ uint.Z ps.commit ≤ (ps.log.length : Int) ∧ γ.reBoot = []⌝)

instance readySrc_persistent (γ : RaftNames) (id : w64) (ps : PState) :
    Persistent (readySrc (GF := GF) γ id ps) := by
  unfold readySrc; infer_instance

/-- **A `ready` report's facts** (`factsExt` at `ReadyFacts`). -/
theorem readyExt (γ : AntNames) (id : w64) (ps : PState)
    (hns : (↑(raftN γ.raft.raftNames) : CoPset) ⊆ ⊤ \ ↑antN) :
    readySrc (GF := GF) γ.raft.raftNames id ps ⊢ factsExt γ (fun G => AntSim.ReadyFacts G id ps) := by
  iintro #Hs
  iunfold readySrc at Hs
  icases Hs with ⟨#Hinv, #HrL, #Hcm, #Hcd, #Hld, #Hv, %Hp⟩
  obtain ⟨hwf, hcle, hboot⟩ := Hp
  have hLi := logIdx_of_wf hwf
  have hc64 : ((uint.nat ps.commit : Nat) : Int) < 2 ^ 64 := by
    have := uint_Z_lt ps.commit; simp only [uint.nat]; omega
  have hcz : ((uint.nat ps.commit : Nat) : Int) = uint.Z ps.commit := by word
  have hcl : uint.nat ps.commit ≤ ps.log.length := by omega
  have hW : W64 ((uint.nat ps.commit : Nat) : Int) = ps.commit := by word
  iunfold factsExt
  iintro %G %hL #HF
  iapply fupd_mask_mono hns
  -- the log and its committed prefix certified
  ihave ⟨#HF1, %H1⟩ := raftFacts_addLog γ.raft.raftNames G ps.log hL hLi $$ [HF HrL]
  · iframe HF HrL
  ihave #HrC := logRecs_take γ.raft.raftNames ps.log (uint.nat ps.commit) $$ HrL
  ihave ⟨#HF2, %H2⟩ := raftFacts_addLog γ.raft.raftNames _ (ps.log.take (uint.nat ps.commit)) H1.1
    (logIdx_prefix hLi (List.take_prefix _ _)) $$ [HF1 HrC]
  · iframe HF1 HrC
  ihave ⟨%G3, #HF3, %H3⟩ := raftFacts_committed γ.raft.raftNames _ (ps.log.take (uint.nat ps.commit))
    H2.1 List.mem_cons_self $$ [HF2 Hcd]
  · iframe HF2 Hcd
  obtain ⟨hL3, hle3, hpre3⟩ := H3
  -- the commit recorded in its term
  imod raftFacts_addCommit γ.raft.raftNames G3 ps.log ps.term (uint.nat ps.commit) hL3 hboot hwf hcl
    hc64 hpre3 $$ [HF3 Hinv Hcm HrL] with ⟨#HF4, %H4⟩
  · iframe HF3 Hinv HrL
    rw [hW]; iexact Hcm
  -- the vote and the leadership
  ihave ⟨%G5, #HF5, %H5⟩ := raftFacts_optVote γ.raft.raftNames _ id ps.term ps.vote H4.1 $$ [HF4 Hv]
  · iframe HF4 Hv
  imod raftFacts_optLeader γ.raft.raftNames G5 id ps.term ps.log (ps.role = .leader) H5.1 hboot hLi
    $$ [HF5 Hinv HrL Hld] with ⟨%G7, #HF7, %H7⟩
  · iframe HF5 Hinv HrL Hld
  imodintro
  iexists G7
  iframe HF7
  ipureintro
  have hle : RaftFacts.Le G G7 :=
    H1.2.trans (H2.2.trans (hle3.trans (H4.2.trans (H5.2.1.trans H7.2.1))))
  have hle37 : RaftFacts.Le G3 G7 := H4.2.trans (H5.2.1.trans H7.2.1)
  have hpre7 : ps.log.take (uint.nat ps.commit) <+: G7.committed := hpre3.trans hle37.2.2.2.2.1
  have hlen : (ps.log.take (uint.nat ps.commit)).length = uint.nat ps.commit := by simp [hcl]
  have htake := List.prefix_iff_eq_take.1 hpre7
  rw [hlen] at htake
  refine ⟨H7.1, hle, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (H2.2.trans (hle3.trans hle37)).2.2.1 _ List.mem_cons_self
  · rw [← hlen]; exact hpre7.length_le
  · exact htake
  · exact H7.2.1.2.2.2.2.2 _ (H5.2.1.2.2.2.2.2 _ List.mem_cons_self)
  · intro hr; exact H7.2.2 hr
  · intro hv; exact H7.2.1.2.1 _ (H5.2.2 hv)

end proof

end AntHarness
end EtcdGrove
end Perennial
