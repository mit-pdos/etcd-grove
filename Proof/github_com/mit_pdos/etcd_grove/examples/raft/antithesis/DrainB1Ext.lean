/-
Lean-first (no Rocq counterpart). #33 parity B1, driver group E (`node.drain`): **raft's facts grown
by a drain's reports** (S4's `DrainExt`, over the parity vocabulary: `factsExt` two-argument,
`FactsLe` at the run's configuration with its boot clause). One fact at a time, each keeping
`RaftLaws` from raft's agreement lemmas between the new fact and those already in `raftFactsOwn`: a
certified log (`logRecs_agree`, `logMatch_of_recs`), a longer committed log (`isCommitted_agree`), a
vote (`isVote_agree`), a leader with its campaign log (`isLeader_unique`, `commitIn_camp_any`
against every recorded commit, `isCamp_ok`; `isCamp_boot`: past the boot term in a bootstrapped
run), a commit recorded in a term (`commitIn_camp_any` against every campaign).
- `commitIn_camp_any`: raft's `commitIn_camp` without its `reBoot = []` premise (the boot arm of
  `commitJ` through `isCamp_boot`: the campaign log extends the boot log);
- `readyExt_b1`: a `Ready`'s facts (`ReadyFacts`) from the node's `rawNode` laws and its durable
  ghost (the vote);
- `sendExt_b1`: a sent message's facts (`MsgFacts`) from its `isMessage`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1Loop
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessReport
public import Proof.go_etcd_io.raft.v3.Protocol.CommitCamp
public import Proof.go_etcd_io.raft.v3.RawNodeApi

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

theorem logIdx_lt {l : List EntryM} (h : AntSim.LogIdx l) {k : Nat} {e : EntryM}
    (hk : l[k]? = some e) : (k : Int) + 1 < 2 ^ 64 := by
  have := h k e hk
  have := uint_Z_lt e.Index'
  omega

/-- The term `plogTermAt` reads at the position `k + 1` of a positionally indexed log is its
`k`-th entry's. -/
theorem plogTermAt_base0_succ {l : List EntryM} (k : Nat) (hk : (k : Int) + 1 < 2 ^ 64) :
    plogTermAt base0 l (pidx base0 (k + 1)) = (fun e : EntryM => e.Term') <$> l[k]? := by
  have hz : uint.Z (pidx base0 (k + 1)) = (k : Int) + 1 := by
    unfold pidx; rw [base0_index]; push_cast
    rw [uint_Z_W64 _ (by omega) (by omega)]; omega
  unfold plogTermAt
  rw [base0_index, hz]
  simp only [show ¬ ((k : Int) + 1 < 0) by omega, show ¬ ((k : Int) + 1 = 0) by omega,
    ↓reduceIte]
  congr 2
  omega

/-- **Log matching from raft's records**: two logs at `base0` whose records agree (`RecsAgree`,
`logRecs_agree`), each indexed by its positions, agree up to any position where their terms do. -/
theorem logMatch_of_recs {l1 l2 : List EntryM} (h1 : AntSim.LogIdx l1) (h2 : AntSim.LogIdx l2)
    (hR : RecsAgree base0 l1 base0 l2) :
    ∀ (k : Nat) (e f : EntryM), l1[k]? = some e → l2[k]? = some f → e.Term' = f.Term' →
      l1.take (k + 1) = l2.take (k + 1) := by
  intro k
  induction k with
  | zero =>
    intro e f he hf ht
    have hlt := logIdx_lt h1 he
    have hi : e.Index' = f.Index' := by
      apply uint_Z_inj.mp; rw [h1 0 e he, h2 0 f hf]
    obtain ⟨hef, -⟩ := hR 0 0 e f he hf (by rw [base0_index]; omega)
      (by rw [base0_index]; omega) ht hi
    subst hef
    rw [List.take_add_one, List.take_add_one, he, hf]
    simp
  | succ k ih =>
    intro e f he hf ht
    have hlt := logIdx_lt h1 he
    have hi : e.Index' = f.Index' := by
      apply uint_Z_inj.mp; rw [h1 _ e he, h2 _ f hf]
    obtain ⟨hef, hpt⟩ := hR (k + 1) (k + 1) e f he hf (by rw [base0_index]; push_cast; omega)
      (by rw [base0_index]; push_cast; omega) ht hi
    subst hef
    have hk1 : k < l1.length := by
      have := (List.getElem?_eq_some_iff.1 he).1; omega
    have hk2 : k < l2.length := by
      have := (List.getElem?_eq_some_iff.1 hf).1; omega
    obtain ⟨e', he'⟩ : ∃ e', l1[k]? = some e' := ⟨_, List.getElem?_eq_getElem hk1⟩
    obtain ⟨f', hf'⟩ : ∃ f', l2[k]? = some f' := ⟨_, List.getElem?_eq_getElem hk2⟩
    rw [plogTermAt_base0_succ k (by omega), plogTermAt_base0_succ k (by omega), he', hf'] at hpt
    simp only [Option.map_eq_map, Option.map_some, Option.some.injEq] at hpt
    have ih' := ih e' f' he' hf' hpt
    rw [List.take_add_one, List.take_add_one (l := l2), ih', he, hf]

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

/-- An append's entries, a prefix of the leader's suffix from `index + 1`, are the full log's slice
from `index`. -/
theorem app_slice {bL : entryID} {fp l es : List EntryM} {i t : w64} (hfull : FullOk bL fp)
    (hterm : plogTermAt bL l i = some t) (hi : uint.Z i + 1 < 2 ^ 64)
    (hes : es <+: plogFrom bL l (i + W64 1)) :
    ((fp ++ l).drop (uint.nat i)).take es.length = es := by
  have hge : uint.Z bL.index' ≤ uint.Z i := by
    unfold plogTermAt at hterm
    split at hterm
    · cases hterm
    · omega
  have hlen := hfull.1
  have hi1 : uint.Z (i + W64 1) = uint.Z i + 1 := by word
  unfold plogFrom at hes
  rw [hi1] at hes
  have hz : ((uint.nat i : Nat) : Int) = uint.Z i := by word
  have hk : (uint.Z i + 1 - uint.Z bL.index' - 1).toNat = uint.nat i - fp.length := by omega
  rw [hk] at hes
  have hd : (fp ++ l).drop (uint.nat i) = l.drop (uint.nat i - fp.length) := by
    have hle : fp.length ≤ uint.nat i := by omega
    rw [List.drop_append, List.drop_eq_nil_of_le hle, List.nil_append]
  rw [hd]
  exact (List.prefix_iff_eq_take.1 hes).symm

theorem w64_nat_cast {n : Nat} (h : (n : Int) < 2 ^ 64) : uint.nat (W64 (n : Int)) = n := by
  word

/-! ### `FactsLe`, composed -/

theorem FactsLe.trans {R : AntSim.RunCfg} {G1 G2 G3 : AntSim.RaftFacts} (h1 : FactsLe R G1 G2)
    (h2 : FactsLe R G2 G3) : FactsLe R G1 G3 := by
  obtain ⟨a1, b1, c1, d1, e1, f1, g1⟩ := h1
  obtain ⟨a2, b2, c2, d2, e2, f2, g2⟩ := h2
  refine ⟨fun x h => a2 x (a1 x h), ?_, fun x h => c2 x (c1 x h), fun x h => d2 x (d1 x h),
    fun x h => e2 x (e1 x h), f1.trans f2, fun x h => g2 x (g1 x h)⟩
  intro x hx hn hb
  by_cases h : x ∈ G2.leaders
  · exact b1 x h hn hb
  · exact b2 x hx h hb

/-- Facts whose leaders are unchanged and whose other lists grow. -/
theorem factsLe_of {R : AntSim.RunCfg} {G G' : AntSim.RaftFacts} (hl : G'.leaders = G.leaders)
    (hv : ∀ x ∈ G.votes, x ∈ G'.votes) (hg : ∀ x ∈ G.logs, x ∈ G'.logs)
    (hc : ∀ x ∈ G.camps, x ∈ G'.camps) (hp : G.committed <+: G'.committed)
    (hm : ∀ x ∈ G.commits, x ∈ G'.commits) : FactsLe R G G' :=
  ⟨fun x h => hl ▸ h, fun x h hn _ => absurd (hl ▸ h) hn, hv, hg, hc, hp, hm⟩

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

theorem raftLaws_addLog (R : AntSim.RunCfg) {G : AntSim.RaftFacts} {l : List EntryM}
    (hL : AntSim.RaftLaws G) (hl : AntSim.LogIdx l) (hself : RecsAgree base0 l base0 l)
    (hag : ∀ b ∈ G.logs, RecsAgree base0 l base0 b ∧ RecsAgree base0 b base0 l ∧ AntSim.LogIdx b) :
    AntSim.RaftLaws (RaftFacts.addLog G l) ∧ FactsLe R G (RaftFacts.addLog G l) := by
  obtain ⟨hld, hvt, hm, hcm, hcamp, hcmts, hct⟩ := hL
  refine ⟨⟨hld, hvt, ?_, List.mem_cons_of_mem _ hcm, fun p hp => List.mem_cons_of_mem _ (hcamp p hp),
    hcmts, hct⟩, factsLe_of rfl (fun _ h => h) (fun _ h => List.mem_cons_of_mem _ h) (fun _ h => h)
    (List.prefix_refl _) (fun _ h => h)⟩
  intro a ha b hb
  simp only [RaftFacts.addLog, List.mem_cons] at ha hb
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · exact logMatch_of_recs hl hl hself
  · exact logMatch_of_recs hl (hag b hb).2.2 (hag b hb).1
  · exact logMatch_of_recs (hag a ha).2.2 hl (hag a ha).2.1
  · exact hm a ha b hb

theorem raftLaws_addVote (R : AntSim.RunCfg) {G : AntSim.RaftFacts} {v : w64 × w64 × w64}
    (hL : AntSim.RaftLaws G) (hag : ∀ b ∈ G.votes, b.1 = v.1 → b.2.1 = v.2.1 → b.2.2 = v.2.2) :
    AntSim.RaftLaws (RaftFacts.addVote G v) ∧ FactsLe R G (RaftFacts.addVote G v) := by
  obtain ⟨hld, hvt, hm, hcm, hcamp, hcmts, hct⟩ := hL
  refine ⟨⟨hld, ?_, hm, hcm, hcamp, hcmts, hct⟩, factsLe_of rfl
    (fun _ h => List.mem_cons_of_mem _ h) (fun _ h => h) (fun _ h => h) (List.prefix_refl _)
    (fun _ h => h)⟩
  intro a ha b hb h1 h2
  simp only [RaftFacts.addVote, List.mem_cons] at ha hb
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · rfl
  · exact (hag b hb h1.symm h2.symm).symm
  · exact hag a ha h1 h2
  · exact hvt a ha b hb h1 h2

theorem raftLaws_setCommitted (R : AntSim.RunCfg) {G : AntSim.RaftFacts} {L : List EntryM}
    (hL : AntSim.RaftLaws G) (hp : G.committed <+: L) (hLm : L ∈ G.logs) :
    AntSim.RaftLaws (RaftFacts.setCommitted G L) ∧ FactsLe R G (RaftFacts.setCommitted G L) := by
  obtain ⟨hld, hvt, hm, hcm, hcamp, hcmts, hct⟩ := hL
  refine ⟨⟨hld, hvt, hm, hLm, hcamp, ?_, hct⟩, factsLe_of rfl (fun _ h => h) (fun _ h => h)
    (fun _ h => h) hp (fun _ h => h)⟩
  intro x hx
  obtain ⟨hle, hc⟩ := hcmts x hx
  refine ⟨Nat.le_trans hle hp.length_le, fun p hpc hlt => ?_⟩
  simp only [RaftFacts.setCommitted]
  rw [take_of_prefix hp hle]
  exact hc p hpc hlt

theorem raftLaws_addLeader (R : AntSim.RunCfg) {G : AntSim.RaftFacts} {id T : w64}
    {F0 : List EntryM} (hL : AntSim.RaftLaws G) (hF0 : F0 ∈ G.logs)
    (hok : ∀ e ∈ F0, uint.Z e.Term' < uint.Z T) (hT : R.boot = true → 2 ≤ uint.Z T)
    (hld' : ∀ b ∈ G.leaders, b.2 = T → b.1 = id)
    (hcmt : ∀ x ∈ G.commits, uint.Z x.1 < uint.Z T → G.committed.take x.2 <+: F0) :
    AntSim.RaftLaws (RaftFacts.addLeader G id T F0) ∧
      FactsLe R G (RaftFacts.addLeader G id T F0) := by
  obtain ⟨hld, hvt, hm, hcm, hcamp, hcmts, hct⟩ := hL
  refine ⟨⟨?_, hvt, hm, hcm, ?_, ?_, ?_⟩, ⟨fun _ h => List.mem_cons_of_mem _ h, ?_, fun _ h => h,
    fun _ h => h, fun _ h => List.mem_cons_of_mem _ h, List.prefix_refl _, fun _ h => h⟩⟩
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
  · intro x hx hn hb
    simp only [RaftFacts.addLeader, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hT hb
    · exact absurd hx hn

theorem raftLaws_addCommit (R : AntSim.RunCfg) {G : AntSim.RaftFacts} {x : w64 × Nat}
    (hL : AntSim.RaftLaws G) (hle : x.2 ≤ G.committed.length)
    (hcmt : ∀ p ∈ G.camps, uint.Z x.1 < uint.Z p.1 → G.committed.take x.2 <+: p.2) :
    AntSim.RaftLaws (RaftFacts.addCommit G x) ∧ FactsLe R G (RaftFacts.addCommit G x) := by
  obtain ⟨hld, hvt, hm, hcm, hcamp, hcmts, hct⟩ := hL
  refine ⟨⟨hld, hvt, hm, hcm, hcamp, ?_, hct⟩, factsLe_of rfl (fun _ h => h) (fun _ h => h)
    (fun _ h => h) (List.prefix_refl _) (fun _ h => List.mem_cons_of_mem _ h)⟩
  intro y hy
  simp only [RaftFacts.addCommit, List.mem_cons] at hy
  rcases hy with rfl | hy
  · exact ⟨hle, hcmt⟩
  · exact hcmts y hy

end pure

/-! ## Raft: leader completeness at any boot log -/

section raft
variable [GooseExts]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- **`commitIn_camp` at any boot log**: raft's `commitIn_camp` (`Protocol/CommitCamp.lean`) drops
its `γ.reBoot = []` premise. `commitJ`'s boot arm (`c` within the boot log, `F`'s term at `c` the
boot log's): the campaign log extends the boot log (`isCamp_boot`), so its term at `c` is the boot
log's too, and `F`, `F0` agree below `c` by their records (`full_take_eq`). The quorum arm is
`commitIn_camp`'s proof. -/
theorem commitIn_camp_any (γ : RaftNames) (F : List EntryM) (c tm : w64) (j T : w64)
    (F0 G : List EntryM) :
    uint.Z tm < uint.Z T → PlogWf base0 F → F0 <+: G →
    ⊢ raftCommitInv (GF := GF) γ -∗
      commitIn γ F c tm -∗ logRecs γ base0 F -∗ isLeader γ j T -∗ isCamp γ j T F0 -∗
      logRecs γ base0 G ={↑(raftN γ)}=∗ ⌜F.take (uint.nat c) <+: F0⌝ := by
  intro HT HwF Hpre
  iintro #Hinv #Hcm #HrF #Hl #Hc #HrG
  ihave #Hcj := commitIn_j γ F c tm $$ Hcm
  icases isCamp_ok γ j T F0 $$ Hc with %Hcok
  have HwF0 : PlogWf base0 F0 := Hcok.1
  have HF0 : G.take F0.length = F0 := by
    rw [take_of_prefix Hpre (Nat.le_refl _)]; exact List.take_length
  ihave #HrF0 := logRecs_take γ G F0.length $$ HrG
  rw [HF0]
  unfold commitJ
  icases Hcj with (%H0 | ⟨%t, %n, %Gq, #Hq, %Hcn⟩)
  · -- the boot arm: the campaign log extends the boot log
    icases isCamp_boot γ j T F0 $$ Hc with %Hb
    have Hs : (plogTermAt base0 γ.reBoot c).isSome := by
      apply plogTermAt_in_range
      unfold plogLastIndexZ
      rw [base0_index]
      have := uint_Z_nonneg c
      omega
    have HF0c : plogTermAt base0 F0 c = plogTermAt base0 γ.reBoot c :=
      plogTermAt_prefix _ _ _ _ Hb.1 Hs
    icases full_take_eq γ F F0 c HwF HwF0 (by rw [← H0.2]; exact Hs) (by rw [← H0.2, HF0c])
      $$ HrF HrF0 with %Htk
    imodintro; ipureintro
    show F.take (uint.Z c).toNat <+: F0
    rw [Htk]; exact List.take_prefix _ _
  obtain ⟨Hcn, Htm, HcF⟩ := Hcn
  -- the vote table, from the commit invariant
  have HE : (↑(raftLogN γ) : CoPset) ⊆ ↑(raftN γ) := raftLogN_of (fun _ h => h)
  ihave #Hli := raftCommitInv_log γ $$ Hinv
  unfold raftLogInv raftLogInvBody
  iinv Hli with ⟨%P, HP, Hjust, >Htbl, Hwt, Hpo⟩ Hclose
  -- `lc_core` at the campaign log: `Gq`'s term at `n` is in `F0`
  icases lc_core γ ((uint.Z T).toNat + 1) T t n Gq j F0 F0
      (by have := uint_Z_nonneg T; omega) (by omega) HwF0 (camp_last T F0 Hcok)
      $$ Htbl Hq Hl Hc HrF0 with %HF0n
  icases cq_full γ t n Gq $$ Hq with ⟨%HwGq, #HrGq⟩
  icases cq_base γ t n Gq $$ Hq with ⟨%HGqn, -⟩
  icases full_match γ Gq F0 n HwGq HwF0 (by rw [HGqn]; rfl) (by rw [HGqn, HF0n]) $$ HrGq HrF0
    with %Hm
  have HsGq := full_term_at_some Gq c n (by rw [HGqn]; rfl) Hcn
  icases full_take_eq γ F F0 c HwF HwF0 (by rw [← HcF]; exact HsGq) (by rw [← HcF]; exact Hm c Hcn)
    $$ HrF HrF0 with %Htk
  imod Hclose $$ [HP Hjust Htbl Hwt Hpo] with -
  · inext
    iexists P
    iframe
  imodintro; ipureintro
  show F.take (uint.Z c).toNat <+: F0
  rw [Htk]; exact List.take_prefix _ _

end raft

/-! ## The facts' ghost side -/

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

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

/-- The same, the fact under an update (`commitIn_camp_any`). -/
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

/-- **A recorded commit against a campaign of a later term** (`commitIn_camp_any`): the committed
log's prefix at the commit is within the campaign log. -/
theorem commit_camp_pair (γ : RaftNames) (C : List EntryM) (x : w64 × Nat) (id T : w64)
    (F0 : List EntryM) :
    iprop(raftCommitInv (GF := GF) γ ∗ isLeader γ id T ∗ isCamp γ id T F0 ∗ logRecs γ base0 F0) ∗
      iprop(∃ F : List EntryM, commitIn γ F (W64 (x.2 : Int)) x.1 ∗ logRecs γ base0 F ∗
        ⌜PlogWf base0 F ∧ x.2 ≤ F.length ∧ (x.2 : Int) < 2 ^ 64 ∧ F.take x.2 <+: C⌝) ⊢
      |={↑(raftN γ)}=> ⌜uint.Z x.1 < uint.Z T → C.take x.2 <+: F0⌝ := by
  by_cases hlt : uint.Z x.1 < uint.Z T
  · iintro ⟨⟨#Hinv, #Hl, #Hc, #HrF0⟩, ⟨%F, #Hcm, #HrF, %Hp⟩⟩
    obtain ⟨hwf, hle, hlt64, hpre⟩ := Hp
    imod commitIn_camp_any γ F (W64 (x.2 : Int)) x.1 id T F0 F0 hlt hwf (List.prefix_refl _)
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

theorem raftFacts_addLog (R : AntSim.RunCfg) (γ : RaftNames) (G : AntSim.RaftFacts)
    (l : List EntryM) (hL : AntSim.RaftLaws G) (hl : AntSim.LogIdx l) :
    raftFactsOwn (GF := GF) γ G ∗ logRecs γ base0 l ⊢
      raftFactsOwn γ (RaftFacts.addLog G l) ∗
        ⌜AntSim.RaftLaws (RaftFacts.addLog G l) ∧ FactsLe R G (RaftFacts.addLog G l)⌝ := by
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
  · ipureintro; exact raftLaws_addLog R hL hl Hself Hag

theorem raftFacts_addVote (R : AntSim.RunCfg) (γ : RaftNames) (G : AntSim.RaftFacts)
    (v : w64 × w64 × w64) (hL : AntSim.RaftLaws G) :
    raftFactsOwn (GF := GF) γ G ∗ isVote γ v.1 v.2.1 v.2.2 ⊢
      raftFactsOwn γ (RaftFacts.addVote G v) ∗
        ⌜AntSim.RaftLaws (RaftFacts.addVote G v) ∧ FactsLe R G (RaftFacts.addVote G v)⌝ := by
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
  · ipureintro; exact raftLaws_addVote R hL Hag

/-- A longer committed log (or the same facts, when it is not longer). -/
theorem raftFacts_committed (R : AntSim.RunCfg) (γ : RaftNames) (G : AntSim.RaftFacts)
    (L : List EntryM) (hL : AntSim.RaftLaws G) (hLm : L ∈ G.logs) :
    raftFactsOwn (GF := GF) γ G ∗ isCommitted γ L ⊢
      ∃ G' : AntSim.RaftFacts, raftFactsOwn γ G' ∗
        ⌜AntSim.RaftLaws G' ∧ FactsLe R G G' ∧ L <+: G'.committed⌝ := by
  iintro ⟨#HF, #HL⟩
  iunfold raftFactsOwn at HF
  icases HF with ⟨#Hld, #Hvt, #Hlogs, #Hcamps, #Hcm, #Hcmts⟩
  ihave %Hag := isCommitted_agree γ L G.committed $$ HL Hcm
  rcases Hag with hp | hp
  · iexists G
    iunfold raftFactsOwn
    iframe Hld Hvt Hlogs Hcamps Hcm Hcmts
    ipureintro; exact ⟨hL, FactsLe.refl R G, hp⟩
  · iexists RaftFacts.setCommitted G L
    iunfold raftFactsOwn
    simp only [RaftFacts.setCommitted]
    iframe Hld Hvt Hlogs Hcamps HL
    isplitl
    · iapply commits_mono γ G.commits G.committed L hp $$ Hcmts
    · ipureintro
      obtain ⟨h1, h2⟩ := raftLaws_setCommitted R hL hp hLm
      exact ⟨h1, h2, List.prefix_refl _⟩

theorem raftFacts_addLeader (R : AntSim.RunCfg) (γ : RaftNames) (G : AntSim.RaftFacts)
    (id T : w64) (F0 : List EntryM) (hL : AntSim.RaftLaws G) (hF0 : F0 ∈ G.logs)
    (hboot : γ.reBoot = AntSim.bootLog R) :
    raftFactsOwn (GF := GF) γ G ∗ raftCommitInv γ ∗ isLeader γ id T ∗ isCamp γ id T F0 ⊢
      |={↑(raftN γ)}=> raftFactsOwn γ (RaftFacts.addLeader G id T F0) ∗
        ⌜AntSim.RaftLaws (RaftFacts.addLeader G id T F0) ∧
          FactsLe R G (RaftFacts.addLeader G id T F0)⌝ := by
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
  ihave %Hb := isCamp_boot γ id T F0 $$ Hc
  have hT : R.boot = true → 2 ≤ uint.Z T := by
    intro hb
    apply Hb.2
    rw [hboot]; simp [AntSim.bootLog, hb]
  have key := bigSepL_pure_all_upd (GF := GF)
      (P := iprop(raftCommitInv γ ∗ isLeader γ id T ∗ isCamp γ id T F0 ∗ logRecs γ base0 F0))
      (Φ := fun (x : w64 × Nat) => iprop(∃ F : List EntryM, commitIn γ F (W64 (x.2 : Int)) x.1 ∗
        logRecs γ base0 F ∗
        ⌜PlogWf base0 F ∧ x.2 ≤ F.length ∧ (x.2 : Int) < 2 ^ 64 ∧ F.take x.2 <+: G.committed⌝))
      ↑(raftN γ) G.commits (fun (x : w64 × Nat) => uint.Z x.1 < uint.Z T → G.committed.take x.2 <+: F0)
      (fun x _ => commit_camp_pair (GF := GF) γ G.committed x id T F0)
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
    exact raftLaws_addLeader R hL hF0 (campTerms_of_ok Hok) hT Hld' (fun x hx h => Hcmt x hx h)

/-- **A recorded commit** `(t, c)` at the log `L`, against every campaign of a later term. -/
theorem raftFacts_addCommit (R : AntSim.RunCfg) (γ : RaftNames) (G : AntSim.RaftFacts)
    (L : List EntryM) (t : w64) (c : Nat) (hL : AntSim.RaftLaws G) (hwf : PlogWf base0 L)
    (hc : c ≤ L.length) (hc64 : (c : Int) < 2 ^ 64) (hpre : L.take c <+: G.committed) :
    raftFactsOwn (GF := GF) γ G ∗ raftCommitInv γ ∗ commitIn γ L (W64 (c : Int)) t ∗
        logRecs γ base0 L ⊢
      |={↑(raftN γ)}=> raftFactsOwn γ (RaftFacts.addCommit G (t, c)) ∗
        ⌜AntSim.RaftLaws (RaftFacts.addCommit G (t, c)) ∧
          FactsLe R G (RaftFacts.addCommit G (t, c))⌝ := by
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
        iapply commit_camp_pair γ G.committed (t, c) cc p.1 p.2 $$ [Hinv Hl Hc Hr Hcm' HrL]
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
    exact raftLaws_addCommit R hL hle Hcmt

/-! ### A `ready` report's facts -/

/-- The vote, if any. -/
theorem raftFacts_optVote (R : AntSim.RunCfg) (γ : RaftNames) (G : AntSim.RaftFacts)
    (id t v : w64) (hL : AntSim.RaftLaws G) :
    raftFactsOwn (GF := GF) γ G ∗ □ (⌜v ≠ W64 0⌝ -∗ isVote γ id t v) ⊢
      ∃ G' : AntSim.RaftFacts, raftFactsOwn γ G' ∗
        ⌜AntSim.RaftLaws G' ∧ FactsLe R G G' ∧ (v ≠ W64 0 → (id, t, v) ∈ G'.votes)⌝ := by
  iintro ⟨#HF, #Hv⟩
  by_cases hv : v ≠ W64 0
  · ihave #Hv' := Hv $$ %hv
    ihave ⟨HF', %H⟩ := raftFacts_addVote R γ G (id, t, v) hL $$ [HF Hv']
    · iframe HF Hv'
    iexists RaftFacts.addVote G (id, t, v)
    iframe HF'
    ipureintro
    exact ⟨H.1, H.2, fun _ => List.mem_cons_self⟩
  · iexists G
    iframe HF
    ipureintro
    exact ⟨hL, FactsLe.refl R G, fun h => absurd h hv⟩

/-- The leadership with its campaign log, if a leader. -/
theorem raftFacts_optLeader (R : AntSim.RunCfg) (γ : RaftNames) (G : AntSim.RaftFacts) (id t : w64)
    (L : List EntryM) (isL : Prop) [Decidable isL] (hL : AntSim.RaftLaws G)
    (hboot : γ.reBoot = AntSim.bootLog R) (hLi : AntSim.LogIdx L) :
    raftFactsOwn (GF := GF) γ G ∗ raftCommitInv γ ∗ logRecs γ base0 L ∗
      □ (⌜isL⌝ -∗ isLeader γ id t ∗ ∃ F0 : List EntryM, isCamp γ id t F0 ∗ ⌜F0 <+: L⌝) ⊢
      |={↑(raftN γ)}=> ∃ G' : AntSim.RaftFacts, raftFactsOwn γ G' ∗
        ⌜AntSim.RaftLaws G' ∧ FactsLe R G G' ∧
          (isL → (id, t) ∈ G'.leaders ∧ ∃ l0, (t, l0) ∈ G'.camps ∧ l0 <+: L)⌝ := by
  iintro ⟨#HF, #Hinv, #HrL, #Hld⟩
  by_cases hl : isL
  · ihave ⟨#Hl, %F0, #Hc, %Hp⟩ := Hld $$ %hl
    ihave #HrF0 := logRecs_take γ L F0.length $$ HrL
    rw [← List.prefix_iff_eq_take.1 Hp] at *
    ihave ⟨HF1, %H1⟩ := raftFacts_addLog R γ G F0 hL (logIdx_prefix hLi Hp) $$ [HF HrF0]
    · iframe HF HrF0
    imod raftFacts_addLeader R γ (RaftFacts.addLog G F0) id t F0 H1.1 List.mem_cons_self hboot
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
    exact ⟨hL, FactsLe.refl R G, fun h => absurd h hl⟩

/-- **What a `ready` report's facts are grown from** (persistent; read from the node's laws after
the `Ready`, `readyExt_b1`): raft's commit invariant, the node's log certified and well formed, its
commit within it, the commit recorded in its term and committed, its leadership with its campaign
log, its vote; the cluster's boot log the run's. -/
def readySrcB1 (R : AntSim.RunCfg) (γ : RaftNames) (id : w64) (ps : PState) (vt : w64) :
    IProp GF :=
  iprop(raftCommitInv γ ∗ logRecs γ base0 ps.log ∗ commitIn γ ps.log ps.commit ps.term ∗
    isCommitted γ (ps.log.take (uint.nat ps.commit)) ∗
    □ (⌜ps.role = .leader⌝ -∗
      isLeader γ id ps.term ∗ ∃ F0 : List EntryM, isCamp γ id ps.term F0 ∗ ⌜F0 <+: ps.log⌝) ∗
    □ (⌜vt ≠ W64 0⌝ -∗ isVote γ id ps.term vt) ∗
    ⌜PlogWf base0 ps.log ∧ uint.Z ps.commit ≤ (ps.log.length : Int) ∧
      γ.reBoot = AntSim.bootLog R⌝)

instance readySrcB1_persistent (R : AntSim.RunCfg) (γ : RaftNames) (id : w64) (ps : PState)
    (vt : w64) : Persistent (readySrcB1 (GF := GF) R γ id ps vt) := by
  unfold readySrcB1; infer_instance

/-- **A `ready` report's facts, from their sources** (`factsExt` at `ReadyFacts`, `FactsLe`). -/
theorem readyExt_src (γ : AntNames) (id : w64) (r : RState) (hfp : r.fp = [])
    (hns : (↑(raftN γ.raft.raftNames) : CoPset) ⊆ ⊤ \ ↑antN) :
    readySrcB1 (GF := GF) γ.R γ.raft.raftNames id r.p r.p.vote ⊢
      factsExt γ (fun G0 G => FactsLe γ.R G0 G ∧ AntSim.RaftLaws G ∧ AntSim.ReadyFacts G id r) := by
  have hfull : r.full = r.p.log := by simp [RState.full, hfp]
  iintro #Hs
  iunfold readySrcB1 at Hs
  icases Hs with ⟨#Hinv, #HrL, #Hcm, #Hcd, #Hld, #Hv, %Hp⟩
  obtain ⟨hwf, hcle, hboot⟩ := Hp
  have hLi := logIdx_of_wf hwf
  have hc64 : ((uint.nat r.p.commit : Nat) : Int) < 2 ^ 64 := by
    have := uint_Z_lt r.p.commit; simp only [uint.nat]; omega
  have hcl : uint.nat r.p.commit ≤ r.p.log.length := by
    have : ((uint.nat r.p.commit : Nat) : Int) = uint.Z r.p.commit := by word
    omega
  have hW : W64 ((uint.nat r.p.commit : Nat) : Int) = r.p.commit := by word
  iunfold factsExt
  iintro %G %hL #HF
  iapply fupd_mask_mono hns
  -- the log and its committed prefix certified
  ihave ⟨#HF1, %H1⟩ := raftFacts_addLog γ.R γ.raft.raftNames G r.p.log hL hLi $$ [HF HrL]
  · iframe HF HrL
  ihave #HrC := logRecs_take γ.raft.raftNames r.p.log (uint.nat r.p.commit) $$ HrL
  ihave ⟨#HF2, %H2⟩ := raftFacts_addLog γ.R γ.raft.raftNames _
    (r.p.log.take (uint.nat r.p.commit)) H1.1 (logIdx_prefix hLi (List.take_prefix _ _))
    $$ [HF1 HrC]
  · iframe HF1 HrC
  ihave ⟨%G3, #HF3, %H3⟩ := raftFacts_committed γ.R γ.raft.raftNames _
    (r.p.log.take (uint.nat r.p.commit)) H2.1 List.mem_cons_self $$ [HF2 Hcd]
  · iframe HF2 Hcd
  obtain ⟨hL3, hle3, hpre3⟩ := H3
  -- the commit recorded in its term
  imod raftFacts_addCommit γ.R γ.raft.raftNames G3 r.p.log r.p.term (uint.nat r.p.commit) hL3 hwf
    hcl hc64 hpre3 $$ [HF3 Hinv Hcm HrL] with ⟨#HF4, %H4⟩
  · iframe HF3 Hinv HrL
    rw [hW]; iexact Hcm
  -- the vote and the leadership
  ihave ⟨%G5, #HF5, %H5⟩ := raftFacts_optVote γ.R γ.raft.raftNames _ id r.p.term r.p.vote H4.1
    $$ [HF4 Hv]
  · iframe HF4 Hv
  imod raftFacts_optLeader γ.R γ.raft.raftNames G5 id r.p.term r.p.log (r.p.role = .leader) H5.1
    hboot hLi $$ [HF5 Hinv HrL Hld] with ⟨%G7, #HF7, %H7⟩
  · iframe HF5 Hinv HrL Hld
  imodintro
  iexists G7
  iframe HF7
  ipureintro
  have hle : FactsLe γ.R G G7 :=
    H1.2.trans (H2.2.trans (hle3.trans (H4.2.trans (H5.2.1.trans H7.2.1))))
  have hle37 : FactsLe γ.R G3 G7 := H4.2.trans (H5.2.1.trans H7.2.1)
  have hpre7 : r.p.log.take (uint.nat r.p.commit) <+: G7.committed := hpre3.trans hle37.2.2.2.2.2.1
  have hlen : (r.p.log.take (uint.nat r.p.commit)).length = uint.nat r.p.commit := by simp [hcl]
  have htake := List.prefix_iff_eq_take.1 hpre7
  rw [hlen] at htake
  refine ⟨hle, H7.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfull]; exact (H2.2.trans (hle3.trans hle37)).2.2.2.1 _ List.mem_cons_self
  · rw [← hlen]; exact hpre7.length_le
  · rw [hfull]; exact htake
  · exact H7.2.1.2.2.2.2.2.2 _ (H5.2.1.2.2.2.2.2.2 _ List.mem_cons_self)
  · intro hr; rw [hfull]; exact H7.2.2 hr
  · intro hv; exact H7.2.1.2.2.1 _ (H5.2.2 hv)

/-- **A `Ready`'s facts** (`factsExt` at `ReadyFacts`, `FactsLe`), at the state `r` the `Ready` is
taken at (no ghost prefix), read from the node's `rawNode` laws and its durable ghost at a state
`S` of `r`'s term and vote (the drain's: the `Ready`'s `readyDurable`): the log certified and well
formed, the commit invariant, the commit recorded and committed, the leadership with its campaign
log; the vote from `S` (`rawNode_vote`, under an update). The cluster's boot log the run's and
raft's namespace outside the harness's invariant's (`nodeRaft`'s pure facts). -/
theorem readyExt_b1 (h_wf : rawNode_wf.law (GF := GF) (hG := hG))
    (h_recs : rawNode_logRecs.law (GF := GF) (hG := hG))
    (h_ld : rawNode_leader.law (GF := GF) (hG := hG))
    (h_vote : rawNode_vote.law (GF := GF) (hG := hG))
    (h_cm : rawNode_commit.law (GF := GF) (hG := hG))
    (h_cmd : rawNode_committed.law (GF := GF) (hG := hG))
    (h_inv : rawNode_commitInv.law (GF := GF) (hG := hG))
    (γ : AntNames) (j : Fin γ.R.N) (md : RnMode) (hsn : md.snapshots = false)
    (hcc : md.confChanges = false) (hfw : md.forwarding = false) (has : md.async = false)
    (rn : Loc) (rs : RNState) (r : RState) (qs : List Msg) (ip : Nat) (S : RaftState)
    (hfp : r.fp = []) (hS : S.term = r.p.term ∧ S.vote = r.p.vote)
    (hboot : γ.raft.raftNames.reBoot = AntSim.bootLog γ.R)
    (hns : (↑(raftN γ.raft.raftNames) : CoPset) ⊆ ⊤ \ ↑antN) :
    rawNode (GF := GF) γ.raft.raftNames md rn (AntSim.nodeId j) rs r qs ip ∗
        ownDurGhost γ.raft.raftNames (AntSim.nodeId j) S ⊢
      |={⊤}=> □ factsExt γ (fun G0 G => FactsLe γ.R G0 G ∧ AntSim.RaftLaws G ∧
          AntSim.ReadyFacts G (AntSim.nodeId j) r) ∗
        rawNode γ.raft.raftNames md rn (AntSim.nodeId j) rs r qs ip ∗
        ownDurGhost γ.raft.raftNames (AntSim.nodeId j) S := by
  iintro ⟨Hrn, HD⟩
  iapply fupd_mask_mono (E1 := ↑(raftN γ.raft.raftNames)) CoPset.subseteq_top
  ihave ⟨%Hwf, Hrn⟩ := h_wf md hsn hcc hfw has _ rn _ rs r qs ip $$ Hrn
  ihave ⟨#HrL, Hrn⟩ := h_recs md hsn hcc hfw has _ rn _ rs r qs ip $$ Hrn
  ihave ⟨#Hld, Hrn⟩ := h_ld md hsn hcc hfw has _ rn _ rs r qs ip $$ Hrn
  ihave ⟨#Hcm, Hrn⟩ := h_cm md hsn hcc hfw has _ rn _ rs r qs ip $$ Hrn
  ihave ⟨#Hinv, Hrn⟩ := h_inv md hsn hcc hfw has _ rn _ rs r qs ip $$ Hrn
  imod h_cmd md hsn hcc hfw has _ rn _ rs r qs ip $$ Hrn with ⟨#Hcd, Hrn⟩
  imod h_vote _ _ S $$ HD with ⟨#Hv, HD⟩
  obtain ⟨hwf, hcle, -⟩ := Hwf
  have hcle' : uint.Z r.p.commit ≤ (r.p.log.length : Int) := by
    unfold plogLastIndexZ at hcle; rw [base0_index] at hcle; omega
  ihave #Hs : readySrcB1 (GF := GF) γ.R γ.raft.raftNames (AntSim.nodeId j) r.p r.p.vote $$ []
  · iunfold readySrcB1
    iframe Hinv HrL Hcm Hcd Hld
    isplitl
    · imodintro
      rw [← hS.1, ← hS.2]
      iexact Hv
    · ipureintro; exact ⟨hwf, hcle', hboot⟩
  imodintro
  iframe Hrn HD
  imodintro
  iapply readyExt_src γ (AntSim.nodeId j) r hfp hns $$ Hs

/-! ### A `send` report's facts -/

/-- An append's full log, certified, with the append's entries its slice. -/
theorem isMessage_app_log (γ : RaftNames) (q : Msg) (hty : q.ty = .app) :
    isMessage (GF := GF) γ q ⊢ ∃ L : List EntryM, logRecs γ base0 L ∗
      ⌜AntSim.LogIdx L ∧ (L.drop (uint.nat q.index)).take q.entries.length = q.entries⌝ := by
  unfold isMessage
  rw [hty]
  iintro ⟨%Hpay, #Hl, ⟨%bL, %l, %fp, #Hlp, %Hpl, #Hfull, -⟩, -⟩
  iunfold leadPrefix at Hlp
  icases Hlp with ⟨-, %γt, %l0, -, -, #Hrl, -⟩
  ihave ⟨#Hrfp, %Hf⟩ := lpfull_fp γ q.src q.term bL l fp $$ Hfull
  obtain ⟨hfo, hwl, -⟩ := Hf
  ihave #HrL := logRecs_full γ bL fp l hfo $$ Hrfp Hrl
  have hi : uint.Z q.index + 1 < 2 ^ 64 := by
    have := Hpay.2; omega
  iexists fp ++ l
  iframe HrL
  ipureintro
  exact ⟨logIdx_of_wf (full_wf bL fp l hfo hwl), app_slice hfo Hpl.1 hi Hpl.2⟩

/-- **A `send` report's facts** (`factsExt` at `MsgFacts`, `FactsLe`): an append's full log, a
grant's vote. -/
theorem sendExt_b1 (γ : AntNames) (q : Msg) :
    □ isMessage (GF := GF) γ.raft.raftNames q ⊢
      factsExt γ (fun G0 G => FactsLe γ.R G0 G ∧ AntSim.RaftLaws G ∧ AntSim.MsgFacts G q) := by
  iintro #Hm
  iunfold factsExt
  iintro %G %hL #HF
  imodintro
  by_cases hty : q.ty = .app
  · ihave ⟨%L, #HrL, %HL⟩ := isMessage_app_log γ.raft.raftNames q hty $$ Hm
    ihave ⟨#HF', %H⟩ := raftFacts_addLog γ.R γ.raft.raftNames G L hL HL.1 $$ [HF HrL]
    · iframe HF HrL
    iexists RaftFacts.addLog G L
    iframe HF'
    ipureintro
    refine ⟨H.2, H.1, fun _ => ⟨L, List.mem_cons_self, HL.2⟩, ?_⟩
    rintro ⟨h, -⟩; rw [hty] at h; cases h
  · by_cases hvr : q.ty = .voteResp ∧ q.reject = false
    · have hv : isMessage (GF := GF) γ.raft.raftNames q ⊢
          isVote γ.raft.raftNames q.src q.term q.dst := by
        unfold isMessage; rw [hvr.1]; simp only [hvr.2, Bool.false_eq_true, ↓reduceIte]; exact .rfl
      ihave #Hv := hv $$ Hm
      ihave ⟨#HF', %H⟩ := raftFacts_addVote γ.R γ.raft.raftNames G (q.src, q.term, q.dst) hL
        $$ [HF Hv]
      · iframe HF Hv
      iexists RaftFacts.addVote G (q.src, q.term, q.dst)
      iframe HF'
      ipureintro
      exact ⟨H.2, H.1, fun h => absurd h hty, fun _ => List.mem_cons_self⟩
    · iexists G
      iframe HF
      ipureintro
      exact ⟨FactsLe.refl γ.R G, hL, fun h => absurd h hty, fun h => absurd h hvr⟩

end proof

end AntHarness
end EtcdGrove
end Perennial
