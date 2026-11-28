/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/gprot/Laws.lean (241f27e).
-/
/-
`gprot` (redesign R1) — the laws: the only way the code uses `Inv`.

* agreement laws (no invariant needed);
* one **update law per protocol step** (`proto.Model`), whose premises are the step's precondition
  as the code knows it (its own state `s`, persistent facts, pure facts), and whose conclusion is
  the updated halves and the new persistent facts;
* **reader laws** for the goroutines that read another goroutine's state (the replication
  goroutine reading its server's log and commit index), giving facts conditional on the term
  being unchanged;
* consequences for the checks (state-machine safety, log safety, election safety).

Masks: every law that opens `Inv` works under any `E ⊇ ↑gprotN`.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.gprot.Defs
public import Perennial.ProgramLogic.Bounds
public import Dsverify.Proof.github_com.hashicorp.raft.gprot.Internal

@[expose] public section

set_option linter.unusedVariables false
set_option linter.deprecated false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.hashicorp.raft
namespace gprot

open proto

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]
variable (γ : GNames)

/-! ## Agreement (no invariant) -/

theorem leaderIs_agree (T : Nat) (a b : SID) :
    leaderIs (GF := GF) γ T a ∗ leaderIs γ T b ⊢ ⌜a = b⌝ := by
  unfold leaderIs
  iintro ⟨#H1, #H2⟩
  iapply ghostMapElem_agree T γ.leader _ _ a b $$ H1 H2

theorem llogIdx_agree (T k : Nat) (e1 e2 : Entry) :
    llogIdx (GF := GF) γ T k e1 ∗ llogIdx γ T k e2 ⊢ ⌜e1 = e2⌝ := by
  unfold llogIdx
  iintro ⟨⟨_, #H1⟩, ⟨_, #H2⟩⟩
  iapply ghostMapElem_agree (T, k) γ.llog _ _ e1 e2 $$ H1 H2

theorem CIdx_agree (k : Nat) (e1 e2 : Entry) :
    CIdx (GF := GF) γ k e1 ∗ CIdx γ k e2 ⊢ ⌜e1 = e2⌝ := by
  unfold CIdx
  iintro ⟨⟨_, #H1⟩, ⟨_, #H2⟩⟩
  iapply mono_list_idx_agree γ.C (k - 1) e1 e2 $$ H1 H2

theorem len0Is_agree (T n1 n2 : Nat) :
    len0Is (GF := GF) γ T n1 ∗ len0Is γ T n2 ⊢ ⌜n1 = n2⌝ := by
  unfold len0Is
  iintro ⟨#H1, #H2⟩
  iapply ghostMapElem_agree T γ.len0 _ _ n1 n2 $$ H1 H2

theorem termCouple_lb (i : SID) (t t' : Nat) :
    termCouple (GF := GF) γ i t ∗ termLb γ i t' ⊢ ⌜t' ≤ t⌝ := by
  unfold termCouple termLb
  iintro ⟨H1, #H2⟩
  ihave %h := monoNatLbOwn_valid (γ.term i) _ t t' $$ H1 H2
  ipureintro; exact h.2

theorem termCouple_get_lb (i : SID) (t : Nat) :
    termCouple (GF := GF) γ i t ⊢ termCouple γ i t ∗ termLb γ i t := by
  unfold termCouple termLb
  iintro H
  ihave #Hlb := monoNatLbOwn_get (γ.term i) _ t $$ H
  iframe; iexact Hlb

theorem termLb_mono (i : SID) (t t' : Nat) (h : t' ≤ t) :
    termLb (GF := GF) γ i t ⊢ termLb γ i t' := by
  unfold termLb
  iintro #H
  iapply monoNatLbOwn_le t' h $$ H

theorem durLb_mono (i : SID) (k k' : Nat) (h : k' ≤ k) :
    durLb (GF := GF) γ i k ⊢ durLb γ i k' := by
  unfold durLb
  iintro #H
  iapply monoNatLbOwn_le k' h $$ H

theorem durView_lb (i : SID) (q : Qp) (d k : Nat) :
    durView (GF := GF) γ i q d ∗ durLb γ i k ⊢ ⌜k ≤ d⌝ := by
  unfold durView durLb
  iintro ⟨H1, #H2⟩
  ihave %h := monoNatLbOwn_valid (γ.dur i) _ d k $$ H1 H2
  ipureintro; exact h.2

theorem durView_get_lb (i : SID) (q : Qp) (d : Nat) :
    durView (GF := GF) γ i q d ⊢ durView γ i q d ∗ durLb γ i d := by
  unfold durView durLb
  iintro H
  ihave #Hlb := monoNatLbOwn_get (γ.dur i) _ d $$ H
  iframe; iexact Hlb

theorem durView_split (i : SID) (q1 q2 : Qp) (d : Nat) :
    durView (GF := GF) γ i (q1 + q2) d ⊣⊢ durView γ i q1 d ∗ durView γ i q2 d := by
  unfold durView
  exact (monoNatAuthOwn_fractional (GF := GF) (γ.dur i) d).fractional q1 q2

theorem termOk_of_termLb (j : SID) (t t' : Nat) (h : t ≤ t') :
    isSrv (GF := GF) γ j ∗ termLb γ j t' ⊢ termOk γ t := by
  unfold termOk
  iintro ⟨#Hv, #Hl⟩
  ileft
  iexists j, t'
  isplitr; · iexact Hv
  isplitr; · iexact Hl
  ipureintro; exact h

theorem termOk_of_aeValid (T prev pt : Nat) (ents : List Entry) (lci : Nat) :
    aeValid (GF := GF) γ T prev pt ents lci ⊢ termOk γ T := by
  unfold aeValid termOk
  iintro ⟨⟨%ℓ, #Hl⟩, -⟩
  iright; iright
  iexists ℓ; iexact Hl

theorem termOk_of_candIs (c : SID) (T li lt : Nat) :
    candIs (GF := GF) γ c T li lt ⊢ termOk γ T := by
  unfold termOk
  iintro #H
  iright; ileft
  iexists c, li, lt; iexact H

/-- Building a valid AppendEntries from what a replication goroutine read. -/
theorem aeValid_intro (T prev pt : Nat) (ents : List Entry) (lci : Nat) (ℓ : SID) :
    leaderIs (GF := GF) γ T ℓ ∗
    (⌜prev = 0 ∧ pt = 0⌝ ∨ ∃ e, ⌜1 ≤ prev ∧ e.term = pt⌝ ∗ llogIdx γ T prev e) ∗
    ([∗list] j ↦ e ∈ ents, llogIdx γ T (prev + 1 + j) e) ∗
    lciOk γ T lci ⊢
    aeValid γ T prev pt ents lci := by
  unfold aeValid
  iintro ⟨#Hl, #Hp, #He, #Hc⟩
  isplitr; · iexists ℓ; iexact Hl
  isplitr; · iexact Hp
  isplitr; · iexact He
  iexact Hc

/-- A heartbeat (no entries, no previous entry, commit index 0) is valid. -/
theorem aeValid_heartbeat (T : Nat) (ℓ : SID) :
    leaderIs (GF := GF) γ T ℓ ⊢ aeValid γ T 0 0 [] 0 := by
  unfold aeValid lciOk
  iintro #Hl
  isplitr; · iexists ℓ; iexact Hl
  isplitr; · ileft; ipureintro; exact ⟨rfl, rfl⟩
  isplitr; · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  ileft; ipureintro; rfl

theorem lciOk_zero (T : Nat) : ⊢ lciOk (GF := GF) γ T 0 := by
  unfold lciOk
  ileft; ipureintro; rfl

/-! ## Facts from the invariant -/

/-- Facts about a server's own state (stage 4: its log is empty or starts with the genesis; its
term is at least 1 once its log is not empty; its configuration entries are valid over the
servers). -/
theorem srvOwn_facts (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ⊢ |={E}=> srvOwn γ i s ∗ isSrv γ i ∗
      ⌜(s.log = [] ∨ ent s.log 1 = some γ.g) ∧ s.dur.1 ≤ s.log.length ∧ s.cidx ≤ s.dur.1 ∧
        s.vterm ≤ s.term ∧ (s.log ≠ [] → 1 ≤ s.term) ∧ s.term < 2 ^ 62 ∧ s.log.length < 2 ^ 62 ∧
        (∀ k e, ent s.log k = some e → e.kind = kConfig → cfgValid γ.srvs (γ.cv e.data)) ∧
        (∀ k e, ent s.log k = some e →
          e.kind = kCommand ∨ e.kind = kNoop ∨ e.kind = kBarrier ∨ e.kind = kConfig)⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, Ho⟩
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_peek γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  ihave Hs := Hcl $$ Hi
  ihave ⟨Hr, Hcc⟩ := Hr
  ihave ⟨Hr, %hb⟩ := receipt_bound _ $$ Hr
  have hi' : i ∈ σ.srvs := by rw [hg.2.1]; exact hi
  have hP := hg.1
  ihave ⟨Hh, #Hv⟩ := H_voter_get γ σ i hi' $$ Hh
  isplitl [Hh Hs Hr Hcc]
  · iframe; ipureintro; exact hg
  isplitl [Ho]; · iexact Ho
  isplitr; · iexact Hv
  ipureintro
  have ht : (σ.srv i).term ≤ σ.maxT := term_le_maxT σ i hP hi'
  have hl : (σ.srv i).log.length ≤ σ.maxI := log_le_maxI σ i hP hi'
  refine ⟨?_, dur_le_log σ i hP hi', (PInv.dur hP i hi').2, ((PInv.votes hP).2.1 i hi').1,
    term_ge_one σ i hP hi', by omega, by omega,
    fun k e h1 h2 => by rw [← hg.2.1, ← hg.2.2.2.1]; exact log_cfg_valid σ i k e hP hi' h1 h2,
    fun k e h1 => log_kinds σ i k e hP hg.2.2.2.2.1 hi' h1⟩
  rw [← hg.2.2.1]; exact log_genesis σ i hP hi'

/-- The genesis entry and the servers (stage 4: the genesis is a valid configuration over the
servers). -/
theorem genesis_facts (E : CoPset) (hE : ↑gprotN ⊆ E) :
    Inv (GF := GF) γ ⊢ |={E}=>
      ⌜γ.g.term = 1 ∧ γ.g.kind = kConfig ∧ γ.srvs.Nodup ∧ cfgValid γ.srvs (γ.cv γ.g.data)⌝ := by
  apply Inv_read0 γ E hE
  intro σ
  unfold InvBody
  iintro ⟨%hg, Hh, Hs, Hr⟩
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  ipureintro
  obtain ⟨h1, h2, h3, h4, _⟩ := PInv.gen hg.1
  rw [← hg.2.2.1, ← hg.2.1, ← hg.2.2.2.1]; exact ⟨h1, h2, h3, h4⟩

/-- (stage 4, FOLLOW-11) Every server's ID is non-empty (`alloc`'s premise; hr3's `voterIds n`): a
recorded vote's candidate reads back from the stable store as a non-nil slice (`requestVote`). -/
theorem srvs_ne_nil (E : CoPset) (hE : ↑gprotN ⊆ E) :
    Inv (GF := GF) γ ⊢ |={E}=> ⌜∀ j ∈ γ.srvs, j ≠ []⌝ := by
  apply Inv_read0 γ E hE
  intro σ
  unfold InvBody
  iintro ⟨%hg, Hh, Hs, Hr⟩
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  ipureintro
  exact hg.2.2.2.2.2

/-- (stage 4, FOLLOW-12) A recorded candidacy is of a term `≥ 1` (`IVotes`; `electTerm_upd` records
`s.term + 1`). -/
theorem candIs_pos (E : CoPset) (hE : ↑gprotN ⊆ E) (c : SID) (T li lt : Nat) :
    Inv (GF := GF) γ ∗ candIs γ c T li lt ⊢ |={E}=> ⌜1 ≤ T⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, #Hc⟩
  ihave ⟨Hh, %hc⟩ := H_cand_lookup γ σ c T li lt $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hc
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  ipureintro
  exact ((PInv.votes hg.1).2.2 c T _ hc).2.1

theorem isSrv_mem (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) :
    Inv (GF := GF) γ ∗ isSrv γ i ⊢ |={E}=> ⌜i ∈ γ.srvs⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody isSrv
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, #Hv⟩
  ihave ⟨Hh, %h⟩ := H_voter_lookup γ σ i $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hv
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  ipureintro; rw [← hg.2.1]; exact h

/-- The server's durable prefix, as a persistent lower bound. -/
theorem srvOwn_durLb (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ⊢ |={E}=> srvOwn γ i s ∗ durLb γ i s.dur.1 := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, Ho⟩
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_peek γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  ihave ⟨Ht, Hd, Hsv, Hl, Hc⟩ := (srvG_eq γ i (σ.srv i)).1 $$ Hi
  ihave #Hlb := monoNatLbOwn_get (γ.dur i) _ _ $$ Hd
  ihave Hi := (srvG_eq γ i (σ.srv i)).2 $$ [Ht Hd Hsv Hl Hc]
  · iframe
  ihave Hs := Hcl $$ Hi
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  isplitl [Ho]; · iexact Ho
  unfold durLb; iexact Hlb

theorem durLb_le (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState) (k : Nat) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ durLb γ i k ⊢ |={E}=> srvOwn γ i s ∗ ⌜k ≤ s.dur.1⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, Ho, #Hlb⟩
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_peek γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  ihave ⟨Hi, %h⟩ := srvG_dur_lb γ i (σ.srv i) k $$ [Hi]
  · isplitl [Hi]; iexact Hi; iexact Hlb
  ihave Hs := Hcl $$ Hi
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  iframe; ipureintro; exact h

/-- The log store's contents are the server's log. -/
theorem logCouple_agree (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState) (L : RLog) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ logCouple γ i L ⊢ |={E}=>
      srvOwn γ i s ∗ logCouple γ i L ∗ ⌜L = s.log⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, Ho, Hc⟩
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_peek γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  ihave ⟨Hi, Hc, %h⟩ := srvG_log_agree γ i (σ.srv i) L $$ [Hi Hc]
  · iframe
  ihave Hs := Hcl $$ Hi
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  iframe; ipureintro; exact h

/-- The main goroutine's view of the durable prefix is the server's. -/
theorem durView_agree (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState) (q : Qp) (d : Nat) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ durView γ i q d ⊢ |={E}=>
      srvOwn γ i s ∗ durView γ i q d ∗ ⌜d = s.dur.1⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, Ho, Hc⟩
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_peek γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  ihave ⟨Hi, Hc, %h⟩ := srvG_dur_agree γ i (σ.srv i) q d $$ [Hi Hc]
  · iframe
  ihave Hs := Hcl $$ Hi
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  iframe; ipureintro; exact h

/-- The log store's length is bounded (for readers without `srvOwn`). -/
theorem logCouple_bound (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (L : RLog) :
    Inv (GF := GF) γ ∗ logCouple γ i L ⊢ |={E}=> logCouple γ i L ∗ ⌜L.length < 2 ^ 62⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, Hc⟩
  ihave ⟨Hc, #Hv⟩ := logCouple_voter γ i L $$ Hc
  ihave ⟨Hh, %hi⟩ := H_voter_lookup γ σ i $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hv
  have hi' : i ∈ γ.srvs := by rw [← hg.2.1]; exact hi
  ihave ⟨Hi, Hcl⟩ := srvs_peek γ σ i hi' $$ Hs
  ihave ⟨Hi, Hc, %h⟩ := srvG_log_agree γ i (σ.srv i) L $$ [Hi Hc]
  · iframe
  ihave Hs := Hcl $$ Hi
  ihave ⟨Hr, Hcc⟩ := Hr
  ihave ⟨Hr, %hb⟩ := receipt_bound _ $$ Hr
  isplitl [Hh Hs Hr Hcc]
  · iframe; ipureintro; exact hg
  iframe; ipureintro
  have hl : (σ.srv i).log.length ≤ σ.maxI := log_le_maxI σ i hg.1 hi
  rw [h]; omega

theorem termCouple_agree (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState) (t : Nat) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ termCouple γ i t ⊢ |={E}=>
      srvOwn γ i s ∗ termCouple γ i t ∗ ⌜t = s.term⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, Ho, Hc⟩
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_peek γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  ihave ⟨Hi, Hc, %h⟩ := srvG_term_agree γ i (σ.srv i) t $$ [Hi Hc]
  · iframe
  ihave Hs := Hcl $$ Hi
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  iframe; ipureintro; exact h

theorem cidxCouple_agree (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState) (c : Nat) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ cidxCouple γ i c ⊢ |={E}=>
      srvOwn γ i s ∗ cidxCouple γ i c ∗ ⌜c = s.cidx⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, Ho, Hc⟩
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_peek γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  ihave ⟨Hi, Hc, %h⟩ := srvG_cidx_agree γ i (σ.srv i) c $$ [Hi Hc]
  · iframe
  ihave Hs := Hcl $$ Hi
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  iframe; ipureintro; exact h

/-- Index 1 of every leader log is the genesis entry. (`ILeaders`/`IGen`.) -/
theorem llogIdx_one (E : CoPset) (hE : ↑gprotN ⊆ E) (T : Nat) (e : Entry) :
    Inv (GF := GF) γ ∗ llogIdx γ T 1 e ⊢ |={E}=> ⌜e = γ.g⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, #He⟩
  ihave ⟨Hh, %h⟩ := H_llog_lookup γ σ T 1 e $$ [Hh]
  · iframe Hh; iexact He
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  ipureintro
  have hP := hg.1
  rw [← hg.2.2.1]
  by_cases hl : σ.leader T = none
  · by_cases hT : T = 1
    · subst hT
      have h1 := (PInv.gen hP).2.2.2.2.1
      rw [h1] at h; simp [ent] at h; exact h.symm
    · have h0 := (PInv.leaders hP).2 T hT hl
      rw [h0] at h; simp [ent] at h
  · obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp hl
    have h1 := ((PInv.leaders hP).1 T ℓ hℓ).2.2.2.2.1
    rw [h1] at h; exact (Option.some.inj h).symm

/-- The candidate of the stable store's last vote is one of the servers. (`IVotes`.) -/
theorem srvOwn_vcand (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ⊢ |={E}=> srvOwn γ i s ∗ ⌜0 < s.vterm → s.vcand ∈ γ.srvs⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, Ho⟩
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_peek γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  ihave Hs := Hcl $$ Hi
  have hi' : i ∈ σ.srvs := by rw [hg.2.1]; exact hi
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  iframe Ho
  ipureintro
  intro hv
  obtain ⟨L, b, hvote⟩ := ((PInv.votes hg.1).2.1 i hi').2 hv
  obtain ⟨_, _, _, ⟨li, lt, hc, _⟩, _⟩ := (PInv.votes hg.1).1 _ _ _ _ _ hvote
  rw [← hg.2.1]
  exact ((PInv.votes hg.1).2.2 _ _ _ hc).1

/-! ## Update laws, one per protocol step -/

/-- **setTerm** at the `currentTerm` atomic store: adopt an existing term `t ≥ s.term`. -/
theorem setTerm_upd (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState) (t : Nat)
    (ht : s.term ≤ t) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ termCouple γ i s.term ∗ termOk γ t ⊢ |={E}=>
      srvOwn γ i { s with term := t } ∗ termCouple γ i t ∗ termLb γ i t := by
  apply Inv_upd γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr, Hcc⟩, Ho, Htc, #Hok⟩
  ihave ⟨Hh, Hs, %htm⟩ := H_termOk γ σ hg t $$ [Hh Hs Hok]
  · iframe; iexact Hok
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_open γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  have hi' : i ∈ σ.srvs := by rw [hg.2.1]; exact hi
  obtain ⟨hP', hGr⟩ := setTerm_inv σ i t hg.1 ⟨hi', ht, htm⟩
  ihave ⟨Ht, Hd, Hsv, Hl, Hc⟩ := (srvG_eq γ i (σ.srv i)).1 $$ Hi
  unfold termCouple termLb
  imod monoNat_update_halves (γ.term i) (σ.srv i).term (σ.srv i).term t ht $$ [Ht Htc]
    with ⟨Ht, Htc, #Hlb⟩
  · iframe
  imod srvOwn_update γ i (σ.srv i) (σ.srv i) { σ.srv i with term := t } $$ [Ho Hsv]
    with ⟨Ho, Hsv⟩
  · iframe
  ihave Hi := (srvG_eq γ i { σ.srv i with term := t }).2 $$ [Ht Hd Hsv Hl Hc]
  · iframe
  ihave Hs := Hcl $$ %{ σ.srv i with term := t } Hi
  imod HistG_grow γ σ (setTerm σ i t) hg.1 hGr (fun T k e h _ => ⟨T, h⟩) [] (fun _ _ => rfl) [] (fun _ _ => rfl)
    [] (fun _ _ => rfl) [] (fun _ _ => rfl) [] (fun _ _ => rfl) [] (fun _ _ => rfl)
    [] (fun _ _ => rfl) $$ Hh with Hh
  imodintro
  isplitl [Hh Hs Hr Hcc]
  · iapply InvInner_close γ (setTerm σ i t) (upd σ.srv i { σ.srv i with term := t }) (σ.maxT + σ.maxI) rfl (Nat.le_refl _) (GInv_step hg hP' hGr hg.2.2.2.2.1)
    iframe
    iapply CcfgG_congr γ σ (setTerm σ i t) rfl rfl rfl $$ Hcc
  isplitl [Ho]; · iexact Ho
  isplitl [Htc]; · iexact Htc
  iexact Hlb

/-- **newTerm + recordCand** at `electSelf`'s `currentTerm` store: a new term, and the candidate's
last entry recorded for its `RequestVote`. Costs one receipt. (Stage 2) The candidate also gets its
publications of the new term, none yet (`pubOwn _ c (s.term + 1) 0`): it is the only one that can
publish in that term, if it becomes its leader. (Stage 4) It also gets both halves of its
commitment's configuration for that term (`ccfgOwn`, any value until it becomes leader,
`becomeLeader_upd`); a non-member at term 0 starts an election of term 1. -/
theorem electTerm_upd (E : CoPset) (hE : ↑gprotN ⊆ E) (c : SID) (s : SState) :
    Inv (GF := GF) γ ∗ srvOwn γ c s ∗ termCouple γ c s.term ∗ receipt 1 ⊢ |={E}=>
      srvOwn γ c { s with term := s.term + 1 } ∗ termCouple γ c (s.term + 1) ∗
      termLb γ c (s.term + 1) ∗ candIs γ c (s.term + 1) s.log.length (lastTerm s.log) ∗
      pubOwn γ c (s.term + 1) 0 ∗ ccfgOwn γ c (s.term + 1) 0 ∗ ccfgOwn γ c (s.term + 1) 0 := by
  apply Inv_upd γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr, Hcc⟩, Ho, Htc, Hr1⟩
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_open γ σ hg c s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  have hi' : c ∈ σ.srvs := by rw [hg.2.1]; exact hi
  have hP := hg.1
  have htm : (σ.srv c).term ≤ σ.maxT := term_le_maxT σ c hP hi'
  obtain ⟨hP1, hG1⟩ := newTerm_inv σ c hP hi'
  have hterm1 : (newTerm σ c).term c = (σ.srv c).term + 1 := by
    simp [newTerm, PState.term, upd]
  have hlog1 : (newTerm σ c).log c = (σ.srv c).log := by
    simp [newTerm, PState.log, upd]
  have hfresh : σ.cand c ((σ.srv c).term + 1) = none := by
    cases h : σ.cand c ((σ.srv c).term + 1) with
    | none => rfl
    | some x =>
      have := ((PInv.votes hP).2.2 c _ x h).2.2
      unfold PState.term at this; omega
  have hcand : (newTerm σ c).cand c ((newTerm σ c).term c) = none := by
    rw [hterm1]; exact hfresh
  have hlt1 : lastTerm ((newTerm σ c).log c) < (newTerm σ c).term c := by
    have := lastTerm_le_term σ c hP hi'
    rw [hlog1, hterm1]; unfold PState.log PState.term at this; omega
  obtain ⟨hP2, hG2⟩ :=
    recordCand_inv (newTerm σ c) c hP1 ⟨hi', by rw [hterm1]; omega, hlt1, hcand⟩
  have hGr := grows_trans hG1 hG2
  have oC : ∀ p, p ∉ [(c, (σ.srv c).term + 1)] →
      candF (recordCand (newTerm σ c) c) p = candF σ p := by
    intro ⟨a, b⟩ hp
    simp only [candF, recordCand, updST]
    split
    · rename_i h
      exfalso; apply hp; rw [h.1, h.2, hterm1]; simp
    · rfl
  have hcand2 : (recordCand (newTerm σ c) c).cand c ((σ.srv c).term + 1) =
      some ((σ.srv c).log.length, lastTerm (σ.srv c).log) := by
    unfold recordCand updST
    rw [hlog1]
    exact if_pos ⟨rfl, hterm1.symm⟩
  have hrc : (recordCand (newTerm σ c) c).maxT + (recordCand (newTerm σ c) c).maxI ≤
      σ.maxT + σ.maxI + 1 := by
    simp only [recordCand, newTerm, PState.term]; omega
  ihave ⟨Ht, Hd, Hsv, Hl, Hc⟩ := (srvG_eq γ c (σ.srv c)).1 $$ Hi
  unfold termCouple termLb
  imod monoNat_update_halves (γ.term c) (σ.srv c).term (σ.srv c).term ((σ.srv c).term + 1)
    (by omega) $$ [Ht Htc] with ⟨Ht, Htc, #Hlb⟩
  · iframe
  imod srvOwn_update γ c (σ.srv c) (σ.srv c) { σ.srv c with term := (σ.srv c).term + 1 }
    $$ [Ho Hsv] with ⟨Ho, Hsv⟩
  · iframe
  ihave Hi := (srvG_eq γ c { σ.srv c with term := (σ.srv c).term + 1 }).2 $$ [Ht Hd Hsv Hl Hc]
  · iframe
  ihave Hs := Hcl $$ %{ σ.srv c with term := (σ.srv c).term + 1 } Hi
  have hcandIff : ∀ c' T', (recordCand (newTerm σ c) c).cand c' T' ≠ none ↔
      (σ.cand c' T' ≠ none ∨ (c' = c ∧ T' = (σ.srv c).term + 1)) := by
    intro c' T'
    show updST σ.cand c ((newTerm σ c).term c) _ c' T' ≠ none ↔ _
    rw [hterm1, updST_apply]
    by_cases hh : c' = c ∧ T' = (σ.srv c).term + 1
    · rw [if_pos hh]; simp [hh]
    · rw [if_neg hh]
      constructor
      · exact Or.inl
      · rintro (h | h)
        · exact h
        · exact absurd h hh
  have hpubs := GMapOf_congr (GF := GF) γ.pubs (pubsF σ) (pubsF (recordCand (newTerm σ c) c))
    (fun _ => rfl)
  imod HistG_grow_with γ σ (recordCand (newTerm σ c) c) hP hGr (fun T k e h _ => ⟨T, h⟩) [] (fun _ _ => rfl) [] (fun _ _ => rfl)
    [] (fun _ _ => rfl) [(c, (σ.srv c).term + 1)] oC [] (fun _ _ => rfl) [] (fun _ _ => rfl)
    [] (fun _ _ => rfl) emp (pubOwn γ c ((σ.srv c).term + 1) 0)
    (by iintro ⟨Hp, H, -⟩
        imod PubMaxG_alloc γ σ _ c ((σ.srv c).term + 1) hGr rfl hfresh hcandIff $$ H with ⟨H, Hk⟩
        imodintro
        isplitl [Hp]; · iapply hpubs $$ Hp
        isplitl [H]; · iexact H
        iexact Hk) $$ [Hh] with ⟨Hh, Hpo⟩
  · isplitl [Hh]; iexact Hh; iempintro
  ihave ⟨Hh, #Hcand⟩ := H_cand_get γ (recordCand (newTerm σ c) c) c ((σ.srv c).term + 1)
    (σ.srv c).log.length (lastTerm (σ.srv c).log) hcand2 $$ Hh
  ihave Hr := (receipt_add (GF := GF) (σ.maxT + σ.maxI) 1).2 $$ [Hr Hr1]
  · iframe
  have hnl : (recordCand (newTerm σ c) c).leader ((σ.srv c).term + 1) ≠ some c := by
    intro hl
    have := ((PInv.leaders hP).1 _ _ hl).2.2.2.2.2.2.2.1
    rw [hfresh] at this; cases this
  imod CcfgG_alloc γ σ (recordCand (newTerm σ c) c) c ((σ.srv c).term + 1) hfresh hcandIff
    (fun T' ℓ h => ⟨h, rfl⟩) hnl $$ Hcc with ⟨Hcc, Hk1, Hk2⟩
  imodintro
  isplitl [Hh Hs Hr Hcc]
  · iapply InvInner_close γ (recordCand (newTerm σ c) c) (upd σ.srv c { σ.srv c with term := (σ.srv c).term + 1 }) (σ.maxT + σ.maxI + 1) rfl (hrc) (GInv_step hg hP2 hGr hg.2.2.2.2.1)
    iframe
  isplitl [Ho]; · iexact Ho
  isplitl [Htc]; · iexact Htc
  isplitr; · iexact Hlb
  isplitr; · iexact Hcand
  isplitl [Hpo]; · iexact Hpo
  isplitl [Hk1]; · iexact Hk1
  iexact Hk2

/-- **grantVote** (`persistVote`): vote for `c`, whose valid request carried `(li, lt)`. -/
theorem grantVote_upd (E : CoPset) (hE : ↑gprotN ⊆ E) (j c : SID) (s : SState) (li lt : Nat)
    (hv : s.vterm < s.term) (hup : upToDate li lt s.log) :
    Inv (GF := GF) γ ∗ srvOwn γ j s ∗ candIs γ c s.term li lt ⊢ |={E}=>
      srvOwn γ j { s with vterm := s.term, vcand := c } ∗ voteIs γ j s.term c := by
  apply Inv_upd γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr, Hcc⟩, Ho, #Hc⟩
  ihave ⟨Hh, %hc⟩ := H_cand_lookup γ σ c s.term li lt $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hc
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_open γ σ hg j s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  have hi' : j ∈ σ.srvs := by rw [hg.2.1]; exact hi
  obtain ⟨hP', hGr⟩ := grantVote_inv σ j c hg.1 ⟨hi', hv, li, lt, hc, hup⟩
  have oV : ∀ p, p ∉ [(j, (σ.srv j).term)] → votesF (grantVote σ j c) p = votesF σ p := by
    intro ⟨a, b⟩ hp
    simp only [votesF, grantVote, updST]
    split
    · rename_i h
      exfalso; apply hp; rw [h.1, h.2]; simp [PState.term]
    · rfl
  have hvote : (grantVote σ j c).votes j (σ.srv j).term =
      some (c, σ.log j, decide (σ.leader (σ.term j) = none)) := by
    unfold grantVote updST
    exact if_pos ⟨rfl, rfl⟩
  ihave ⟨Ht, Hd, Hsv, Hl, Hcx⟩ := (srvG_eq γ j (σ.srv j)).1 $$ Hi
  imod srvOwn_update γ j (σ.srv j) (σ.srv j)
    { σ.srv j with vterm := (σ.srv j).term, vcand := c } $$ [Ho Hsv] with ⟨Ho, Hsv⟩
  · iframe
  ihave Hi := (srvG_eq γ j { σ.srv j with vterm := (σ.srv j).term, vcand := c }).2
    $$ [Ht Hd Hsv Hl Hcx]
  · iframe
  ihave Hs := Hcl $$ %{ σ.srv j with vterm := (σ.srv j).term, vcand := c } Hi
  imod HistG_grow γ σ (grantVote σ j c) hg.1 hGr (fun T k e h _ => ⟨T, h⟩) [] (fun _ _ => rfl) [] (fun _ _ => rfl)
    [] (fun _ _ => rfl) [] (fun _ _ => rfl) [(j, (σ.srv j).term)] oV [] (fun _ _ => rfl)
    [] (fun _ _ => rfl) $$ Hh with Hh
  ihave ⟨Hh, #Hvote⟩ := H_vote_get γ (grantVote σ j c) j (σ.srv j).term c _ _ hvote $$ Hh
  imodintro
  isplitl [Hh Hs Hr Hcc]
  · iapply InvInner_close γ (grantVote σ j c) (upd σ.srv j { σ.srv j with vterm := (σ.srv j).term, vcand := c }) (σ.maxT + σ.maxI) rfl (Nat.le_refl _) (GInv_step hg hP' hGr hg.2.2.2.2.1)
    iframe
    iapply CcfgG_congr γ σ (grantVote σ j c) rfl rfl rfl $$ Hcc
  isplitl [Ho]; · iexact Ho
  iexact Hvote

/-- The stable store's last vote is a granted vote (granting it again needs no step). -/
theorem vote_again (E : CoPset) (hE : ↑gprotN ⊆ E) (j : SID) (s : SState) (hv : 0 < s.vterm) :
    Inv (GF := GF) γ ∗ srvOwn γ j s ⊢ |={E}=> srvOwn γ j s ∗ voteIs γ j s.vterm s.vcand := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, Ho⟩
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_peek γ σ hg j s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  ihave Hs := Hcl $$ Hi
  have hi' : j ∈ σ.srvs := by rw [hg.2.1]; exact hi
  obtain ⟨L, b, hvb⟩ := ((PInv.votes hg.1).2.1 j hi').2 hv
  ihave ⟨Hh, #Hvote⟩ := H_vote_get γ σ j (σ.srv j).vterm (σ.srv j).vcand L b hvb $$ Hh
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  isplitl [Ho]; · iexact Ho
  iexact Hvote

/-- **becomeLeader**: a quorum `Q` of the latest configuration of its log (stage 4) granted `c` its
votes of its current term, its log unchanged since its election started. (Stage 4) Both halves of
its commitment's configuration, at their pre-election value `0` (`electTerm_upd`; review tier-2 2:
so `c` does not lead `s.term` yet, since a leader's `ccfg` is a configuration entry's index `≥ 1`,
and the model's `becomeLeader` needs no branch for a second call), are set to its latest
configuration's index (`newCommitment` over `configurations.latest`). (Interface stage 4 before the
review: the halves at any `p0`.) -/
theorem becomeLeader_upd (E : CoPset) (hE : ↑gprotN ⊆ E) (c : SID) (s : SState) (Q : List SID)
    (hQ : isQuorumOf (cfgOfC γ.cv s.log) Q) :
    Inv (GF := GF) γ ∗ srvOwn γ c s ∗ candIs γ c s.term s.log.length (lastTerm s.log) ∗
      ([∗list] j ∈ Q, voteIs γ j s.term c) ∗ ccfgOwn γ c s.term 0 ∗ ccfgOwn γ c s.term 0 ⊢
      |={E}=>
      srvOwn γ c s ∗ leaderIs γ s.term c ∗ len0Is γ s.term s.log.length ∗
      ccfgOwn γ c s.term (lastCfgIdx s.log) ∗ ccfgOwn γ c s.term (lastCfgIdx s.log) := by
  apply Inv_upd γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr, Hcc⟩, Ho, #Hc, #Hvs, Hk1, Hk2⟩
  ihave ⟨Hh, %hc⟩ := H_cand_lookup γ σ c s.term s.log.length (lastTerm s.log) $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hc
  ihave ⟨Hh, %hvs⟩ := H_vote_lookup_list γ σ s.term c Q $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hvs
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_peek γ σ hg c s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  ihave Hs := Hcl $$ Hi
  have hi' : c ∈ σ.srvs := by rw [hg.2.1]; exact hi
  have hP := hg.1
  have hQ' : isQuorumOf (cfgOf σ (σ.log c)) Q := by
    show isQuorumOf (cfgOfC σ.cv (σ.srv c).log) Q
    rw [hg.2.2.2.1]; exact hQ
  have hpre : becomeLeaderPre σ c := ⟨hi', hc, Q, hQ', hvs⟩
  obtain ⟨hP', hGr⟩ := becomeLeader_inv σ c hP hpre
  obtain ⟨hL', hL0'⟩ := becomeLeader_len0 σ c hP hpre
  ihave ⟨Hcc, Hk1, %hk⟩ := CcfgG_lookup γ σ c (σ.srv c).term 0 $$ [Hcc Hk1]
  · iframe
  -- (stage 4) `c` does not lead its term yet: a leader of it would be `c` (election safety), whose
  -- commitment's configuration is not `0`.
  have hnone : σ.leader (σ.term c) = none := by
    cases hl : σ.leader (σ.term c) with
    | none => rfl
    | some ℓ =>
      exfalso
      have hLM : LMok σ (σ.log c) := ((PInv.logs hP).1 c hi').1
      have hℓ : ℓ = c := elect_safety σ hP (σ.term c) ℓ c (σ.log c) Q hl hLM hc hQ'
        (fun j hj => by obtain ⟨L, b, h⟩ := hvs j hj; exact ⟨L, b, h⟩)
      subst hℓ
      have h0 : σ.ccfg (σ.term ℓ) = 0 := hk.2 hl
      have := ccfg_pos hP hl
      omega
  have hbl : becomeLeader σ c =
      { σ with
        leader := updT σ.leader (σ.term c) (some c)
        llog := updT σ.llog (σ.term c) (σ.log c)
        len0 := updT σ.len0 (σ.term c) (σ.log c).length
        ccfg := updT σ.ccfg (σ.term c) (lastCfgIdx (σ.log c)) } := by
    unfold becomeLeader; rw [if_pos hnone]
  imod CcfgG_set γ σ (becomeLeader σ c) c (σ.srv c).term 0 0 (lastCfgIdx (σ.srv c).log)
    (by rw [hbl])
    (fun T' hT' => by
      rw [hbl]; show updT σ.leader _ _ T' = _ ∧ updT σ.ccfg _ _ T' = _
      simp only [updT, PState.term] at hT' ⊢; simp [hT'])
    (fun c' hc' => by
      rw [hbl] at hc' ⊢
      change updT σ.leader (σ.term c) (some c) (σ.term c) = some c' at hc'
      simp only [updT, if_pos rfl] at hc'
      cases hc'
      exact ⟨rfl, by show updT σ.ccfg (σ.term c) _ (σ.term c) = _; simp [updT]; rfl⟩)
    $$ [Hcc Hk1 Hk2] with ⟨Hcc, Hk1, Hk2⟩
  · iframe
  have hsrv : (becomeLeader σ c).srv = σ.srv := by rw [hbl]
  have hmax : (becomeLeader σ c).maxT + (becomeLeader σ c).maxI = σ.maxT + σ.maxI := by
    rw [hbl]
  have hT2 : 2 ≤ σ.term c := ((PInv.leaders hP').1 _ _ hL').2.1
  have hLcB : ∀ T k e, ent ((becomeLeader σ c).llog T) k = some e → e.kind = kCommand →
      ∃ T', ent (σ.llog T') k = some e := by
    intro T k e he _
    rw [hbl] at he
    change ent (updT σ.llog (σ.term c) (σ.log c) T) k = some e at he
    unfold updT at he
    split at he
    · exact ⟨_, LMok_ent ((PInv.logs hP).1 c hi').1 he⟩
    · exact ⟨T, he⟩
  have hbc : (becomeLeader σ c).cand = σ.cand := by rw [hbl]
  have hbv : (becomeLeader σ c).votes = σ.votes := by rw [hbl]
  have hba : (becomeLeader σ c).acked = σ.acked := by rw [hbl]
  have hbm : (becomeLeader σ c).commits = σ.commits := by rw [hbl]
  have hL'' : (becomeLeader σ c).leader (σ.srv c).term = some c := hL'
  have hL0'' : (becomeLeader σ c).len0 (σ.srv c).term = (σ.srv c).log.length := hL0'
  have hll : σ.leader (σ.term c) = none → σ.llog (σ.term c) = [] :=
    fun h => (PInv.leaders hP).2 _ (by omega) h
  have oL : ∀ T, T ∉ [σ.term c] → (becomeLeader σ c).leader T = σ.leader T := by
    intro T hT
    simp only [List.mem_singleton] at hT
    rw [hbl]; show updT σ.leader _ _ T = _
    simp [updT, hT]
  have oL0 : ∀ T, T ∉ [σ.term c] → len0F (becomeLeader σ c) T = len0F σ T := by
    intro T hT
    simp only [List.mem_singleton] at hT
    unfold len0F; rw [hbl]
    show (if updT σ.leader _ _ T ≠ none ∨ T = 1 then some (updT σ.len0 _ _ T) else none) = _
    simp [updT, hT]
  have oLl : ∀ p, p ∉ (List.range ((σ.log c).length + 1)).map (fun k => (σ.term c, k)) →
      llogF (becomeLeader σ c) p = llogF σ p := by
    intro ⟨T, k⟩ hp
    unfold llogF; rw [hbl]
    show ent (updT σ.llog (σ.term c) (σ.log c) T) k = ent (σ.llog T) k
    unfold updT
    split
    · rename_i hT
      subst hT
      have hk : (σ.log c).length < k := by
        apply Nat.lt_of_not_le
        intro hk
        apply hp
        rw [List.mem_map]
        exact ⟨k, List.mem_range.mpr (by omega), rfl⟩
      rw [hll hnone, ent_none_of_gt _ _ hk, ent_none_of_gt _ _ (by simp; omega)]
    · rfl
  imod HistG_grow γ σ (becomeLeader σ c) hP hGr hLcB [σ.term c] oL
    ((List.range ((σ.log c).length + 1)).map (fun k => (σ.term c, k))) oLl
    [σ.term c] oL0 [] (fun _ _ => by simp only [candF, hbc])
    [] (fun _ _ => by simp only [votesF, hbv])
    [] (fun p _ => acksF_congr hba p)
    [] (fun p _ => commitsF_congr hbm p) $$ Hh with Hh
  ihave ⟨Hh, #Hlead⟩ := H_leader_get γ (becomeLeader σ c) (σ.srv c).term c hL' $$ Hh
  ihave ⟨Hh, #Hlen⟩ := H_len0_get γ (becomeLeader σ c) (σ.srv c).term (σ.srv c).log.length
    (by unfold len0F; rw [if_pos (Or.inl (by rw [hL'']; simp)), hL0'']) $$ Hh
  imodintro
  isplitl [Hh Hs Hr Hcc]
  · iapply InvInner_close γ (becomeLeader σ c) σ.srv (σ.maxT + σ.maxI) hsrv (Nat.le_of_eq hmax)
      (GInv_step hg hP' hGr (becomeLeader_kinds σ c hP hpre hg.2.2.2.2.1))
    iframe
  isplitl [Ho]; · iexact Ho
  isplitr; · iexact Hlead
  isplitr; · iexact Hlen
  isplitl [Hk1]; · iexact Hk1
  iexact Hk2

/-- **leaderAppend** (before the log store's `StoreLogs`, stage 2: so that the entries' `llogIdx`
facts can be passed to the store, see `iface/Stores.lean`): the leader of its term appends its own
no-op or barrier entries (commands: `Ops.leaderAppendCmd_upd`, which takes their tokens; a barrier,
from `Raft.Barrier`, has no token). Costs one receipt per entry. -/
theorem leaderAppend_upd (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState) (es : RLog)
    (hes : ∀ e ∈ es, e.term = s.term ∧ (e.kind = kNoop ∨ e.kind = kBarrier)) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ logCouple γ i s.log ∗ leaderIs γ s.term i ∗
      receipt es.length ⊢ |={E}=>
      srvOwn γ i { s with log := s.log ++ es } ∗ logCouple γ i (s.log ++ es) ∗
      ([∗list] k ↦ e ∈ es, llogIdx γ s.term (s.log.length + 1 + k) e) := by
  apply Inv_upd γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr, Hcc⟩, Ho, Hlc, #Hl, Hrs⟩
  ihave ⟨Hh, %hl⟩ := H_leader_lookup γ σ s.term i $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hl
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_open γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  have hi' : i ∈ σ.srvs := by rw [hg.2.1]; exact hi
  have hP := hg.1
  have hpreA : leaderAppendPre σ i es := ⟨hi', hl, fun e he => ⟨(hes e he).1, Or.inr (hes e he).2⟩⟩
  obtain ⟨hP', hGr⟩ := leaderAppend_inv σ i es hP hpreA
  have hLL : (σ.srv i).log = σ.llog (σ.srv i).term := leader_log σ i hP hi' hl
  have hlen : (σ.srv i).log.length ≤ σ.maxI := log_le_maxI σ i hP hi'
  have oLl : ∀ p, p ∉ (List.range es.length).map
      (fun k => (σ.term i, (σ.log i).length + 1 + k)) →
      llogF (leaderAppend σ i es) p = llogF σ p := by
    intro ⟨T, k⟩ hp
    unfold llogF; simp only [leaderAppend, updT]
    split
    · rename_i hT
      subst hT
      have hLL' : σ.log i = σ.llog (σ.term i) := hLL
      rw [← hLL']
      by_cases hk : k ≤ (σ.log i).length
      · exact ent_append_left _ _ _ hk
      · have hk2 : (σ.log i).length + es.length < k := by
          apply Nat.lt_of_not_le
          intro hk2
          apply hp
          rw [List.mem_map]
          exact ⟨k - (σ.log i).length - 1, List.mem_range.mpr (by omega), by
            simp only [Prod.mk.injEq, true_and]; omega⟩
        rw [ent_none_of_gt _ _ (by simp; omega), ent_none_of_gt _ _ (by omega)]
    · rfl
  have hLcA : ∀ T k e, ent ((leaderAppend σ i es).llog T) k = some e → e.kind = kCommand →
      ∃ T', ent (σ.llog T') k = some e := by
    intro T k e he hk
    rw [la_llog hP hpreA] at he
    split at he
    · by_cases hk' : k ≤ (σ.llog T).length
      · rw [proto.ent_append_left _ _ _ hk'] at he; exact ⟨T, he⟩
      · have := (hes e (ent_append_mem he (by omega))).2
        rw [hk] at this; simp [kCommand, kNoop, kBarrier] at this
    · exact ⟨T, he⟩
  have hnew : ∀ (j : Nat) (e : Entry), es[j]? = some e →
      ent ((leaderAppend σ i es).llog (σ.srv i).term) ((σ.srv i).log.length + 1 + j) = some e := by
    intro j e hj
    show ent (updT σ.llog (σ.term i) (σ.log i ++ es) (σ.term i)) ((σ.log i).length + 1 + j) = some e
    simp only [updT, if_true]
    rw [ent_append_right]; exact hj
  have hrc : (leaderAppend σ i es).maxT + (leaderAppend σ i es).maxI ≤
      σ.maxT + σ.maxI + es.length := by
    simp only [leaderAppend, PState.log]; omega
  ihave ⟨Ht, Hd, Hsv, Hlg, Hc⟩ := (srvG_eq γ i (σ.srv i)).1 $$ Hi
  unfold logCouple
  icases Hlc with ⟨Hlc, #Hv⟩
  imod ghostVar_update_halves ((σ.srv i).log ++ es) (γ.slog i) _ _ $$ Hlg Hlc with ⟨Hlg, Hlc⟩
  imod srvOwn_update γ i (σ.srv i) (σ.srv i) { σ.srv i with log := (σ.srv i).log ++ es }
    $$ [Ho Hsv] with ⟨Ho, Hsv⟩
  · iframe
  ihave Hi := (srvG_eq γ i { σ.srv i with log := (σ.srv i).log ++ es }).2 $$ [Ht Hd Hsv Hlg Hc]
  · iframe
  ihave Hs := Hcl $$ %{ σ.srv i with log := (σ.srv i).log ++ es } Hi
  imod HistG_grow γ σ (leaderAppend σ i es) hP hGr hLcA [] (fun _ _ => rfl)
    ((List.range es.length).map (fun k => (σ.term i, (σ.log i).length + 1 + k))) oLl
    [] (fun _ _ => rfl) [] (fun _ _ => rfl) [] (fun _ _ => rfl) [] (fun _ _ => rfl)
    [] (fun _ _ => rfl) $$ Hh with Hh
  ihave ⟨Hh, #Hents⟩ := H_llog_get_list γ (leaderAppend σ i es) (σ.srv i).term es
    (fun k => (σ.srv i).log.length + 1 + k) hnew $$ Hh
  ihave Hr := (receipt_add (GF := GF) (σ.maxT + σ.maxI) es.length).2 $$ [Hr Hrs]
  · iframe
  imodintro
  isplitl [Hh Hs Hr Hcc]
  · iapply InvInner_close γ (leaderAppend σ i es) (upd σ.srv i { σ.srv i with log := (σ.srv i).log ++ es }) (σ.maxT + σ.maxI + es.length) rfl (hrc) (GInv_step hg hP' hGr (leaderAppend_kinds σ i es hP hpreA hg.2.2.2.2.1))
    iframe
    iapply CcfgG_congr γ σ (leaderAppend σ i es) rfl rfl rfl $$ Hcc
  isplitl [Ho]; · iexact Ho
  isplitl [Hlc]; · iframe; iexact Hv
  iexact Hents

/-- The bound for a leader's append, before it computes the new indexes: with `n` receipts in
hand, the indexes stay below `2^62`. -/
theorem append_bound (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState) (n : Nat) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ receipt n ⊢ |={E}=>
      srvOwn γ i s ∗ receipt n ∗ ⌜s.log.length + n < 2 ^ 62⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr, Hcc⟩, Ho, Hn⟩
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_peek γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  ihave Hs := Hcl $$ Hi
  have hi' : i ∈ σ.srvs := by rw [hg.2.1]; exact hi
  have hlen : (σ.srv i).log.length ≤ σ.maxI := log_le_maxI σ i hg.1 hi'
  ihave Hr := (receipt_add (GF := GF) (σ.maxT + σ.maxI) n).2 $$ [Hr Hn]
  · iframe
  ihave ⟨Hr, %hb⟩ := receipt_bound _ $$ Hr
  ihave ⟨Hr, Hn⟩ := (receipt_add (GF := GF) (σ.maxT + σ.maxI) n).1 $$ Hr
  isplitl [Hh Hs Hr Hcc]
  · iframe; ipureintro; exact hg
  iframe; ipureintro; omega

/-- **truncate** at the log store's `DeleteRange`. -/
theorem truncate_upd (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState)
    (prev pt : Nat) (ents : RLog) (lci j : Nat)
    (hpre : prevMatch s.log prev pt ∧ matchedUpTo s.log prev ents j ∧ j < ents.length ∧
      prev + 1 + j ≤ s.log.length ∧ termAt s.log (prev + 1 + j) ≠ termAt ents (j + 1)) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ logCouple γ i s.log ∗ aeValid γ s.term prev pt ents lci ⊢
      |={E}=>
      srvOwn γ i { s with log := s.log.take (prev + j) } ∗ logCouple γ i (s.log.take (prev + j)) ∗
      ⌜s.dur.1 < prev + 1 + j⌝ := by
  apply Inv_upd γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr, Hcc⟩, Ho, Hlc, #Hae⟩
  ihave ⟨Hh, %hae⟩ := H_AEok γ σ s.term prev pt ents lci $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hae
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_open γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  have hi' : i ∈ σ.srvs := by rw [hg.2.1]; exact hi
  have hpre' : truncatePre σ i prev pt ents lci j := ⟨hi', hae, hpre⟩
  obtain ⟨hP', hGr⟩ := truncate_inv σ i prev pt ents lci j hg.1 hpre'
  have hgt := proto.truncate_gt_dur σ i prev pt ents lci j hg.1 hpre'
  have hσ : truncate σ i (prev + 1 + j) =
      { σ with srv := upd σ.srv i { σ.srv i with log := (σ.srv i).log.take (prev + j) } } := by
    unfold truncate; rw [show prev + 1 + j - 1 = prev + j by omega]; rfl
  rw [hσ] at hP' hGr
  ihave ⟨Ht, Hd, Hsv, Hlg, Hc⟩ := (srvG_eq γ i (σ.srv i)).1 $$ Hi
  unfold logCouple
  icases Hlc with ⟨Hlc, #Hv⟩
  imod ghostVar_update_halves ((σ.srv i).log.take (prev + j)) (γ.slog i) _ _ $$ Hlg Hlc
    with ⟨Hlg, Hlc⟩
  imod srvOwn_update γ i (σ.srv i) (σ.srv i) { σ.srv i with log := (σ.srv i).log.take (prev + j) }
    $$ [Ho Hsv] with ⟨Ho, Hsv⟩
  · iframe
  ihave Hi := (srvG_eq γ i { σ.srv i with log := (σ.srv i).log.take (prev + j) }).2
    $$ [Ht Hd Hsv Hlg Hc]
  · iframe
  ihave Hs := Hcl $$ %{ σ.srv i with log := (σ.srv i).log.take (prev + j) } Hi
  imod HistG_grow γ σ _ hg.1 hGr (fun T k e h _ => ⟨T, h⟩) [] (fun _ _ => rfl) [] (fun _ _ => rfl)
    [] (fun _ _ => rfl) [] (fun _ _ => rfl) [] (fun _ _ => rfl) [] (fun _ _ => rfl)
    [] (fun _ _ => rfl) $$ Hh with Hh
  imodintro
  isplitl [Hh Hs Hr Hcc]
  · iapply InvInner_close γ { σ with srv := upd σ.srv i { σ.srv i with log := (σ.srv i).log.take (prev + j) } }
      (upd σ.srv i { σ.srv i with log := (σ.srv i).log.take (prev + j) })
      (σ.maxT + σ.maxI) rfl (Nat.le_refl _) (GInv_step hg hP' hGr hg.2.2.2.2.1)
    iframe
    iapply CcfgG_congr γ σ ({ σ with srv := upd σ.srv i { σ.srv i with log := (σ.srv i).log.take (prev + j) } }) rfl rfl rfl $$ Hcc
  isplitl [Ho]; · iexact Ho
  isplitl [Hlc]; · iframe; iexact Hv
  ipureintro; exact hgt

/-- The truncation point is past the durable prefix (the check before `DeleteRange`). -/
theorem truncate_gt_dur (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState)
    (prev pt : Nat) (ents : RLog) (lci j : Nat)
    (hpre : prevMatch s.log prev pt ∧ matchedUpTo s.log prev ents j ∧ j < ents.length ∧
      prev + 1 + j ≤ s.log.length ∧ termAt s.log (prev + 1 + j) ≠ termAt ents (j + 1)) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ aeValid γ s.term prev pt ents lci ⊢
      |={E}=> srvOwn γ i s ∗ ⌜s.dur.1 < prev + 1 + j⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, Ho, #Hae⟩
  ihave ⟨Hh, %hae⟩ := H_AEok γ σ s.term prev pt ents lci $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hae
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_peek γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  ihave Hs := Hcl $$ Hi
  have hi' : i ∈ σ.srvs := by rw [hg.2.1]; exact hi
  have hgt := proto.truncate_gt_dur σ i prev pt ents lci j hg.1 ⟨hi', hae, hpre⟩
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  iframe; ipureintro; exact hgt

/-- **followerStore** at the log store's `StoreLogs`. -/
theorem followerStore_upd (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState)
    (prev pt : Nat) (ents : RLog) (lci j : Nat)
    (hpre : prevMatch s.log prev pt ∧ matchedUpTo s.log prev ents j ∧ j < ents.length ∧
      s.log.length = prev + j) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ logCouple γ i s.log ∗ aeValid γ s.term prev pt ents lci ⊢
      |={E}=>
      srvOwn γ i { s with log := s.log ++ ents.drop j } ∗ logCouple γ i (s.log ++ ents.drop j) := by
  apply Inv_upd γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr, Hcc⟩, Ho, Hlc, #Hae⟩
  ihave ⟨Hh, %hae⟩ := H_AEok γ σ s.term prev pt ents lci $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hae
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_open γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  have hi' : i ∈ σ.srvs := by rw [hg.2.1]; exact hi
  obtain ⟨hP', hGr⟩ := followerStore_inv σ i prev pt ents lci j hg.1 ⟨hi', hae, hpre⟩
  ihave ⟨Ht, Hd, Hsv, Hlg, Hc⟩ := (srvG_eq γ i (σ.srv i)).1 $$ Hi
  unfold logCouple
  icases Hlc with ⟨Hlc, #Hv⟩
  imod ghostVar_update_halves ((σ.srv i).log ++ ents.drop j) (γ.slog i) _ _ $$ Hlg Hlc
    with ⟨Hlg, Hlc⟩
  imod srvOwn_update γ i (σ.srv i) (σ.srv i) { σ.srv i with log := (σ.srv i).log ++ ents.drop j }
    $$ [Ho Hsv] with ⟨Ho, Hsv⟩
  · iframe
  ihave Hi := (srvG_eq γ i { σ.srv i with log := (σ.srv i).log ++ ents.drop j }).2
    $$ [Ht Hd Hsv Hlg Hc]
  · iframe
  ihave Hs := Hcl $$ %{ σ.srv i with log := (σ.srv i).log ++ ents.drop j } Hi
  imod HistG_grow γ σ _ hg.1 hGr (fun T k e h _ => ⟨T, h⟩) [] (fun _ _ => rfl) [] (fun _ _ => rfl)
    [] (fun _ _ => rfl) [] (fun _ _ => rfl) [] (fun _ _ => rfl) [] (fun _ _ => rfl)
    [] (fun _ _ => rfl) $$ Hh with Hh
  imodintro
  isplitl [Hh Hs Hr Hcc]
  · iapply InvInner_close γ (followerStore σ i (ents.drop j))
      (upd σ.srv i { σ.srv i with log := (σ.srv i).log ++ ents.drop j })
      (σ.maxT + σ.maxI) rfl (Nat.le_refl _) (GInv_step hg hP' hGr hg.2.2.2.2.1)
    iframe
    iapply CcfgG_congr γ σ (followerStore σ i (ents.drop j)) rfl rfl rfl $$ Hcc
  isplitl [Ho]; · iexact Ho
  iframe; iexact Hv

/-- **ack**, follower: after it has every entry of a valid request of its term. -/
theorem ackFollower (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState)
    (prev pt : Nat) (ents : RLog) (lci : Nat)
    (hpre : prevMatch s.log prev pt ∧ matchedUpTo s.log prev ents ents.length) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ aeValid γ s.term prev pt ents lci ⊢ |={E}=>
      srvOwn γ i s ∗ ackIs γ i s.term (prev + ents.length) := by
  apply Inv_upd γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr, Hcc⟩, Ho, #Hae⟩
  ihave ⟨Hh, %hae⟩ := H_AEok γ σ s.term prev pt ents lci $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hae
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_peek γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  ihave Hs := Hcl $$ Hi
  have hi' : i ∈ σ.srvs := by rw [hg.2.1]; exact hi
  have hag := ae_agree σ i prev pt ents lci hg.1 hi' hae hpre.1 hpre.2
  obtain ⟨hP', hGr⟩ := ack_inv σ i (prev + ents.length) hg.1 ⟨hi', hae.1, hag⟩
  have oA : ∀ p, p ∉ [(i, σ.term i, prev + ents.length)] →
      acksF (ack σ i (σ.term i) (prev + ents.length)) p = acksF σ p := by
    intro p hp
    apply acksF_of_iff
    obtain ⟨a, b, d⟩ := p
    simp only [ack]
    constructor
    · intro h
      rcases h with h | h
      · exact h
      · exfalso; apply hp; rw [h.1, h.2.1, h.2.2]; simp
    · exact Or.inl
  imod HistG_grow γ σ _ hg.1 hGr (fun T k e h _ => ⟨T, h⟩) [] (fun _ _ => rfl) [] (fun _ _ => rfl)
    [] (fun _ _ => rfl) [] (fun _ _ => rfl) [] (fun _ _ => rfl)
    [(i, σ.term i, prev + ents.length)] oA [] (fun _ _ => rfl) $$ Hh with Hh
  ihave ⟨Hh, #Hack⟩ := H_ack_get γ (ack σ i (σ.term i) (prev + ents.length)) i (σ.srv i).term
    (prev + ents.length) (Or.inr ⟨rfl, rfl, rfl⟩) $$ Hh
  imodintro
  isplitl [Hh Hs Hr Hcc]
  · iapply InvInner_close γ (ack σ i (σ.term i) (prev + ents.length)) σ.srv (σ.maxT + σ.maxI) rfl (Nat.le_refl _) (GInv_step hg hP' hGr hg.2.2.2.2.1)
    iframe
    iapply CcfgG_congr γ σ (ack σ i (σ.term i) (prev + ents.length)) rfl rfl rfl $$ Hcc
  isplitl [Ho]; · iexact Ho
  iexact Hack

/-- **ack**, leader: its own log (`commitment.match(localID, lastIndex)` in dispatchLogs). -/
theorem ackLeader (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ leaderIs γ s.term i ⊢ |={E}=>
      srvOwn γ i s ∗ ackIs γ i s.term s.log.length := by
  apply Inv_upd γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr, Hcc⟩, Ho, #Hl⟩
  ihave ⟨Hh, %hl⟩ := H_leader_lookup γ σ s.term i $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hl
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_peek γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  ihave Hs := Hcl $$ Hi
  have hi' : i ∈ σ.srvs := by rw [hg.2.1]; exact hi
  have hl' : σ.leader (σ.term i) = some i := hl
  have hLL : σ.log i = σ.llog (σ.term i) := leader_log σ i hg.1 hi' hl'
  have hag : agree (σ.log i) (σ.llog (σ.term i)) (σ.log i).length := by
    rw [← hLL]; exact ⟨Nat.le_refl _, Nat.le_refl _, rfl⟩
  obtain ⟨hP', hGr⟩ := ack_inv σ i (σ.log i).length hg.1 ⟨hi', by rw [hl']; simp, hag⟩
  have oA : ∀ p, p ∉ [(i, σ.term i, (σ.log i).length)] →
      acksF (ack σ i (σ.term i) (σ.log i).length) p = acksF σ p := by
    intro p hp
    apply acksF_of_iff
    obtain ⟨a, b, d⟩ := p
    simp only [ack]
    constructor
    · intro h
      rcases h with h | h
      · exact h
      · exfalso; apply hp; rw [h.1, h.2.1, h.2.2]; simp
    · exact Or.inl
  imod HistG_grow γ σ _ hg.1 hGr (fun T k e h _ => ⟨T, h⟩) [] (fun _ _ => rfl) [] (fun _ _ => rfl)
    [] (fun _ _ => rfl) [] (fun _ _ => rfl) [] (fun _ _ => rfl)
    [(i, σ.term i, (σ.log i).length)] oA [] (fun _ _ => rfl) $$ Hh with Hh
  ihave ⟨Hh, #Hack⟩ := H_ack_get γ (ack σ i (σ.term i) (σ.log i).length) i (σ.srv i).term
    (σ.srv i).log.length (Or.inr ⟨rfl, rfl, rfl⟩) $$ Hh
  imodintro
  isplitl [Hh Hs Hr Hcc]
  · iapply InvInner_close γ (ack σ i (σ.term i) (σ.log i).length) σ.srv (σ.maxT + σ.maxI) rfl (Nat.le_refl _) (GInv_step hg hP' hGr hg.2.2.2.2.1)
    iframe
    iapply CcfgG_congr γ σ (ack σ i (σ.term i) (σ.log i).length) rfl rfl rfl $$ Hcc
  isplitl [Ho]; · iexact Ho
  iexact Hack

/-- **commit** (`commitment.recalculate`): a quorum of the configuration the commitment counts (the
entry `e` at `p` of `llog T`, `ccfgOwn`, stage 4) acknowledged at least `k` entries of term `T`, and
`k` is past the leader's election-time log (an entry of its own term). -/
theorem commit_upd (E : CoPset) (hE : ↑gprotN ⊆ E) (T k n p : Nat) (ℓ : SID) (e : Entry)
    (Q : List SID) (hQ : isQuorumOf (γ.cv e.data) Q) (hk : n < k) :
    Inv (GF := GF) γ ∗ leaderIs γ T ℓ ∗ len0Is γ T n ∗ ccfgOwn γ ℓ T p ∗ llogIdx γ T p e ∗
      ([∗list] j ∈ Q, ∃ m, ackIs γ j T m ∗ ⌜k ≤ m⌝) ⊢ |={E}=>
      ccfgOwn γ ℓ T p ∗ commitIs γ T k p := by
  apply Inv_upd γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr, Hcc⟩, #Hl, #Hn, Hk, #He, #Hacks⟩
  ihave ⟨Hh, %hl⟩ := H_leader_lookup γ σ T ℓ $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hl
  ihave ⟨Hh, %hn⟩ := H_len0_lookup γ σ T n $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hn
  ihave ⟨Hh, %hacks⟩ := H_ack_lookup_list γ σ T k Q $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hacks
  ihave ⟨Hh, %he⟩ := H_llog_lookup γ σ T p e $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact He
  ihave ⟨Hcc, Hk, %hkc⟩ := CcfgG_lookup γ σ ℓ T p $$ [Hcc Hk]
  · iframe
  have hP := hg.1
  have hp : σ.ccfg T = p := hkc.2 hl
  have hn' : σ.len0 T = n := by
    unfold len0F at hn
    split at hn
    · exact Option.some.inj hn
    · cases hn
  have hQ' : isQuorumOf (σ.cv e.data) Q := by rw [hg.2.2.2.1]; exact hQ
  have hQne : Q ≠ [] := by
    intro h; have := hQ.2.2; rw [h] at this; simp at this
  obtain ⟨j0, hj0⟩ := List.exists_mem_of_ne_nil Q hQne
  obtain ⟨m0, hkm, hack0⟩ := hacks j0 hj0
  have hkl : k ≤ (σ.llog T).length := Nat.le_trans hkm ((PInv.acks hP) j0 T m0 hack0).2.2.1
  have hek : e.kind = kConfig := by
    obtain ⟨e', he', hk'⟩ := ccfg_entry hP hl
    rw [hp, he] at he'; cases he'; exact hk'
  have hcm : committed σ T k (σ.ccfg T) := ⟨by rw [hl]; simp, by omega, hkl,
    leader_own_term σ T k ℓ hP hl (by omega) hkl, e, by rw [hp]; exact he, hek, Q, hQ', hacks⟩
  obtain ⟨hP', hGr⟩ := commit_inv σ T k hP hcm
  have oCm : ∀ x, x ∉ [(T, k, p)] → commitsF (commit σ T k) x = commitsF σ x := by
    intro x hx
    apply commitsF_of_iff
    obtain ⟨a, b, d⟩ := x
    simp only [commit]
    constructor
    · intro h
      rcases h with h | h
      · exact h
      · exfalso; apply hx; rw [h.1, h.2.1, h.2.2, hp]; simp
    · exact Or.inl
  imod HistG_grow γ σ _ hP hGr (fun T k e h _ => ⟨T, h⟩) [] (fun _ _ => rfl) [] (fun _ _ => rfl)
    [] (fun _ _ => rfl) [] (fun _ _ => rfl) [] (fun _ _ => rfl)
    [] (fun _ _ => rfl) [(T, k, p)] oCm $$ Hh with Hh
  ihave ⟨Hh, #Hc⟩ := H_commit_get γ (commit σ T k) T k p (Or.inr ⟨rfl, rfl, hp.symm⟩) $$ Hh
  imodintro
  isplitl [Hh Hs Hr Hcc]
  · iapply InvInner_close γ (commit σ T k) σ.srv (σ.maxT + σ.maxI) rfl (Nat.le_refl _) (GInv_step hg hP' hGr hg.2.2.2.2.1)
    iframe
    iapply CcfgG_congr γ σ (commit σ T k) rfl rfl rfl $$ Hcc
  isplitl [Hk]; · iexact Hk
  iexact Hc

/-- **learnCommit**, follower: `idx = min lci v` for `v` up to which it has the request's entries. -/
theorem learnCommitFollower (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState)
    (prev pt : Nat) (ents : RLog) (lci v : Nat)
    (hpre : prevMatch s.log prev pt ∧ matchedUpTo s.log prev ents ents.length ∧
      v ≤ prev + ents.length ∧ 0 < Min.min lci v) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ durView γ i (1 : Qp).half s.dur.1 ∗
      aeValid γ s.term prev pt ents lci ⊢ |={E}=>
      ∃ d, srvOwn γ i { s with dur := d } ∗ durView γ i (1 : Qp).half d.1 ∗
        durLb γ i (Min.min lci v) ∗ ⌜d.1 = Max.max s.dur.1 (Min.min lci v)⌝ := by
  apply Inv_upd γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr, Hcc⟩, Ho, Hdv, #Hae⟩
  ihave ⟨Hh, %hae⟩ := H_AEok γ σ s.term prev pt ents lci $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hae
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_open γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  have hi' : i ∈ σ.srvs := by rw [hg.2.1]; exact hi
  have hP := hg.1
  have hag := ae_agree σ i prev pt ents lci hP hi' hae hpre.1 hpre.2.1
  have hagv := agree_mono hag hpre.2.2.1
  obtain ⟨T', hlc⟩ := ae_learn σ i prev pt ents lci v hP hi' hae hagv hpre.2.2.2
  obtain ⟨hP', hGr⟩ := learnCommit_inv σ i (Min.min lci v) T' hP hlc
  obtain ⟨d, hd⟩ : ∃ d : Nat × Nat, d = (if (σ.srv i).dur.1 < Min.min lci v then (Min.min lci v, T')
      else (σ.srv i).dur) := ⟨_, rfl⟩
  have hd1 : (σ.srv i).dur.1 ≤ d.1 := by rw [hd]; split <;> (try dsimp only) <;> omega
  have hd2 : Min.min lci v ≤ d.1 := by rw [hd]; split <;> (try dsimp only) <;> omega
  have hdm : d.1 = Max.max (σ.srv i).dur.1 (Min.min lci v) := by rw [hd]; split <;> (try dsimp only) <;> omega
  have hsrv : (learnCommit σ i (Min.min lci v) T').srv = upd σ.srv i { σ.srv i with dur := d } := by
    rw [hd]; rfl
  ihave ⟨Ht, Hd, Hsv, Hlg, Hc⟩ := (srvG_eq γ i (σ.srv i)).1 $$ Hi
  unfold durView durLb
  imod monoNat_update_halves (γ.dur i) (σ.srv i).dur.1 (σ.srv i).dur.1 d.1 hd1 $$ [Hd Hdv]
    with ⟨Hd, Hdv, #Hlb⟩
  · iframe
  ihave #Hlb2 := monoNatLbOwn_le (Min.min lci v) hd2 $$ Hlb
  imod srvOwn_update γ i (σ.srv i) (σ.srv i) { σ.srv i with dur := d } $$ [Ho Hsv] with ⟨Ho, Hsv⟩
  · iframe
  ihave Hi := (srvG_eq γ i { σ.srv i with dur := d }).2 $$ [Ht Hd Hsv Hlg Hc]
  · iframe
  ihave Hs := Hcl $$ %{ σ.srv i with dur := d } Hi
  imod HistG_grow γ σ _ hP hGr (fun T k e h _ => ⟨T, h⟩) [] (fun _ _ => rfl) [] (fun _ _ => rfl)
    [] (fun _ _ => rfl) [] (fun _ _ => rfl) [] (fun _ _ => rfl) [] (fun _ _ => rfl)
    [] (fun _ _ => rfl) $$ Hh with Hh
  imodintro
  isplitl [Hh Hs Hr Hcc]
  · iapply InvInner_close γ (learnCommit σ i (Min.min lci v) T') (upd σ.srv i { σ.srv i with dur := d }) (σ.maxT + σ.maxI) hsrv
      (Nat.le_refl _) (GInv_step hg hP' hGr hg.2.2.2.2.1)
    iframe
    iapply CcfgG_congr γ σ (learnCommit σ i (Min.min lci v) T') rfl rfl rfl $$ Hcc
  iexists d
  isplitl [Ho]; · iexact Ho
  isplitl [Hdv]; · iexact Hdv
  isplitr; · iexact Hlb2
  ipureintro; exact hdm

/-- **learnCommit**, leader: a recorded commit of its own term. (Stage 2) The leader publishes `k`
first (`proto.publish`, leaderLoop's `commitCh` case, before `setCommitIndex(k)`): it gets
`pubIs` and its publications' bound grows to `k`. (Stage 3) The recorded commit may be at any `k' ≥ k`: the
commitment's index is covered by a recorded commit of `T` (an acknowledging quorum, or an install
counted by the commitment, `commit_or_snap`). -/
theorem learnCommitLeader (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState) (k k' p m : Nat)
    (hk : k ≤ k') :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ durView γ i (1 : Qp).half s.dur.1 ∗
      leaderIs γ s.term i ∗ commitIs γ s.term k' p ∗ pubOwn γ i s.term m ⊢ |={E}=>
      ∃ d, srvOwn γ i { s with dur := d } ∗ durView γ i (1 : Qp).half d.1 ∗ durLb γ i k ∗
        pubOwn γ i s.term (Max.max m k) ∗ pubIs γ s.term k ∗
        ⌜d.1 = Max.max s.dur.1 k⌝ := by
  apply Inv_upd γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr, Hcc⟩, Ho, Hdv, #Hl, #Hcm, Hpo⟩
  ihave ⟨Hh, %hl⟩ := H_leader_lookup γ σ s.term i $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hl
  ihave ⟨Hh, %hcm⟩ := H_commit_lookup γ σ s.term k' p $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hcm
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_open γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  have hi' : i ∈ σ.srvs := by rw [hg.2.1]; exact hi
  have hP := hg.1
  have hl' : σ.leader (σ.term i) = some i := hl
  have hLL : σ.log i = σ.llog (σ.term i) := leader_log σ i hP hi' hl'
  have hkl : k ≤ (σ.llog (σ.term i)).length :=
    Nat.le_trans hk ((PInv.commits hP).1 _ k' p hcm).1.2.2.1
  have hag : agree (σ.log i) (σ.llog (σ.term i)) k := by
    rw [← hLL]; rw [← hLL] at hkl; exact ⟨hkl, hkl, rfl⟩
  have hpp : publishPre σ i k := ⟨hi', hl', k', p, hk, hcm⟩
  obtain ⟨hP1, hG1⟩ := publish_inv σ i k hP hpp
  have hlc : learnCommitPre (publish σ (σ.term i) k) i k (σ.term i) :=
    ⟨hi', Nat.le_refl _, ⟨k', p, hk, hcm⟩, hag, σ.term i, k, Nat.le_refl _, Nat.le_refl _,
      Or.inr ⟨rfl, rfl⟩⟩
  obtain ⟨hP', hG2⟩ := learnCommit_inv (publish σ (σ.term i) k) i k (σ.term i) hP1 hlc
  have hGr := grows_trans hG1 hG2
  obtain ⟨d, hd⟩ : ∃ d : Nat × Nat, d = (if (σ.srv i).dur.1 < k then (k, σ.term i)
      else (σ.srv i).dur) := ⟨_, rfl⟩
  have hd1 : (σ.srv i).dur.1 ≤ d.1 := by rw [hd]; split <;> (try dsimp only) <;> omega
  have hd2 : k ≤ d.1 := by rw [hd]; split <;> (try dsimp only) <;> omega
  have hdm : d.1 = Max.max (σ.srv i).dur.1 k := by rw [hd]; split <;> (try dsimp only) <;> omega
  have hsrv : (learnCommit (publish σ (σ.term i) k) i k (σ.term i)).srv =
      upd σ.srv i { σ.srv i with dur := d } := by
    rw [hd]; rfl
  have hsubP : ∀ p v, pubsF σ p = some v →
      pubsF (learnCommit (publish σ (σ.term i) k) i k (σ.term i)) p = some v := by
    intro ⟨a, b⟩ v h
    cases v
    exact (pubsF_iff _ a b).2 (Or.inl ((pubsF_iff σ a b).1 h))
  have houtP : ∀ p, p ∉ [((σ.srv i).term, k)] →
      pubsF (learnCommit (publish σ (σ.term i) k) i k (σ.term i)) p = pubsF σ p := by
    intro ⟨a, b⟩ hp
    have hiff : (learnCommit (publish σ (σ.term i) k) i k (σ.term i)).pubs a b ↔ σ.pubs a b := by
      refine ⟨fun h => ?_, Or.inl⟩
      rcases h with h | ⟨rfl, rfl⟩
      · exact h
      · exact absurd (by simp [PState.term]) hp
    cases h2 : pubsF σ (a, b) with
    | none =>
      cases h3 : pubsF (learnCommit (publish σ (σ.term i) k) i k (σ.term i)) (a, b) with
      | none => rfl
      | some u =>
        cases u
        rw [(pubsF_iff σ a b).2 (hiff.1 ((pubsF_iff _ a b).1 h3))] at h2; cases h2
    | some u =>
      cases u
      exact (pubsF_iff _ a b).2 (hiff.2 ((pubsF_iff σ a b).1 h2))
  ihave ⟨Ht, Hd, Hsv, Hlg, Hc⟩ := (srvG_eq γ i (σ.srv i)).1 $$ Hi
  unfold durView durLb
  imod monoNat_update_halves (γ.dur i) (σ.srv i).dur.1 (σ.srv i).dur.1 d.1 hd1 $$ [Hd Hdv]
    with ⟨Hd, Hdv, #Hlb⟩
  · iframe
  ihave #Hlb2 := monoNatLbOwn_le k hd2 $$ Hlb
  imod srvOwn_update γ i (σ.srv i) (σ.srv i) { σ.srv i with dur := d } $$ [Ho Hsv] with ⟨Ho, Hsv⟩
  · iframe
  ihave Hi := (srvG_eq γ i { σ.srv i with dur := d }).2 $$ [Ht Hd Hsv Hlg Hc]
  · iframe
  ihave Hs := Hcl $$ %{ σ.srv i with dur := d } Hi
  imod HistG_grow_with γ σ (learnCommit (publish σ (σ.term i) k) i k (σ.term i)) hP hGr
    (fun T k e h _ => ⟨T, h⟩) [] (fun _ _ => rfl) [] (fun _ _ => rfl)
    [] (fun _ _ => rfl) [] (fun _ _ => rfl) [] (fun _ _ => rfl) [] (fun _ _ => rfl)
    [] (fun _ _ => rfl) (pubOwn γ i (σ.srv i).term m) (pubOwn γ i (σ.srv i).term (Max.max m k))
    (by iintro ⟨Hp, H, Hk⟩
        imod GMapOf_grow γ.pubs [((σ.srv i).term, k)] (pubsF σ) _ hsubP houtP $$ Hp with Hp
        imod PubMaxG_publish γ σ (learnCommit (publish σ (σ.term i) k) i k (σ.term i)) i
          (σ.srv i).term k m hGr hl (fun T' k' => Iff.rfl) (fun _ _ h => h) $$ [H Hk] with ⟨H, Hk⟩
        · isplitl [H]; iexact H; iexact Hk
        imodintro
        isplitl [Hp]; · iexact Hp
        isplitl [H]; · iexact H
        iexact Hk) $$ [Hh Hpo] with ⟨Hh, Hpo⟩
  · isplitl [Hh]; iexact Hh; iexact Hpo
  ihave ⟨Hh, #Hpub⟩ := H_pub_get γ (learnCommit (publish σ (σ.term i) k) i k (σ.term i))
    (σ.srv i).term k (Or.inr ⟨rfl, rfl⟩) $$ Hh
  imodintro
  isplitl [Hh Hs Hr Hcc]
  · iapply InvInner_close γ (learnCommit (publish σ (σ.term i) k) i k (σ.term i))
      (upd σ.srv i { σ.srv i with dur := d }) (σ.maxT + σ.maxI) hsrv
      (Nat.le_refl _) (GInv_step hg hP' hGr hg.2.2.2.2.1)
    iframe
    iapply CcfgG_congr γ σ (learnCommit (publish σ (σ.term i) k) i k (σ.term i)) rfl rfl rfl $$ Hcc
  iexists d
  isplitl [Ho]; · iexact Ho
  isplitl [Hdv]; · iexact Hdv
  isplitr; · iexact Hlb2
  isplitl [Hpo]; · iexact Hpo
  isplitr; · iexact Hpub
  ipureintro; exact hdm
/-- **setCidx** at the `commitIndex` atomic store. -/
theorem setCidx_upd (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState) (c : Nat)
    (hc : c ≤ s.dur.1) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ cidxCouple γ i s.cidx ⊢ |={E}=>
      srvOwn γ i { s with cidx := c } ∗ cidxCouple γ i c := by
  apply Inv_upd γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr, Hcg⟩, Ho, Hcc⟩
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_open γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  have hi' : i ∈ σ.srvs := by rw [hg.2.1]; exact hi
  obtain ⟨hP', hGr⟩ := setCidx_inv σ i c hg.1 ⟨hi', hc⟩
  ihave ⟨Ht, Hd, Hsv, Hlg, Hc⟩ := (srvG_eq γ i (σ.srv i)).1 $$ Hi
  unfold cidxCouple
  imod ghostVar_update_halves c (γ.cidx i) _ _ $$ Hc Hcc with ⟨Hc, Hcc⟩
  imod srvOwn_update γ i (σ.srv i) (σ.srv i) { σ.srv i with cidx := c } $$ [Ho Hsv]
    with ⟨Ho, Hsv⟩
  · iframe
  ihave Hi := (srvG_eq γ i { σ.srv i with cidx := c }).2 $$ [Ht Hd Hsv Hlg Hc]
  · iframe
  ihave Hs := Hcl $$ %{ σ.srv i with cidx := c } Hi
  imod HistG_grow γ σ _ hg.1 hGr (fun T k e h _ => ⟨T, h⟩) [] (fun _ _ => rfl) [] (fun _ _ => rfl)
    [] (fun _ _ => rfl) [] (fun _ _ => rfl) [] (fun _ _ => rfl) [] (fun _ _ => rfl)
    [] (fun _ _ => rfl) $$ Hh with Hh
  imodintro
  isplitl [Hh Hs Hr Hcg]
  · iapply InvInner_close γ (setCidx σ i c) (upd σ.srv i { σ.srv i with cidx := c }) (σ.maxT + σ.maxI) rfl
      (Nat.le_refl _) (GInv_step hg hP' hGr hg.2.2.2.2.1)
    iframe
    iapply CcfgG_congr γ σ (setCidx σ i c) rfl rfl rfl $$ Hcg
  isplitl [Ho]; · iexact Ho
  iexact Hcc

/-! ## Reader laws (the replication goroutine of leader `i` of term `T`) -/

/-- Reading entry `k` of `i`'s log (inside the log store's atomic read): it is `llog T`'s entry,
or `i` has already left term `T`. -/
theorem readLog_repl (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (T k : Nat) (L : RLog) (e : Entry)
    (he : ent L k = some e) :
    Inv (GF := GF) γ ∗ logCouple γ i L ∗ leaderIs γ T i ∗ termLb γ i T ⊢ |={E}=>
      logCouple γ i L ∗ (llogIdx γ T k e ∨ termLb γ i (T + 1)) := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, Hlc, #Hl, #Hlb⟩
  ihave ⟨Hh, %hl⟩ := H_leader_lookup γ σ T i $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hl
  have hP := hg.1
  have hi' : i ∈ σ.srvs := ((PInv.leaders hP).1 T i hl).1
  have hi : i ∈ γ.srvs := by rw [← hg.2.1]; exact hi'
  ihave ⟨Hi, Hcl⟩ := srvs_peek γ σ i hi $$ Hs
  ihave ⟨Hi, Hlc, %hL⟩ := srvG_log_agree γ i (σ.srv i) L $$ [Hi Hlc]
  · iframe
  ihave ⟨Hi, %hT⟩ := srvG_term_lb γ i (σ.srv i) T $$ [Hi]
  · isplitl [Hi]; iexact Hi; iexact Hlb
  ihave ⟨Hi, #Hlb2⟩ := srvG_term_get_lb γ i (σ.srv i) $$ Hi
  ihave Hs := Hcl $$ Hi
  subst hL
  by_cases hTe : (σ.srv i).term = T
  · have hl' : σ.leader (σ.term i) = some i := by
      show σ.leader (σ.srv i).term = _; rw [hTe]; exact hl
    have hLL : σ.log i = σ.llog (σ.term i) := leader_log σ i hP hi' hl'
    have hLT : (σ.srv i).log = σ.llog T := by rw [← hTe]; exact hLL
    have he' : ent (σ.llog T) k = some e := by rw [← hLT]; exact he
    ihave ⟨Hh, #Hle⟩ := H_llog_get γ σ T k e he' $$ Hh
    isplitl [Hh Hs Hr]
    · iframe; ipureintro; exact hg
    isplitl [Hlc]; · iexact Hlc
    ileft; iexact Hle
  · isplitl [Hh Hs Hr]
    · iframe; ipureintro; exact hg
    isplitl [Hlc]; · iexact Hlc
    iright
    iapply termLb_mono γ i (σ.srv i).term (T + 1) (by omega) $$ Hlb2

/-- Reading `i`'s `commitIndex` (at the atomic load): it may be sent in term `T`, or `i` has
already left term `T`. -/
theorem readCidx_repl (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (T c : Nat) :
    Inv (GF := GF) γ ∗ cidxCouple γ i c ∗ leaderIs γ T i ∗ termLb γ i T ⊢ |={E}=>
      cidxCouple γ i c ∗ (lciOk γ T c ∨ termLb γ i (T + 1)) := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, Hcc, #Hl, #Hlb⟩
  ihave ⟨Hh, %hl⟩ := H_leader_lookup γ σ T i $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hl
  have hP := hg.1
  have hi' : i ∈ σ.srvs := ((PInv.leaders hP).1 T i hl).1
  have hi : i ∈ γ.srvs := by rw [← hg.2.1]; exact hi'
  ihave ⟨Hi, Hcl⟩ := srvs_peek γ σ i hi $$ Hs
  ihave ⟨Hi, Hcc, %hc⟩ := srvG_cidx_agree γ i (σ.srv i) c $$ [Hi Hcc]
  · iframe
  ihave ⟨Hi, %hT⟩ := srvG_term_lb γ i (σ.srv i) T $$ [Hi]
  · isplitl [Hi]; iexact Hi; iexact Hlb
  ihave ⟨Hi, #Hlb2⟩ := srvG_term_get_lb γ i (σ.srv i) $$ Hi
  ihave Hs := Hcl $$ Hi
  subst hc
  by_cases hTe : (σ.srv i).term = T
  · have hl' : σ.leader (σ.term i) = some i := by
      show σ.leader (σ.srv i).term = _; rw [hTe]; exact hl
    have hlci := leader_lci σ i (σ.srv i).cidx hP hi' hl' (Nat.le_refl _)
    have hpub : (σ.srv i).cidx = 0 ∨
        ∃ T0 k0, T0 ≤ T ∧ (σ.srv i).cidx ≤ k0 ∧ σ.pubs T0 k0 := by
      have hcx := ((PInv.dur hP) i hi').2
      rcases hP.2.2.2.2.2.2.2.2.2.2.2.2.1.2 i hi' with h0 | ⟨T0, k0, a, b, c⟩
      · left; omega
      · right; exact ⟨T0, k0, by rw [← hTe]; exact a, by omega, c⟩
    rcases hpub with h0 | ⟨T0, k0, hT0, hk0, hpb⟩
    · isplitl [Hh Hs Hr]
      · iframe; ipureintro; exact hg
      isplitl [Hcc]; · iexact Hcc
      ileft; unfold lciOk; ileft; ipureintro; exact h0
    rcases hlci with h0 | ⟨T', k', p', hT', hk', hcm, hag⟩
    · isplitl [Hh Hs Hr]
      · iframe; ipureintro; exact hg
      isplitl [Hcc]; · iexact Hcc
      ileft; unfold lciOk; ileft; ipureintro; exact h0
    · have hag' : agree (σ.llog T) (σ.llog T') (σ.srv i).cidx := by rw [← hTe]; exact hag
      have hT'' : T' ≤ T := by rw [← hTe]; exact hT'
      ihave ⟨Hh, #Hcm⟩ := H_commit_get γ σ T' k' p' hcm $$ Hh
      ihave ⟨Hh, #Hpb⟩ := H_pub_get γ σ T0 k0 hpb $$ Hh
      ihave ⟨Hh, #Hes1⟩ := H_llog_get_list γ σ T ((σ.llog T).take (σ.srv i).cidx)
        (fun j => j + 1) (by
          intro j e hj
          rw [ent_succ]; rw [List.getElem?_take] at hj
          split at hj
          · exact hj
          · cases hj) $$ Hh
      ihave ⟨Hh, #Hes2⟩ := H_llog_get_list γ σ T' ((σ.llog T).take (σ.srv i).cidx)
        (fun j => j + 1) (by
          intro j e hj
          rw [ent_succ]; rw [hag'.2.2, List.getElem?_take] at hj
          split at hj
          · exact hj
          · cases hj) $$ Hh
      isplitl [Hh Hs Hr]
      · iframe; ipureintro; exact hg
      isplitl [Hcc]; · iexact Hcc
      ileft; unfold lciOk; iright
      isplitr
      · iexists T', k', p', ((σ.llog T).take (σ.srv i).cidx)
        isplitr
        · ipureintro
          have := hag'.1
          refine ⟨hT'', hk', ?_⟩
          rw [List.length_take]; omega
        isplitr; · iexact Hcm
        iapply BigSepL.bigSepL_sep_eqv.2
        isplitr; · iexact Hes1
        iexact Hes2
      · iexists T0, k0
        isplitr; · ipureintro; exact ⟨hT0, hk0⟩
        iexact Hpb
  · isplitl [Hh Hs Hr]
    · iframe; ipureintro; exact hg
    isplitl [Hcc]; · iexact Hcc
    iright
    iapply termLb_mono γ i (σ.srv i).term (T + 1) (by omega) $$ Hlb2

/-- **No leader of term 0** (stage 2, HR3-1; `IGen`: `σ.leader 0 = none`). -/
theorem leaderIs_pos (E : CoPset) (hE : ↑gprotN ⊆ E) (T : Nat) (ℓ : SID) :
    Inv (GF := GF) γ ∗ leaderIs γ T ℓ ⊢ |={E}=> ⌜1 ≤ T⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, #Hl⟩
  ihave ⟨Hh, %hl⟩ := H_leader_lookup γ σ T ℓ $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hl
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  ipureintro
  apply Nat.pos_of_ne_zero
  intro h0
  subst h0
  rw [(PInv.gen hg.1).2.2.2.2.2.2.1] at hl
  cases hl

/-- **A recorded commit of `T` is past `T`'s election-time log** (stage 2, MAINL-4): its last
entry is of term `T` (`committed`), the first `len0 T` entries of `llog T` are of earlier terms
(`ILeaders`). -/
theorem commitIs_len0 (E : CoPset) (hE : ↑gprotN ⊆ E) (T k p n0 : Nat) :
    Inv (GF := GF) γ ∗ commitIs γ T k p ∗ len0Is γ T n0 ⊢ |={E}=> ⌜n0 < k⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, #Hc, #Hn⟩
  ihave ⟨Hh, %hc⟩ := H_commit_lookup γ σ T k p $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hc
  ihave ⟨Hh, %hn⟩ := H_len0_lookup γ σ T n0 $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hn
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  ipureintro
  obtain ⟨hl, hk1, hkl, hkt, _⟩ := ((PInv.commits hg.1).1 T k p hc).1
  obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp hl
  have hn0 : σ.len0 T = n0 := by
    unfold len0F at hn; rw [if_pos (Or.inl hl)] at hn; cases hn; rfl
  have hel := (PInv.leaders hg.1).1 T ℓ hℓ
  apply Classical.byContradiction
  intro hc'
  have := hel.2.2.2.2.2.1 k hk1 (by omega)
  omega

/-- **A publication of `T` is within the bound of `T`'s leader** (stage 2, MAINL-5; `PubMaxG`). -/
theorem pubIs_le (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (T k m : Nat) :
    Inv (GF := GF) γ ∗ leaderIs γ T i ∗ pubIs γ T k ∗ pubOwn γ i T m ⊢ |={E}=>
      pubOwn γ i T m ∗ ⌜k ≤ m⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, #Hl, #Hp, Hpo⟩
  ihave ⟨Hh, %hl⟩ := H_leader_lookup γ σ T i $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hl
  ihave ⟨Hh, %hp⟩ := H_pub_lookup γ σ T k $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hp
  ihave ⟨Hh, Hpo, %hb⟩ := H_pubOwn_bound γ σ i T m $$ [Hh Hpo]
  · isplitl [Hh]; iexact Hh; iexact Hpo
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  isplitl [Hpo]; · iexact Hpo
  ipureintro; exact hb k hp hl

/-! ## Election safety -/

/-- **Election safety** (stage 2, MF1): a quorum `Q` of votes for `c` in `T` and a leader `ℓ` of
`T` give `ℓ = c` (`ILeaders`: the leader had a quorum of votes; one vote per voter and term).
(Stage 4) `Q` is a quorum of the latest configuration of `c`'s election log `L` (review T1-4: a
persistent description, `llogPre γ lt L`, so the law holds after the candidate's log changed within
`T`: `llogPre_srv` at `electSelf`), whose last entry `c` recorded for its election of `T`
(`candIs`); the two election configurations' quorums meet (`proto.elect_safety`, through
`proto.CL0`). (Interface stage 4 before the review: `srvOwn γ c s` with `candIs γ c T |s.log|
(lastTerm s.log)` and the quorum of `cfgOfC γ.cv s.log`.) -/
theorem leader_votes_agree (E : CoPset) (hE : ↑gprotN ⊆ E) (ℓ c : SID) (T li lt : Nat) (L : RLog)
    (Q : List SID) (hL : L.length = li ∧ lastTerm L = lt) (hQ : isQuorumOf (cfgOfC γ.cv L) Q) :
    Inv (GF := GF) γ ∗ candIs γ c T li lt ∗ llogPre γ lt L ∗
      leaderIs γ T ℓ ∗ ([∗list] j ∈ Q, voteIs γ j T c) ⊢ |={E}=> ⌜ℓ = c⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, #Hc, #Hp, #Hl, #Hvs⟩
  ihave ⟨Hh, %hl⟩ := H_leader_lookup γ σ T ℓ $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hl
  ihave ⟨Hh, %hvs⟩ := H_vote_lookup_list γ σ T c Q $$ [Hh Hvs]
  · isplitl [Hh]; iexact Hh; iexact Hvs
  ihave ⟨Hh, %hc⟩ := H_cand_lookup γ σ c T li lt $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hc
  ihave ⟨Hh, %hp⟩ := H_llogPre_lookup γ σ lt L $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hp
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  ipureintro
  have hP := hg.1
  have hQ' : isQuorumOf (cfgOf σ L) Q := by
    show isQuorumOf (cfgOfC σ.cv L) Q
    rw [hg.2.2.2.1]; exact hQ
  have hLM : LMok σ L := by
    rw [hp]; exact LMok_take ((PInv.logs hP).2.1 lt) _
  have hc' : σ.cand c T = some (L.length, lastTerm L) := by rw [hL.1, hL.2]; exact hc
  exact elect_safety σ hP T ℓ c L Q hl hLM hc' hQ'
    (fun j hj => by obtain ⟨L', b, h⟩ := hvs j hj; exact ⟨L', b, h⟩)

/-! ## Consequences for the checks -/

/-- State-machine safety: an entry of the durable prefix is the committed log's entry. -/
theorem applied_C (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState) (x : Nat) (e : Entry)
    (hx : 1 ≤ x ∧ x ≤ s.dur.1) (he : ent s.log x = some e) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ⊢ |={E}=> srvOwn γ i s ∗ CIdx γ x e := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, Ho⟩
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_peek γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  ihave Hs := Hcl $$ Hi
  have hi' : i ∈ σ.srvs := by rw [hg.2.1]; exact hi
  have hC := (dur_C σ i x hg.1 hi' hx.1 hx.2).2
  have hCe : ent σ.C x = some e := by rw [hC]; exact he
  ihave ⟨Hh, #Hc⟩ := H_C_get γ σ x e hCe $$ Hh
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  isplitl [Ho]; · iexact Ho
  iexact Hc

/-- An entry of the committed log is its term's leader log entry. -/
theorem CIdx_llog (E : CoPset) (hE : ↑gprotN ⊆ E) (x : Nat) (e : Entry) :
    Inv (GF := GF) γ ∗ CIdx γ x e ⊢ |={E}=> llogIdx γ e.term x e := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, #Hc⟩
  ihave ⟨Hh, %hC⟩ := H_C_lookup γ σ x e $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hc
  ihave ⟨Hh, #Hl⟩ := H_llog_get γ σ e.term x e (C_llog σ x e hg.1 hC) $$ Hh
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  iexact Hl

/-- A leader of its current term: its log is the leader log (so no entry of its term lies past
its log). -/
theorem llogIdx_leader (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState) (k : Nat)
    (e : Entry) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ leaderIs γ s.term i ∗ llogIdx γ s.term k e ⊢ |={E}=>
      srvOwn γ i s ∗ ⌜ent s.log k = some e⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, Ho, #Hl, #He⟩
  ihave ⟨Hh, %hl⟩ := H_leader_lookup γ σ s.term i $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hl
  ihave ⟨Hh, %he⟩ := H_llog_lookup γ σ s.term k e $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact He
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_peek γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  ihave Hs := Hcl $$ Hi
  have hi' : i ∈ σ.srvs := by rw [hg.2.1]; exact hi
  have hLL : σ.log i = σ.llog (σ.term i) := leader_log σ i hg.1 hi' hl
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  isplitl [Ho]; · iexact Ho
  ipureintro
  show ent (σ.log i) k = some e
  rw [hLL]; exact he

/-- The committed log, as a lower bound (a snapshot). -/
theorem CLb_get (E : CoPset) (hE : ↑gprotN ⊆ E) :
    Inv (GF := GF) γ ⊢ |={E}=> ∃ L, CLb γ L := by
  apply Inv_read0 γ E hE
  intro σ
  unfold InvBody
  iintro ⟨%hg, Hh, Hs, Hr⟩
  ihave ⟨Hh, #Hc⟩ := H_C_lb γ σ $$ Hh
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  iexists σ.C; iexact Hc

theorem CLb_idx (L : RLog) (k : Nat) (e : Entry) (h : ent L k = some e) :
    CLb (GF := GF) γ L ⊢ CIdx γ k e := by
  unfold CLb CIdx
  iintro #H
  have hk := ent_pos h
  isplitr
  · ipureintro; exact hk
  · iapply monoListIdxOwn_get (k - 1) e (by rw [← ent_eq_getElem? _ _ hk]; exact h) $$ H

/-! ## Allocation -/

/-- The bootstrapped protocol (stage 4): the servers `srvs`; the bootstrap voters `cv g.data` (a
valid configuration over `srvs`) with log `[g]`, term 1; the other servers with the empty log,
term 0 (`proto.initSrv`). Needs two receipts (`maxT = maxI = 1`). -/
theorem alloc (E : CoPset) (srvs : List SID) (g : Entry) (cv : List w8 → List SID)
    (hnd : srvs.Nodup) (hg1 : g.term = 1) (hgk : g.kind = kConfig)
    (hcv : cfgValid srvs (cv g.data)) (hne : ∀ j ∈ srvs, j ≠ []) :
    receipt (GF := GF) 2 ⊢ |={E}=> ∃ γ : GNames, ⌜γ.srvs = srvs ∧ γ.g = g ∧ γ.cv = cv⌝ ∗ Inv γ ∗
      opsAuth γ ∅ ∗
      [∗list] i ∈ srvs, isSrv γ i ∗
        srvOwn γ i (initSrv cv g i) ∗ durView γ i (1 : Qp).half 0 ∗
        termCouple γ i (initSrv cv g i).term ∗ logCouple γ i (initSrv cv g i).log ∗
        cidxCouple γ i 0 := by
  have oLl : ∀ p, p ∉ [((1 : Nat), (1 : Nat))] → llogF (init srvs g cv) p = none := by
    intro ⟨T, k⟩ hp
    simp only [llogF, init]
    by_cases hT : T = 1
    · rw [if_pos hT]
      have hk : k ≠ 1 := fun hk => hp (by simp [hT, hk])
      unfold ent; split
      · rfl
      · exact List.getElem?_eq_none (by simp; omega)
    · rw [if_neg hT]; unfold ent; split <;> simp
  have oL0 : ∀ T, T ∉ [(1 : Nat)] → len0F (init srvs g cv) T = none := by
    intro T hT
    simp only [List.mem_singleton] at hT
    simp [len0F, init, hT]
  have oA : ∀ p, p ∉ ([] : List (SID × Nat × Nat)) → acksF (init srvs g cv) p = none := by
    intro p _; simp [acksF, init]
  have oCm : ∀ p, p ∉ ([] : List (Nat × Nat × Nat)) → commitsF (init srvs g cv) p = none := by
    intro p _; simp [commitsF, init]
  have oVs : ∀ i, i ∉ srvs → srvsF (init srvs g cv) i = none := by
    intro i hi; unfold srvsF; exact if_neg hi
  iintro Hr
  imod GMapOf_alloc (GF := GF) (K := Nat) (V := SID) with ⟨%γL, HL⟩
  imod GMapOf_alloc (GF := GF) (K := Nat × Nat) (V := Entry) with ⟨%γLl, HLl⟩
  imod GMapOf_grow γLl [((1 : Nat), (1 : Nat))] (fun _ => none) (llogF (init srvs g cv))
    (fun _ _ h => by cases h) oLl $$ HLl with HLl
  imod GMapOf_alloc (GF := GF) (K := Nat) (V := Nat) with ⟨%γL0, HL0⟩
  imod GMapOf_grow γL0 [(1 : Nat)] (fun _ => none) (len0F (init srvs g cv))
    (fun _ _ h => by cases h) oL0 $$ HL0 with HL0
  imod GMapOf_alloc (GF := GF) (K := SID × Nat) (V := Nat × Nat) with ⟨%γC, HC⟩
  imod GMapOf_alloc (GF := GF) (K := SID × Nat) (V := SID × RLog × Bool) with ⟨%γV, HV⟩
  imod GMapOf_alloc (GF := GF) (K := SID × Nat × Nat) (V := Unit) with ⟨%γA, HA⟩
  imod GMapOf_grow γA [] (fun _ => none) (acksF (init srvs g cv))
    (fun _ _ h => by cases h) oA $$ HA with HA
  imod GMapOf_alloc (GF := GF) (K := Nat × Nat × Nat) (V := Unit) with ⟨%γCm, HCm⟩
  imod GMapOf_grow γCm [] (fun _ => none) (commitsF (init srvs g cv))
    (fun _ _ h => by cases h) oCm $$ HCm with HCm
  imod GMapOf_alloc (GF := GF) (K := SID) (V := Unit) with ⟨%γVs, HVs⟩
  imod GMapOf_grow γVs srvs (fun _ => none) (srvsF (init srvs g cv))
    (fun _ _ h => by cases h) oVs $$ HVs with HVs
  imod mono_list_own_alloc (GF := GF) ([] : List Entry) with ⟨%γCC, HCC, -⟩
  imod alloc_srvs (GF := GF) (initSrv cv g) srvs hnd with ⟨%N, HN⟩
  ihave HN := bigSepL_congr_mem srvs (fun i => fullG (GF := GF) (initSrv cv g i) (N i))
    (fun i => fullG (GF := GF) (initSrv cv g i) ((N i).1, (N i).2.1, (N i).2.2.1, (N i).2.2.2.1, (N i).2.2.2.2))
    (fun _ _ => rfl) $$ HN
  ihave HL := GMapOf_congr γL (fun (_ : Nat) => (none : Option SID)) (init srvs g cv).leader (fun _ => rfl) $$ HL
  ihave HC := GMapOf_congr γC (fun (_ : SID × Nat) => (none : Option (Nat × Nat))) (candF (init srvs g cv)) (fun _ => rfl) $$ HC
  ihave HV := GMapOf_congr γV (fun (_ : SID × Nat) => (none : Option (SID × RLog × Bool))) (votesF (init srvs g cv)) (fun _ => rfl) $$ HV
  imod ghost_map_alloc_empty (GF := GF) (K := List w8) (V := Nat) with ⟨%γops, Hops⟩
  imod GMapOf_alloc (GF := GF) (K := Nat × Nat) (V := Unit) with ⟨%γP, HP⟩
  ihave HP := GMapOf_congr γP (fun _ => none) (pubsF (init srvs g cv))
    (fun p => by simp [pubsF, init]) $$ HP
  imod ghost_map_alloc_empty (GF := GF) (K := SID × Nat) (V := Nat) with ⟨%γPM, HPM⟩
  imod mono_list_own_alloc (GF := GF) ([] : List Snap) with ⟨%γH, HH, -⟩
  imod ghost_map_alloc_empty (GF := GF) (K := SID × Nat) (V := Nat) with ⟨%γCF, HCF⟩
  iexists (GNames.mk srvs cv g γL γLl γL0 γC γV γA γCm γCC γVs (fun i => (N i).1)
    (fun i => (N i).2.1) (fun i => (N i).2.2.1) (fun i => (N i).2.2.2.1) (fun i => (N i).2.2.2.2)
    γops γP γPM γH γCF)
  isplitr; · ipureintro; exact ⟨rfl, rfl, rfl⟩
  have hinit : ∀ T k e, ent ((init srvs g cv).llog T) k = some e → e = g := by
    intro T k e he
    have he' : ent (if T = 1 then [g] else []) k = some e := he
    split at he'
    · unfold ent at he'
      split at he'
      · cases he'
      · match k with
        | 0 => contradiction
        | 1 => simp at he'; exact he'.symm
        | k + 2 => simp at he'
    · unfold ent at he'; split at he' <;> simp at he'
  have hnc : ∀ T k e, ent ((init srvs g cv).llog T) k = some e → e.kind ≠ kCommand := by
    intro T k e he hk; rw [hinit T k e he, hgk] at hk; cases hk
  ihave HCF := CcfgG_init (GNames.mk srvs cv g γL γLl γL0 γC γV γA γCm γCC γVs (fun i => (N i).1)
    (fun i => (N i).2.1) (fun i => (N i).2.2.1) (fun i => (N i).2.2.2.1) (fun i => (N i).2.2.2.2)
    γops γP γPM γH γCF) srvs g cv $$ HCF
  ihave H := alloc_core (GNames.mk srvs cv g γL γLl γL0 γC γV γA γCm γCC γVs (fun i => (N i).1)
    (fun i => (N i).2.1) (fun i => (N i).2.2.1) (fun i => (N i).2.2.2.1) (fun i => (N i).2.2.2.2)
    γops γP γPM γH γCF)
    E hnd hne hg1 hgk hcv $$ [HL HLl HL0 HC HV HA HCm HVs HCC HN Hr HP HPM HH HCF]
  · unfold HistG
    rw [show ∀ v g', (init v g' cv).C = ([] : List Entry) from fun _ _ => rfl]
    iframe
    isplitr [HPM HH]
    · unfold OpsG
      iexists ∅
      isplitr
      · ipureintro
        refine ⟨fun T k e he hk => absurd hk (hnc T k e he), fun T1 k1 e1 T2 k2 e2 h1 _ hk1 =>
          absurd hk1 (hnc _ _ _ h1), fun d n y hn => ?_⟩
        cases hn
      · iapply (BigSepM.bigSepM_empty (PROP := IProp GF)).2; iempintro
    isplitl [HPM]
    · unfold PubMaxG
      iexists ∅
      isplitl [HPM]; · iexact HPM
      ipureintro
      refine ⟨fun c T => ?_, fun T k h => False.elim h⟩
      show ((∅ : GMap (SID × Nat) Nat).lookup (c, T)).isSome = true ↔ (none : Option (Nat × Nat)) ≠ none
      simp
    · unfold SnapG
      iexists []
      isplitl [HH]; · iexact HH
      ipureintro
      exact ⟨fun n s h => by simp at h, List.Pairwise.nil⟩
  imod H with ⟨Hinv, Hl⟩
  imodintro
  isplitl [Hinv]; · iexact Hinv
  isplitl [Hops]; · unfold opsAuth; iexact Hops
  iexact Hl

end laws

end gprot
end github_com.hashicorp.raft

end Perennial
