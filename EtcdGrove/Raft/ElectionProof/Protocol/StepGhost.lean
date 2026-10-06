/-
Port of election_proof/protocol.v, lines 3199–4017 at feb5c73d4: the log ghost state
across a step. (On top of `Protocol/GhostState.lean`; Leader Completeness over the vote
table is `Protocol/LeaderCompleteness.lean`.)

Lean notes:
* Proofs are skeletons: every lemma's proof that is not done is `sorry`, on the line
  after a `-- PORT: proof` marker.
* `kl_step` (Prop-valued) is `KlStep`. Lemma names keep the definition's name as written
  (`own_log_ghost_upd` → `ownLogGhost_upd`, `kl_ok_step` → `klOk_step`,
  `acks_ok_upd` → `acksOk_upd`, `snap_ok_message` → `snapOk_message` (the name
  `Model.lean` uses), `repl_ok_message` → `replOk_message`, `ack_agree_full` →
  `ackAgree_full`, `pleader_entry_term` → `pleaderEntry_term`); lemmas that do not
  start with a definition's name keep their snake_case name (`take_prefix_le`,
  `acks_add`, `ack_invs_insert`, `vote_excl`, `hist_replace`, ...).
* Rocq `Local Lemma`s are public theorems here (the later modules use them).
* `if kl is Some _ then true else false` is `kl.isSome`.
* Rocq's chained `a ≤ b ≤ c` in a premise is `a ≤ b ∧ b ≤ c`.
* The Rocq `Local Ltac log_mono_tac` (proof automation) is kept as a comment, for the
  proof-filling port to turn into a macro.
-/
import EtcdGrove.Raft.ElectionProof.Protocol.GhostState

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section ghost
variable [FfiSyntax]
variable {GF : BundledGFunctors} [AllG GF] [InvGS GF]

/-! ### The log ghost state across a step -/

/-- (Lean helper.) `acksOk` of a non-leader, and of a leader, unfolded. -/
private theorem acksOk_nl (γ : RaftElectionNames) (s : PState) (acks : GMap (w64 × w64) Unit) :
    s.role ≠ .leader → acksOk (GF := GF) γ s acks = iprop([∗map] k ↦ _u ∈ acks, ackOk γ s k) := by
  intro H
  unfold acksOk
  split
  · contradiction
  · rfl

private theorem acksOk_l (γ : RaftElectionNames) (s : PState) (acks : GMap (w64 × w64) Unit) :
    s.role = .leader → acksOk (GF := GF) γ s acks = iprop(True) := by
  intro H
  unfold acksOk
  rw [H]

/-- `acksOk` across a step that never lowers the term or the commit index and demotes a
leader only into a higher term. Within one term the caller says how a justification
survives the new log (`Hkeep`); across a term change there is nothing to keep: nothing
of the new term has been acknowledged yet (`AcksTerm`). -/
theorem acksOk_upd (γ : RaftElectionNames) (s s' : PState) (acks : GMap (w64 × w64) Unit) :
    uint.Z s.term ≤ uint.Z s'.term →
    (s'.role ≠ .leader → s.role = .leader →
       uint.Z s.term < uint.Z s'.term) →
    uint.Z s.commit ≤ uint.Z s'.commit →
    AcksTerm s acks →
    ⊢ □ (⌜s'.term = s.term⌝ -∗ ∀ i,
         ⌜uint.Z s'.commit < uint.Z i⌝ -∗
         ackAgree (GF := GF) γ s.base s.log s.term i -∗
         ackAgree γ s'.base s'.log s.term i) -∗
      acksOk γ s acks -∗ acksOk γ s' acks := by
  intro Hle Hdown Hcm Hat
  iintro #Hkeep #Hok
  by_cases Hr' : s'.role = .leader
  · rw [acksOk_l γ s' acks Hr']; ipureintro; trivial
  rw [acksOk_nl γ s' acks Hr']
  by_cases Heq : s'.term = s.term
  · have Hr : s.role ≠ .leader := fun H2 => by
      have := Hdown Hr' H2; rw [Heq] at this; omega
    rw [acksOk_nl γ s acks Hr]
    iapply BigSepM.bigSepM_impl $$ Hok
    imodintro
    iintro %k %u %Hk #Hk
    unfold ackOk
    iintro %Hk12
    obtain ⟨Hk1, Hk2⟩ := Hk12
    ihave #Hk' := Hk $$ %(⟨Hk1.trans Heq, by omega⟩ : k.1 = s.term ∧ uint.Z s.commit < uint.Z k.2)
    rw [Hk1, Heq]
    iapply Hkeep $$ %rfl %k.2 %Hk2 Hk'
  · iapply (BigSepM.bigSepM_forall (Φ := fun (k : w64 × w64) (_ : Unit) => ackOk (GF := GF) γ s' k)).2
    iintro %k %u %Hk
    unfold ackOk
    iintro %Hk12
    have Hkt := Hat k (by rw [show acks !! k = some u from Hk]; rfl)
    have Hne : uint.Z s'.term ≠ uint.Z s.term := fun h => Heq (uint_Z_inj.mp h)
    exact absurd Hk12.1 (fun h => by rw [h] at Hkt; omega)

/- The log part of the ghost state across a step that does not make the node leader, or
keeps it leader in the same term with the same log. A leader that stops being one must
have moved to a higher term: that is what keeps it from ever allocating a second term
log for one term, and what makes its acknowledgements need no justification. The caller
supplies the new state's records, `Match` and commit facts, and how the justification
of an acknowledgement survives (`acksOk_upd`). -/
/-- How the known leader moves across a step: kept within the term (the vote only goes
from none to some, a non-leader does not become leader without `Step.win`), or reset for
a higher term. -/
def KlStep (s s' : PState) (kl kl' : Option w64) : Prop :=
  (kl' = kl ∧ s'.term = s.term ∧
   (s'.vote = W64 0 → s.vote = W64 0) ∧
   (s'.role = .leader → s.role = .leader)) ∨
  (kl' = none ∧ uint.Z s.term < uint.Z s'.term ∧
   s'.role ≠ .leader)

theorem KlStep_bnd (s s' : PState) (kl kl' : Option w64) :
    KlStep s s' kl kl' → bnd s kl ≤ bnd s' kl' := by
  intro H
  unfold bnd
  rcases H with ⟨rfl, Ht, -, -⟩ | ⟨rfl, Hlt, -⟩
  · rw [Ht]; exact Int.le_refl _
  · split <;> omega

theorem klOk_step (γ : RaftElectionNames) (id : w64) (s s' : PState) (kl kl' : Option w64) :
    KlStep s s' kl kl' → ⊢ klOk (GF := GF) γ id s kl -∗ klOk γ id s' kl' := by
  rintro (⟨rfl, Ht, Hv, Hr⟩ | ⟨rfl, -, Hr⟩)
  · unfold klOk
    cases kl' with
    | none =>
      iintro %Hnl
      ipureintro; exact fun H => Hnl (Hr H)
    | some ldr =>
      iintro ⟨⟨%q, #Hw, %Hq⟩, %Hl⟩
      rw [Ht]
      isplitl
      · iexists q; iframe Hw; ipureintro; exact fun H0 => Hq (Hv H0)
      · ipureintro; exact fun H => Hl (Hr H)
  · unfold klOk
    iintro -
    ipureintro; exact Hr

theorem bnd_le (s : PState) (kl : Option w64) : bnd s kl ≤ uint.Z s.term + 1 := by
  unfold bnd; split <;> omega

theorem vbnd_bnd (s : PState) (kl : Option w64) :
    vbnd s.term kl.isSome = bnd s kl := by
  unfold vbnd bnd; cases kl <;> simp

/-- (Lean helper.) `leadLogOwn` and `matchedOk` of a non-leader. -/
private theorem leadLogOwn_nl (γ : RaftElectionNames) (s : PState) (terms : GMap w64 TermRec) :
    s.role ≠ .leader → leadLogOwn (GF := GF) γ s terms = iprop(True) := by
  intro H
  unfold leadLogOwn
  split
  · contradiction
  · rfl

private theorem matchedOk_nl (γ : RaftElectionNames) (s : PState) :
    s.role ≠ .leader → matchedOk (GF := GF) γ s = iprop(True) := by
  intro H
  unfold matchedOk
  split
  · contradiction
  · rfl

theorem ownLogGhost_upd (γ : RaftElectionNames) (id : w64) (s s' : PState) (kl kl' : Option w64) :
    (s'.role = .leader →
       s.role = .leader ∧ s'.term = s.term ∧
       s'.base = s.base ∧ s'.log = s.log) →
    (s'.role ≠ .leader → s.role = .leader →
       uint.Z s.term < uint.Z s'.term) →
    (s'.role = .candidate →
       s.role = .candidate ∧ s'.term = s.term) →
    uint.Z s.term ≤ uint.Z s'.term →
    uint.Z s.commit ≤ uint.Z s'.commit →
    KlStep s s' kl kl' →
    LogOk s' →
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗
      □ (⌜s'.term = s.term⌝ -∗ ∀ i,
           ⌜uint.Z s'.commit < uint.Z i⌝ -∗
           ackAgree γ s.base s.log s.term i -∗
           ackAgree γ s'.base s'.log s.term i) -∗
      logRecs γ s'.base s'.log -∗
      matchedOk γ s' -∗
      baseOk γ s'.base -∗
      (∀ fp, ⌜FullOk s.base fp ∧ PlogWf s.base s.log ∧
               TermsLe s (fp ++ s.log)⌝ -∗
         logRecs γ base0 fp -∗
         commitIn γ (fp ++ s.log) s.commit s.term -∗
         isCommitted γ (cprefix fp s) -∗
         ∃ fp', ⌜(FullOk s'.base fp' ∧ PlogWf s'.base s'.log ∧
                   TermsLe s' (fp' ++ s'.log)) ∧
                  (s'.role ≠ .follower → fp' ++ s'.log = fp ++ s.log)⌝ ∗
           logRecs γ base0 fp' ∗
           commitIn γ (fp' ++ s'.log) s'.commit s'.term ∗
           isCommitted γ (cprefix fp' s') ∗
           □ (∀ t i, ⌜uint.Z t ≤ uint.Z s.term⌝ -∗
                hist γ (fp ++ s.log) t i (bnd s kl) -∗
                hist γ (fp' ++ s'.log) t i (bnd s' kl'))) -∗
      ownLogGhost γ id s' kl' := by
  intro Hlead Hdown Hcand Hle Hcm Hkl Hok'
  iintro H #Hkeep #Hr' #Hm' #Hb' Hnew
  unfold ownLogGhost
  icases H with ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  icases Hnew $$ %fp %Hfull Hfrecs Hcommit Hcmt with ⟨%fp', %Hfp', #Hfr', #Hc', #Hcmt', #Hh⟩
  obtain ⟨Hfull', Hfeq⟩ := Hfp'
  ihave Hevs' := ownEvs_mono γ id s.term s'.term acks acks Hle (fun _ h => h) $$ Hevs
  ihave #Hacks' := acksOk_upd γ s s' acks Hle Hdown Hcm Hacks_term $$ Hkeep Hacks_ok
  ihave #Hkl' := klOk_step γ id s s' kl kl' Hkl $$ Hkl
  have Hterms_ok' : TermsOk terms s' := by
    intro t Ht
    rcases Hterms_ok t Ht with Hlt | ⟨rfl, Hr⟩
    · left; omega
    · by_cases Hr' : s'.role = .leader
      · obtain ⟨-, Hte, -⟩ := Hlead Hr'; right; exact ⟨Hte.symm, Hr'⟩
      · left; exact Hdown Hr' Hr
  have Hwins_ok' : WinsOk wins s' := by
    intro t Ht
    rcases Hwins_ok t Ht with Hlt | ⟨rfl, Hr⟩
    · left; omega
    · by_cases Hr' : s'.role = .leader
      · obtain ⟨-, Hte, -⟩ := Hlead Hr'; right; exact ⟨Hte.symm, Hr'⟩
      · left; exact Hdown Hr' Hr
  have Hacks_term' : AcksTerm s' acks := fun k Hk => by have := Hacks_term k Hk; omega
  have Hcamps_ok' : ∀ T, (camps !! T).isSome → uint.Z T ≤ uint.Z s'.term :=
    fun T HT => by have := Hcamps_ok T HT; omega
  ihave Htlog' : leadLogOwn (GF := GF) γ s' terms $$ [Htlog]
  · by_cases Hr' : s'.role = .leader
    · obtain ⟨Hr, Ht, Hb, Hl⟩ := Hlead Hr'
      unfold leadLogOwn
      rw [Hr', Hr, Ht, Hb, Hl]
      iexact Htlog
    · rw [leadLogOwn_nl γ s' terms Hr']
      ipureintro; trivial
  ihave #Hcown' : campOwn (GF := GF) γ id s' (fp' ++ s'.log) $$ []
  · cases Hr' : s'.role with
    | follower => unfold campOwn; rw [Hr']; ipureintro; trivial
    | candidate =>
      obtain ⟨Hr, Ht⟩ := Hcand Hr'
      rw [Hfeq (by rw [Hr']; decide)]
      unfold campOwn
      rw [Hr', Hr, Ht]
      iexact Hcown
    | leader =>
      obtain ⟨Hr, Ht, -⟩ := Hlead Hr'
      rw [Hfeq (by rw [Hr']; decide)]
      unfold campOwn
      rw [Hr', Hr, Ht]
      iexact Hcown
  ihave #Hvlogs' : vlogsOk (GF := GF) γ s' acks vlogs $$ []
  · unfold vlogsOk
    iapply BigSepM.bigSepM_impl $$ Hvlogs_ok
    imodintro
    iintro %k %x %Hx ⟨%Hxt, #Hx⟩
    isplitr; · ipureintro; omega
    iexact Hx
  ihave #Hhists' : histsOk (GF := GF) γ s' kl' (fp' ++ s'.log) acks $$ []
  · unfold histsOk
    iapply BigSepM.bigSepM_impl $$ Hhists
    imodintro
    iintro %k %u %Hk #Hk
    iapply Hh $$ %k.1 %k.2 %(Hacks_term k (by rw [show acks !! k = some u from Hk]; rfl)) Hk
  iexists γm, terms, γa, acks, fp', γc, camps, γl, vlogs, γw, wins
  iframe % # ∗

theorem ownLogGhost_recs (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64) :
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗ ⌜LogOk s⌝ ∗ logRecs γ s.base s.log := by
  unfold ownLogGhost
  iintro ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  isplitr; · ipureintro; exact Hlog_ok
  iexact Hrecs

/-- The full log, with what the node keeps of it. -/
theorem ownLogGhost_full (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64) :
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗
      ∃ fp, ⌜FullOk s.base fp ∧ PlogWf s.base s.log ∧
              TermsLe s (fp ++ s.log)⌝ ∗
        logRecs γ base0 fp ∗
        commitIn γ (fp ++ s.log) s.commit s.term ∗
        campOwn γ id s (fp ++ s.log) := by
  unfold ownLogGhost
  iintro ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  iexists fp
  isplitr; · ipureintro; exact Hfull
  iframe Hfrecs Hcommit Hcown

theorem ownLogGhost_kl (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64) :
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗ klOk γ id s kl := by
  unfold ownLogGhost
  iintro ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  iexact Hkl

theorem ownLogGhost_wf (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64) :
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗ ⌜PlogWf s.base s.log⌝ := by
  unfold ownLogGhost
  iintro ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  ipureintro; exact Hfull.2.1

theorem ownLogGhost_committed (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64) :
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗ isCommittedIdx γ s.commit := by
  unfold ownLogGhost
  iintro ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  iapply commitIn_committed $$ Hcommit

theorem ownLogGhost_matched (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64) :
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗ matchedOk γ s := by
  unfold ownLogGhost
  iintro ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  iexact Hmatched

theorem ownLogGhost_base (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64) :
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗ baseOk γ s.base := by
  unfold ownLogGhost
  iintro ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  iexact Hbase

/-- The node's committed prefix, with the compacted prefix it is of. -/
theorem ownLogGhost_cmt (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64) :
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗
      ∃ fp, ⌜FullOk s.base fp⌝ ∗ logRecs γ base0 fp ∗ isCommitted γ (cprefix fp s) := by
  unfold ownLogGhost
  iintro ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  iexists fp
  isplitr; · ipureintro; exact Hfull.1
  iframe Hfrecs Hcmt

theorem ownLogGhost_inv (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64) :
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗ raftCommitInv γ := by
  unfold ownLogGhost
  iintro ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  iexact Hinv

/-- The compacted prefix is determined by the base (`FullOk_unique`), so a committed
prefix can be read with any compacted prefix that has records. -/
theorem cprefix_transfer (γ : RaftElectionNames) (fp1 fp2 : List raftpb.Entry) (s : PState) :
    FullOk s.base fp1 → FullOk s.base fp2 →
    ⊢ logRecs (GF := GF) γ base0 fp1 -∗ logRecs γ base0 fp2 -∗
      isCommitted γ (cprefix fp1 s) -∗ isCommitted γ (cprefix fp2 s) := by
  intro H1 H2
  iintro #Hr1 #Hr2 #Hc
  icases FullOk_unique γ s.base fp1 fp2 H1 H2 $$ Hr1 Hr2 with %Heq
  subst Heq
  iexact Hc

omit [FfiSyntax] in
theorem take_prefix_le {A : Type _} (l : List A) (n m : Nat) :
    n ≤ m → l.take n <+: l.take m := by
  intro H
  have : l.take n = (l.take m).take n := by rw [List.take_take, Nat.min_eq_left H]
  rw [this]; exact List.take_prefix _ _

/-- A log that grows past the commit index keeps its committed prefix. -/
theorem cprefix_app (fp : List raftpb.Entry) (s : PState) (es : List raftpb.Entry) :
    uint.Z s.commit ≤ ((fp ++ s.log).length : Int) →
    (fp ++ s.log ++ es).take (uint.Z s.commit).toNat = cprefix fp s := by
  intro H
  unfold cprefix
  apply List.take_append_of_le_length
  omega

/-- Learning the leader of the term, from one of its messages: the bound goes up to the
term plus one. The caller supplies that the node is not in the winning quorum if it has
not voted (`vote_excl`). -/
theorem ownLogGhost_learn (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64)
    (ldr : w64) (q : GSet w64) :
    s.role ≠ .leader →
    ⊢ isWin (GF := GF) γ ldr s.term q -∗ ⌜s.vote = W64 0 → id ∉ q⌝ -∗
      ownLogGhost γ id s kl -∗ ownLogGhost γ id s (some ldr) := by
  intro Hr
  iintro #Hw %Hq H
  unfold ownLogGhost
  icases H with ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  ihave #Hkl' : klOk (GF := GF) γ id s (some ldr) $$ []
  · unfold klOk
    isplitl
    · iexists q; iframe Hw; ipureintro; exact Hq
    · ipureintro; exact fun H => absurd H Hr
  ihave #Hhists' : histsOk (GF := GF) γ s (some ldr) (fp ++ s.log) acks $$ []
  · unfold histsOk
    iapply BigSepM.bigSepM_impl $$ Hhists
    imodintro
    iintro %k %u %Hk #Hk
    iapply hist_mono γ _ _ _ _ (bnd s (some ldr)) (bnd_le s kl) $$ Hk
  iclear Hkl Hhists
  irename Hkl' => Hkl
  irename Hhists' => Hhists
  iexists γm, terms, γa, acks, fp, γc, camps, γl, vlogs, γw, wins
  iframe % # ∗

/-- The same, for a step that leaves the log alone. The caller says how the commit fact
moves to the new commit index. -/
theorem ownLogGhost_mono' (γ : RaftElectionNames) (id : w64) (s s' : PState)
    (kl kl' : Option w64) :
    s'.log = s.log →
    s'.base = s.base →
    (s'.role = .leader →
       s.role = .leader ∧ s'.term = s.term) →
    (s'.role ≠ .leader → s.role = .leader →
       uint.Z s.term < uint.Z s'.term) →
    (s'.role = .candidate →
       s.role = .candidate ∧ s'.term = s.term) →
    uint.Z s.term ≤ uint.Z s'.term →
    uint.Z s.commit ≤ uint.Z s'.commit →
    KlStep s s' kl kl' →
    (s'.commit = s.commit ∨
     uint.Z s'.commit ≤ plogLastIndexZ s.base s.log) →
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗ matchedOk γ s' -∗
      (∀ fp, ⌜FullOk s.base fp ∧ PlogWf s.base s.log⌝ -∗
         logRecs γ base0 fp -∗
         commitIn γ (fp ++ s.log) s.commit s.term -∗
         commitIn γ (fp ++ s.log) s'.commit s'.term) -∗
      (∀ fp, ⌜FullOk s.base fp ∧ PlogWf s.base s.log⌝ -∗
         logRecs γ base0 fp -∗
         isCommitted γ (cprefix fp s) -∗ isCommitted γ (cprefix fp s')) -∗
      ownLogGhost γ id s' kl' := by
  intro Hlog Hbase Hlead Hdown Hcand Hle Hcm Hkl Hcl
  iintro H #Hm' Hcnew Hcmnew
  icases persistent_entails_right (wand_entails (ownLogGhost_recs (GF := GF) γ id s kl)) $$ H
    with ⟨⟨%Hok, #Hr⟩, H⟩
  icases persistent_entails_right (wand_entails (ownLogGhost_base (GF := GF) γ id s kl)) $$ H
    with ⟨#Hb, H⟩
  have Hlead' : s'.role = .leader →
      s.role = .leader ∧ s'.term = s.term ∧ s'.base = s.base ∧ s'.log = s.log :=
    fun Hr' => ⟨(Hlead Hr').1, (Hlead Hr').2, Hbase, Hlog⟩
  have Hok' : LogOk s' := by
    obtain ⟨h1, h2, h3⟩ := Hok
    unfold LogOk
    rw [Hlog, Hbase]
    refine ⟨h1, by omega, ?_⟩
    rcases Hcl with h | h
    · rw [h]; exact h3
    · exact h
  iapply ownLogGhost_upd γ id s s' kl kl' Hlead' Hdown Hcand Hle Hcm Hkl Hok' $$ H [] [] Hm' [] [Hcnew Hcmnew]
  · imodintro
    iintro %_ %i %_ #Ha
    rw [Hlog, Hbase]
    iexact Ha
  · rw [Hlog, Hbase]; iexact Hr
  · rw [Hbase]; iexact Hb
  · iintro %fp %Hfw #Hfr #Hc #Hcm
    obtain ⟨Hf, Hw, Ht⟩ := Hfw
    ihave #Hc' := Hcnew $$ %fp %(⟨Hf, Hw⟩ : FullOk s.base fp ∧ PlogWf s.base s.log) Hfr Hc
    ihave #Hcm' := Hcmnew $$ %fp %(⟨Hf, Hw⟩ : FullOk s.base fp ∧ PlogWf s.base s.log) Hfr Hcm
    iexists fp
    isplitr
    · ipureintro
      rw [Hlog, Hbase]
      refine ⟨⟨Hf, Hw, ?_⟩, fun _ => rfl⟩
      intro j x Hx
      obtain ⟨H1, H2⟩ := Ht j x Hx
      refine ⟨by omega, fun Hc => ?_⟩
      obtain ⟨Hc0, Hte⟩ := Hcand Hc
      rw [Hte]; exact H2 Hc0
    isplitr; · iexact Hfr
    isplitr; · rw [Hlog]; iexact Hc'
    isplitr; · iexact Hcm'
    imodintro
    iintro %t %i %_ #Hh
    rw [Hlog]
    iapply hist_mono γ _ t i _ _ (KlStep_bnd s s' kl kl' Hkl) $$ Hh

/-- The same, when `Match` and the commit index do not change either, at the same
term ... -/
theorem ownLogGhost_mono (γ : RaftElectionNames) (id : w64) (s s' : PState) (kl : Option w64) :
    s'.log = s.log →
    s'.base = s.base →
    s'.commit = s.commit →
    (s'.role = .leader →
       s.role = .leader ∧ s'.term = s.term ∧
       s'.matched = s.matched) →
    (s'.role = .candidate →
       s.role = .candidate ∧ s'.term = s.term) →
    (s.role = .leader → s'.role = .leader) →
    s'.term = s.term →
    (s'.vote = W64 0 → s.vote = W64 0) →
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗ ownLogGhost γ id s' kl := by
  intro Hlog Hbase Hcm Hlead Hcand Hstay Hte Hv
  iintro H
  icases persistent_entails_right (wand_entails (ownLogGhost_matched (GF := GF) γ id s kl)) $$ H
    with ⟨#Hm, H⟩
  iapply ownLogGhost_mono' γ id s s' kl kl Hlog Hbase
    (fun Hr' => ⟨(Hlead Hr').1, (Hlead Hr').2.1⟩) (fun Hr' Hr => absurd (Hstay Hr) Hr') Hcand
    (Int.le_of_eq (congrArg _ Hte.symm)) (Int.le_of_eq (congrArg _ Hcm.symm))
    (Or.inl ⟨rfl, Hte, Hv, fun Hr' => (Hlead Hr').1⟩) (Or.inl Hcm) $$ H [] [] []
  · by_cases Hr' : s'.role = .leader
    · obtain ⟨Hr, Ht, Hmt⟩ := Hlead Hr'
      iapply matchedOk_eq γ s s' (by rw [Hr, Hr']) Ht Hmt $$ Hm
    · rw [matchedOk_nl γ s' Hr']; ipureintro; trivial
  · iintro %fp %_ - #Hc
    rw [Hcm]
    iapply commitIn_agree γ _ _ s.commit s.term s'.term (Int.le_of_eq (congrArg _ Hte.symm)) rfl $$ Hc
  · iintro %fp %_ - #Hc
    unfold cprefix
    rw [Hcm, Hlog]
    iexact Hc

/-- ... or at a higher term, where the known leader is forgotten. -/
theorem ownLogGhost_mono_up (γ : RaftElectionNames) (id : w64) (s s' : PState) (kl : Option w64) :
    s'.log = s.log →
    s'.base = s.base →
    s'.commit = s.commit →
    s'.role = .follower →
    uint.Z s.term < uint.Z s'.term →
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗ ownLogGhost γ id s' none := by
  intro Hlog Hbase Hcm Hr' Hlt
  iintro H
  have Hnl : s'.role ≠ .leader := by rw [Hr']; decide
  iapply ownLogGhost_mono' γ id s s' kl none Hlog Hbase (fun H => absurd H Hnl) (fun _ _ => Hlt)
    (fun H => by rw [Hr'] at H; cases H) (by omega) (Int.le_of_eq (congrArg _ Hcm.symm))
    (Or.inr ⟨rfl, Hlt, Hnl⟩) (Or.inl Hcm) $$ H [] [] []
  · rw [matchedOk_nl γ s' Hnl]; ipureintro; trivial
  · iintro %fp %_ - #Hc
    rw [Hcm]
    iapply commitIn_agree γ _ _ s.commit s.term s'.term (by omega) rfl $$ Hc
  · iintro %fp %_ - #Hc
    unfold cprefix
    rw [Hcm, Hlog]
    iexact Hc

/- Discharging `ownLogGhost_mono`'s premises for a concrete step. Rocq:
```
Local Ltac log_mono_tac :=
  first [ (rewrite /kl_step; left; split_and!; [reflexivity|..]; simpl; intros;
           first [ done | congruence ])
        | (rewrite ?pbecome_follower_vote_same; intros; done)
        | (simpl; intros; first [ done | congruence | lia | word | (split_and!; done) ]) ].
```
-/

/-- Adding an acknowledgement to one's own map: fresh, or already there. -/
theorem acks_add (γa : GName) (acks : GMap (w64 × w64) Unit) (k : w64 × w64) :
    ⊢ ghostMapAuth (GF := GF) γa 1 acks -∗ ([∗map] k ↦ u ∈ acks, k ↪[γa]□ u) ==∗
      ghostMapAuth γa 1 (<[k := ()]> acks) ∗
      ([∗map] k ↦ u ∈ <[k := ()]> acks, k ↪[γa]□ u) ∗ k ↪[γa]□ () := by
  iintro Hauth #Hfr
  cases Hk : acks !! k with
  | some u =>
    rw [GMap.insert_id acks k () (by rw [Hk])]
    imodintro
    iframe Hauth Hfr
    iapply (BigSepM.bigSepM_lookup (Φ := fun k u => iprop(k ↪[γa]□ u)) Hk) $$ Hfr
  | none =>
    imod ghost_map_insert_persist k () Hk $$ Hauth with ⟨Hauth, #Hnew⟩
    imodintro
    iframe Hauth Hnew
    iapply (BigSepM.bigSepM_insert (Φ := fun k u => iprop(k ↪[γa]□ u)) Hk).2
    iframe Hnew Hfr

theorem AcksTerm_insert (s : PState) (acks : GMap (w64 × w64) Unit) (t i : w64) :
    uint.Z t ≤ uint.Z s.term → AcksTerm s acks → AcksTerm s (<[(t, i) := ()]> acks) := by
  intro Ht H k Hk
  by_cases Hkk : k = (t, i)
  · subst Hkk; exact Ht
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm Hkk)] at Hk; exact H k Hk

/-- The per-acknowledgement invariants of a new acknowledgement, at the node's term: its
history, and nothing for the vote-time logs (they are of terms up to this one). -/
theorem ack_invs_insert (γ : RaftElectionNames) (s : PState) (kl : Option w64)
    (F : List raftpb.Entry) (acks : GMap (w64 × w64) Unit)
    (vlogs : GMap Nat ((w64 × Bool) × List raftpb.Entry)) (i : w64) :
    ⊢ hist (GF := GF) γ F s.term i (bnd s kl) -∗
      histsOk γ s kl F acks -∗ vlogsOk γ s acks vlogs -∗
      histsOk γ s kl F (<[(s.term, i) := ()]> acks) ∗
      vlogsOk γ s (<[(s.term, i) := ()]> acks) vlogs := by
  unfold histsOk vlogsOk
  iintro #Hh #Hhs #Hv
  isplitl
  · iapply (BigSepM.bigSepM_insert_elim (Φ := fun (k : w64 × w64) (_ : Unit) => hist (GF := GF) γ F k.1 k.2 (bnd s kl))
      (m := acks) (i := (s.term, i)) (x := ()))
      $$ Hh Hhs
  · iapply BigSepM.bigSepM_impl $$ Hv
    imodintro
    iintro %k %xx %Hx ⟨%Hxt, #Hx⟩
    isplitr; · ipureintro; exact Hxt
    iapply (BigSepM.bigSepM_insert_elim (Φ := fun (k : w64 × w64) (_ : Unit) => iprop(∀ (_ : uint.Z k.1 < uint.Z xx.1.1),
      hist (GF := GF) γ xx.2 k.1 k.2 (vbnd xx.1.1 xx.1.2)))) $$ [] Hx
    iintro %Hlt
    exact absurd Hlt (by simp only; omega)

/-- A node acknowledges at its own term, with the justification `acksOk` asks of it and
the history `histsOk` asks of it. -/
theorem ownLogGhost_ack (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64)
    (i : w64) :
    ⊢ ackOk (GF := GF) γ s (s.term, i) -∗
      (∀ fp, ⌜FullOk s.base fp ∧ PlogWf s.base s.log⌝ -∗
         logRecs γ base0 fp -∗
         commitIn γ (fp ++ s.log) s.commit s.term -∗
         hist γ (fp ++ s.log) s.term i (bnd s kl)) -∗
      ownLogGhost γ id s kl ==∗ ownLogGhost γ id s kl ∗ isAcked γ id s.term i := by
  iintro #Hk Hhnew H
  unfold ownLogGhost
  icases H with ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  ihave #Hh := Hhnew $$ %fp %(⟨Hfull.1, Hfull.2.1⟩ : FullOk s.base fp ∧ PlogWf s.base s.log)
    Hfrecs Hcommit
  icases ack_invs_insert γ s kl (fp ++ s.log) acks vlogs i $$ Hh Hhists Hvlogs_ok
    with ⟨#Hhists', #Hvlogs'⟩
  imod acks_add γa acks (s.term, i) $$ Hacks Hafrags with ⟨Hacks', #Hafr', #Hnew⟩
  imod ownEvs_ack γ id s.term acks i $$ Hevs with ⟨Hevs', #Hev⟩
  have Hacks_term' := AcksTerm_insert s acks s.term i (Int.le_refl _) Hacks_term
  ihave #Hacks_ok' : acksOk (GF := GF) γ s (<[(s.term, i) := ()]> acks) $$ []
  · by_cases Hr : s.role = .leader
    · rw [acksOk_l γ s (<[(s.term, i) := ()]> acks) Hr]; ipureintro; trivial
    · rw [acksOk_nl γ s (<[(s.term, i) := ()]> acks) Hr, acksOk_nl γ s acks Hr]
      iapply (BigSepM.bigSepM_insert_elim
        (Φ := fun (k : w64 × w64) (_ : Unit) => ackOk (GF := GF) γ s k)
        (m := acks) (i := (s.term, i)) (x := ())) $$ Hk Hacks_ok
  imodintro
  isplitl
  · iexists γm, terms, γa, (<[(s.term, i) := ()]> acks), fp, γc, camps, γl, vlogs, γw, wins
    iframe % # ∗
  · unfold isAcked
    iright
    isplitr
    · iexists γa
      isplitr; · ipureintro; exact Haname
      iexact Hnew
    iexact Hev

theorem pleaderEntry_term (s : PState) : (pleaderEntry s).Term' = s.term := rfl

/-- (Lean helper.) `leadLogOwn` and `campOwn` of a leader, unfolded. -/
private theorem leadLogOwn_l (γ : RaftElectionNames) (s : PState) (terms : GMap w64 TermRec) :
    s.role = .leader → leadLogOwn (GF := GF) γ s terms =
      iprop(∃ γt, ∃ (M : GMap w64 (raftpb.Entry × w64)), ∃ l0,
        ⌜terms !! s.term = some ((γt, s.base), l0)⌝ ∗
        ghostMapAuth γt 1 M ∗
        ([∗map] i ↦ e ∈ M, i ↪[γt]□ e) ∗
        ⌜∀ i, (M !! i).isSome → uint.Z i ≤ plogLastIndexZ s.base s.log⌝ ∗
        ⌜l0 <+: s.log⌝ ∗
        leadFrags γt l0 s.log) := by
  intro H
  unfold leadLogOwn
  rw [H]

private theorem campOwn_l (γ : RaftElectionNames) (id : w64) (s : PState) (F : List raftpb.Entry) :
    s.role = .leader → campOwn (GF := GF) γ id s F =
      iprop(∃ F0, isCamp γ id s.term F0 ∗
       ⌜F0 <+: F ∧ plogLastIndexZ base0 F0 < plogLastIndexZ base0 F ∧
         (plogLast base0 F).term' = s.term⌝) := by
  intro H
  unfold campOwn
  rw [H]

/-- A leader's whole log is a log of the leader of its term, with its full log and the
commit fact about it. -/
theorem ownLogGhost_lead_full (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64) :
    s.role = .leader →
    ⊢ isLeader (GF := GF) γ id s.term -∗ ownLogGhost γ id s kl -∗
      (∃ fp, leadPrefix γ id s.term s.base s.log ∗
         lpfull γ id s.term s.base s.log fp ∗
         commitIn γ (fp ++ s.log) s.commit s.term) ∗
      ownLogGhost γ id s kl := by
  intro Hr
  iintro #Hl H
  unfold ownLogGhost
  icases H with ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  rw [leadLogOwn_l γ s terms Hr]
  icases Htlog with ⟨%γt, %M, %l0, %Hγt, Ha, #Hfr, %Hdom, %Hpre, #Hlf⟩
  ihave #Hcown0 := Hcown
  rw [campOwn_l γ id s _ Hr]
  icases Hcown0 with ⟨%F0, #Hc0, %HF0⟩
  have ⟨Hf, Hw, Ht⟩ := Hfull
  isplitr [Ha Hterms Hacks Hcamps Hvlogs Hwins Hevs]
  · iexists fp
    isplitr
    · unfold leadPrefix
      isplitr; · iexact Hl
      iexists γt, l0
      isplitr
      · unfold isTermLog
        iexists γm
        isplitr; · ipureintro; exact Htname
        iapply (BigSepM.bigSepM_lookup (Φ := fun (t : w64) (γt : TermRec) => iprop(t ↪[γm]□ γt))
          Hγt) $$ Htfrags
      isplitr; · ipureintro; exact ⟨Hlog_ok.1, Hpre⟩
      isplitr; · iexact Hrecs
      iexact Hlf
    isplitr
    · unfold lpfull
      iexists F0
      isplitr; · iexact Hc0
      isplitr; · iexact Hfrecs
      ipureintro; exact ⟨Hf, HF0.1, Hw, fun j x Hx => (Ht j x Hx).1⟩
    · iexact Hcommit
  · iexists γm, terms, γa, acks, fp, γc, camps, γl, vlogs, γw, wins
    iframe % # ∗
    rw [leadLogOwn_l γ s terms Hr, campOwn_l γ id s (fp ++ s.log) Hr]
    isplitl [Ha]
    · iexists γt, M, l0
      iframe % # ∗
    · iexact Hcown

theorem ownLogGhost_lead_prefix (γ : RaftElectionNames) (id : w64) (s : PState)
    (kl : Option w64) :
    s.role = .leader →
    ⊢ isLeader (GF := GF) γ id s.term -∗ ownLogGhost γ id s kl -∗
      leadPrefix γ id s.term s.base s.log ∗ ownLogGhost γ id s kl := by
  intro Hr
  iintro #Hl H
  icases ownLogGhost_lead_full γ id s kl Hr $$ Hl H with ⟨⟨%fp, #Hp, -, -⟩, H⟩
  isplitr [H]
  · iexact Hp
  · iexact H

/-- `Step.campaign`, on the log ghost state: record the campaign log (the full log,
unchanged since) and, for the self-vote, the vote-time log -- with the histories of
every earlier acknowledgement; the new term has no known leader. -/
theorem ownLogGhost_campaign (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64) :
    s.role ≠ .leader →
    uint.Z s.term + 1 < 2 ^ 64 →
    ⊢ ownLogGhost (GF := GF) γ id s kl ==∗
      ∃ k F, ownLogGhost γ id (pbecomeCandidate id s) none ∗
        isCamp γ id (s.term + W64 1) F ∗
        isVlog γ id k (s.term + W64 1) false F ∗ logRecs γ base0 F ∗
        ⌜PlogWf base0 F ∧ plogLast base0 F = plogLast s.base s.log⌝ ∗
        voteEv γ id (s.term + W64 1) false F := by
  intro Hr Hnw
  iintro H
  unfold ownLogGhost
  icases H with ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  have HT' : uint.Z (s.term + W64 1) = uint.Z s.term + 1 := by word
  have ⟨Hf, Hw, Htle⟩ := Hfull
  have HwF : PlogWf base0 (fp ++ s.log) := full_wf _ _ _ Hf Hw
  have Hnl : (pbecomeCandidate id s).role ≠ .leader := by
    show Role.candidate ≠ Role.leader; decide
  have Hbs := bnd_le s kl
  have Hcfree : camps !! (s.term + W64 1) = none := by
    cases h : camps !! (s.term + W64 1) with
    | none => rfl
    | some _ => have := Hcamps_ok _ (by rw [h]; rfl); omega
  imod ghost_map_insert_persist (s.term + W64 1) (fp ++ s.log) Hcfree $$ Hcamps with ⟨Hcamps', #Hcf⟩
  obtain ⟨k, Hk⟩ := Iris.Std.List.fresh vlogs.domList
  have Hkfree : vlogs !! k = none := by
    cases h : vlogs !! k with
    | none => rfl
    | some _ => exact absurd ((GMap.mem_dom_list vlogs k).mpr (by rw [h]; rfl)) Hk
  imod ghost_map_insert_persist k ((s.term + W64 1, false), fp ++ s.log) Hkfree $$ Hvlogs
    with ⟨Hvl, #Hvf⟩
  ihave #Hcamp : isCamp (GF := GF) γ id (s.term + W64 1) (fp ++ s.log) $$ []
  · unfold isCamp
    iexists γc
    isplitr
    · ipureintro
      refine ⟨Hcname, HwF, fun j x Hx => ?_⟩
      have := (Htle j x Hx).1
      omega
    iexact Hcf
  ihave #HrF := logRecs_full γ s.base fp s.log Hf $$ Hfrecs Hrecs
  imod ownEvs_vote γ id s.term (s.term + W64 1) acks false (fp ++ s.log) (by omega) $$ Hevs []
    with ⟨Hevs', #Hvev⟩
  · unfold histsOk
    iapply BigSepM.bigSepM_impl $$ Hhists
    imodintro
    iintro %kk %u %Hkk #Hh %_
    iapply hist_mono γ _ _ _ _ (vbnd (s.term + W64 1) false)
      (by unfold vbnd; simp only [Bool.false_eq_true, ↓reduceIte]; omega) $$ Hh
  have Hterms_ok' : TermsOk terms (pbecomeCandidate id s) := by
    intro t Ht
    left
    show uint.Z t < uint.Z (s.term + W64 1)
    rcases Hterms_ok t Ht with h | ⟨-, h⟩
    · omega
    · exact absurd h Hr
  have Hwins_ok' : WinsOk wins (pbecomeCandidate id s) := by
    intro t Ht
    left
    show uint.Z t < uint.Z (s.term + W64 1)
    rcases Hwins_ok t Ht with h | ⟨-, h⟩
    · omega
    · exact absurd h Hr
  have Hacks_term' : AcksTerm (pbecomeCandidate id s) acks := fun kk Hkk => by
    have := Hacks_term kk Hkk
    show uint.Z kk.1 ≤ uint.Z (s.term + W64 1)
    omega
  have Hlog_ok' : LogOk (pbecomeCandidate id s) := Hlog_ok
  have Hfull' : FullOk s.base fp ∧ PlogWf s.base s.log ∧
      TermsLe (pbecomeCandidate id s) (fp ++ s.log) := by
    refine ⟨Hf, Hw, fun j x Hx => ?_⟩
    have := (Htle j x Hx).1
    show uint.Z x ≤ uint.Z (s.term + W64 1) ∧
      (Role.candidate = Role.candidate → uint.Z x < uint.Z (s.term + W64 1))
    exact ⟨by omega, fun _ => by omega⟩
  have Hcamps_ok' : ∀ T, ((<[s.term + W64 1 := fp ++ s.log]> camps) !! T).isSome →
      uint.Z T ≤ uint.Z (s.term + W64 1) := by
    intro T HT
    by_cases hT : T = s.term + W64 1
    · rw [hT]; exact Int.le_refl _
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hT)] at HT
      have := Hcamps_ok T HT
      omega
  ihave Htlog' : leadLogOwn (GF := GF) γ (pbecomeCandidate id s) terms $$ []
  · rw [leadLogOwn_nl γ _ terms Hnl]; ipureintro; trivial
  ihave #Hacks_ok' : acksOk (GF := GF) γ (pbecomeCandidate id s) acks $$ []
  · rw [acksOk_nl γ _ acks Hnl]
    iapply (BigSepM.bigSepM_forall (Φ := fun (k : w64 × w64) (_ : Unit) =>
      ackOk (GF := GF) γ (pbecomeCandidate id s) k)).2
    iintro %kk %u %Hkk
    unfold ackOk
    iintro %Hk1
    have := Hacks_term kk (by rw [show acks !! kk = some u from Hkk]; rfl)
    have h1 : kk.1 = s.term + W64 1 := Hk1.1
    rw [h1] at this
    exact absurd this (by omega)
  ihave #Hmatched' : matchedOk (GF := GF) γ (pbecomeCandidate id s) $$ []
  · rw [matchedOk_nl γ _ Hnl]; ipureintro; trivial
  ihave #Hcommit' : commitIn (GF := GF) γ (fp ++ s.log) s.commit (s.term + W64 1) $$ []
  · iapply commitIn_agree γ _ _ s.commit s.term (s.term + W64 1) (by omega) rfl $$ Hcommit
  ihave #Hcown' : campOwn (GF := GF) γ id (pbecomeCandidate id s) (fp ++ s.log) $$ []
  · unfold campOwn
    rw [show (pbecomeCandidate id s).role = .candidate from rfl,
      show (pbecomeCandidate id s).term = s.term + W64 1 from rfl]
    iexact Hcamp
  ihave #Hkl' : klOk (GF := GF) γ id (pbecomeCandidate id s) none $$ []
  · unfold klOk; ipureintro; exact Hnl
  ihave #Hvlogs' : vlogsOk (GF := GF) γ (pbecomeCandidate id s) acks
      (<[k := ((s.term + W64 1, false), fp ++ s.log)]> vlogs) $$ []
  · unfold vlogsOk
    iapply (BigSepM.bigSepM_insert_elim
      (Φ := fun (_ : Nat) (x : (w64 × Bool) × List raftpb.Entry) =>
        iprop(⌜uint.Z x.1.1 ≤ uint.Z (pbecomeCandidate id s).term⌝ ∗ [∗map] k ↦ _u ∈ acks,
          ∀ (_ : uint.Z k.1 < uint.Z x.1.1), hist (GF := GF) γ x.2 k.1 k.2 (vbnd x.1.1 x.1.2)))
      (m := vlogs) (i := k) (x := ((s.term + W64 1, false), fp ++ s.log))) $$ [] []
    · isplitr; · ipureintro; exact Int.le_refl _
      unfold histsOk
      iapply BigSepM.bigSepM_impl $$ Hhists
      imodintro
      iintro %kk %u %Hkk #Hh %_
      iapply hist_mono γ _ _ _ _ (vbnd (s.term + W64 1) false)
        (by unfold vbnd; simp only [Bool.false_eq_true, ↓reduceIte]; omega) $$ Hh
    · iapply BigSepM.bigSepM_impl $$ Hvlogs_ok
      imodintro
      iintro %kk %x %Hx ⟨%Hxt, #Hx⟩
      isplitr
      · ipureintro; show uint.Z x.1.1 ≤ uint.Z (s.term + W64 1); omega
      iexact Hx
  ihave #Hhists' : histsOk (GF := GF) γ (pbecomeCandidate id s) none (fp ++ s.log) acks $$ []
  · unfold histsOk
    iapply BigSepM.bigSepM_impl $$ Hhists
    imodintro
    iintro %kk %u %Hkk #Hh
    iapply hist_mono γ _ _ _ _ (bnd (pbecomeCandidate id s) none)
      (by show bnd s kl ≤ uint.Z (s.term + W64 1); omega) $$ Hh
  ihave #Hcmt' : isCommitted (GF := GF) γ (cprefix fp (pbecomeCandidate id s)) $$ []
  · unfold cprefix
    rw [show (pbecomeCandidate id s).log = s.log from rfl,
      show (pbecomeCandidate id s).commit = s.commit from rfl]
    iexact Hcmt
  imodintro
  iexists k, fp ++ s.log
  isplitl
  · iexists γm, terms, γa, acks, fp, γc, (<[s.term + W64 1 := fp ++ s.log]> camps), γl,
      (<[k := ((s.term + W64 1, false), fp ++ s.log)]> vlogs), γw, wins
    rw [show (pbecomeCandidate id s).log = s.log from rfl,
      show (pbecomeCandidate id s).base = s.base from rfl,
      show (pbecomeCandidate id s).commit = s.commit from rfl,
      show (pbecomeCandidate id s).term = s.term + W64 1 from rfl]
    iframe % # ∗
  · isplitr; · iexact Hcamp
    isplitr
    · unfold isVlog
      iexists γl
      isplitr; · ipureintro; exact Hlname
      iexact Hvf
    isplitr; · iexact HrF
    isplitr; · ipureintro; exact ⟨HwF, full_last _ _ _ Hf⟩
    iexact Hvev

/-- A first vote, on the log ghost state: record the vote-time log, which has the
histories of all acknowledgements, at the node's bound -- the term, or the term plus one
if it knows the term's leader. -/
theorem ownLogGhost_vote (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64) :
    ⊢ ownLogGhost (GF := GF) γ id s kl ==∗
      ∃ k F, ownLogGhost γ id s kl ∗
        isVlog γ id k s.term kl.isSome F ∗
        logRecs γ base0 F ∗ klOk γ id s kl ∗
        ⌜PlogWf base0 F ∧
          ∀ x, plogUpToDate base0 F x = plogUpToDate s.base s.log x⌝ ∗
        voteEv γ id s.term kl.isSome F := by
  iintro H
  unfold ownLogGhost
  icases H with ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  have ⟨Hf, Hw, Htle⟩ := Hfull
  obtain ⟨k, Hk⟩ := Iris.Std.List.fresh vlogs.domList
  have Hkfree : vlogs !! k = none := by
    cases h : vlogs !! k with
    | none => rfl
    | some _ => exact absurd ((GMap.mem_dom_list vlogs k).mpr (by rw [h]; rfl)) Hk
  imod ghost_map_insert_persist k ((s.term, kl.isSome), fp ++ s.log) Hkfree $$ Hvlogs
    with ⟨Hvl, #Hvf⟩
  ihave #Hvlogs' : vlogsOk (GF := GF) γ s acks
      (<[k := ((s.term, kl.isSome), fp ++ s.log)]> vlogs) $$ []
  · unfold vlogsOk
    iapply (BigSepM.bigSepM_insert_elim
      (Φ := fun (_ : Nat) (x : (w64 × Bool) × List raftpb.Entry) =>
        iprop(⌜uint.Z x.1.1 ≤ uint.Z s.term⌝ ∗ [∗map] k ↦ _u ∈ acks,
          ∀ (_ : uint.Z k.1 < uint.Z x.1.1), hist (GF := GF) γ x.2 k.1 k.2 (vbnd x.1.1 x.1.2)))
      (m := vlogs) (i := k) (x := ((s.term, kl.isSome), fp ++ s.log))) $$ [] Hvlogs_ok
    isplitr; · ipureintro; exact Int.le_refl _
    unfold histsOk
    iapply BigSepM.bigSepM_impl $$ Hhists
    imodintro
    iintro %kk %u %Hkk #Hh %_
    dsimp only
    rw [vbnd_bnd]
    iexact Hh
  imod ownEvs_vote γ id s.term s.term acks kl.isSome (fp ++ s.log) (Int.le_refl _) $$ Hevs []
    with ⟨Hevs', #Hvev⟩
  · unfold histsOk
    iapply BigSepM.bigSepM_impl $$ Hhists
    imodintro
    iintro %kk %u %Hkk #Hh %_
    rw [vbnd_bnd]
    iexact Hh
  imodintro
  iexists k, fp ++ s.log
  isplitl
  · iexists γm, terms, γa, acks, fp, γc, camps, γl, (<[k := ((s.term, kl.isSome), fp ++ s.log)]> vlogs), γw, wins
    iframe % # ∗
  · isplitr
    · unfold isVlog
      iexists γl
      isplitr; · ipureintro; exact Hlname
      iexact Hvf
    isplitr; · iapply logRecs_full γ s.base fp s.log Hf $$ Hfrecs Hrecs
    isplitr; · iexact Hkl
    isplitr; · ipureintro; exact ⟨full_wf _ _ _ Hf Hw, fun x => full_up_to_date _ _ _ x Hf⟩
    iexact Hvev

omit [FfiSyntax] in
/-- (Lean helper.) The true branch of an `if` in a BI. -/
private theorem ite_pos_elim {PROP : Type _} [BI PROP] {c : Prop} [Decidable c] (P Q : PROP)
    (h : c) : (if c then P else Q) ⊢ P := by
  rw [ite_eq_left_iff.mpr (fun hn => absurd h hn)]

/-- (Lean helper.) One entry's record in a log with records, at any base. -/
private theorem logRecs_lookup_b (γ : RaftElectionNames) (b : entryID) (es : List raftpb.Entry)
    (k : Nat) (e : raftpb.Entry) :
    es[k]? = some e → uint.Z b.index' + (k : Int) + 1 < 2 ^ 64 →
    ⊢ logRecs (GF := GF) γ b es -∗
      ∃ pt, ⌜plogTermAt b es (pidx b k) = some pt⌝ ∗ isEntryR γ e pt := by
  intro He Hr
  unfold logRecs
  iintro #H
  ihave #He' := BigSepL.bigSepL_lookup He $$ H
  iapply ite_pos_elim _ _ Hr $$ He'

/-- What a leader's `MsgSnap` carries beyond its leadership. `Qed` since 2026-10-03
(admitted from 2026-10-02 as a client assumption, before `SnapOk` carried the commit
bound and the log fact): `isCommittedIdx` is `isCommittedIdx_le` of the commit index;
`isSnapMeta` is the log's record of the entry at `m.index` (`logRecs`), or, when the
snapshot is exactly at the base, `ownLogGhost`'s `baseOk`. -/
theorem snapOk_message (γ : RaftElectionNames) (id : w64) (s : PState) (m : Msg) :
    PlogWfR s.base s.log →
    SnapOk id s m →
    ⊢ isCommittedIdx (GF := GF) γ s.commit -∗
      logRecs γ s.base s.log -∗
      baseOk γ s.base -∗
      isCommittedIdx γ m.index ∗ isSnapMeta γ m.logterm m.index ∗
      ⌜plogTermAt s.base s.log m.index = some m.logterm⌝ := by
  intro Hwf Hsnap
  obtain ⟨-, -, -, -, Hnz, Hle, Hidx⟩ := Hsnap
  iintro #Hc #Hrecs #Hb
  isplitr; · iapply isCommittedIdx_le γ s.commit m.index Hle $$ Hc
  isplitr
  · have ⟨Hlo, Hhi⟩ := plogTermAt_some_range _ _ _ _ Hidx
    by_cases Heq : uint.Z m.index = uint.Z s.base.index'
    · have Hi : m.index = s.base.index' := uint_Z_inj.mp Heq
      rw [Hi, plogTermAt_base] at Hidx
      injection Hidx with Ht
      unfold baseOk
      icases Hb with (%H0 | #Hm)
      · exact absurd (by word : m.index = W64 0) Hnz
      · rw [Hi, ← Ht]; iexact Hm
    · obtain ⟨k, hk⟩ : ∃ k : Nat, (k : Int) = uint.Z m.index - uint.Z s.base.index' - 1 :=
        ⟨_, Int.toNat_of_nonneg (by omega)⟩
      unfold plogTermAt at Hidx
      simp only [show ¬ (uint.Z m.index < uint.Z s.base.index') by omega,
        show ¬ (uint.Z m.index = uint.Z s.base.index') by omega, ↓reduceIte,
        show (uint.Z m.index - uint.Z s.base.index' - 1).toNat = k by omega] at Hidx
      cases He : s.log[k]? with
      | none => rw [He] at Hidx; cases Hidx
      | some e =>
        rw [He] at Hidx
        simp only [Option.map_eq_map, Option.map_some, Option.some.injEq] at Hidx
        have Hr : uint.Z s.base.index' + (k : Int) + 1 < 2 ^ 64 := by
          have := uint_Z_lt m.index; omega
        icases logRecs_lookup_b γ s.base s.log k e He Hr $$ Hrecs with ⟨%pt, -, #He⟩
        unfold isSnapMeta
        iexists e
        isplitr
        · unfold isEntry; iexists pt; iexact He
        ipureintro
        exact ⟨Hidx, uint_Z_inj.mp (by rw [Hwf k e He Hr]; omega)⟩
  · ipureintro; exact Hidx

/-- What a leader's broadcast carries, from what the leader holds. -/
theorem replOk_message (γ : RaftElectionNames) (id : w64) (s : PState) (m : Msg)
    (fp : List raftpb.Entry) :
    PlogWfR s.base s.log →
    ReplOk id s m → id ≠ W64 0 →
    ⊢ isLeader (GF := GF) γ id s.term -∗
      leadPrefix γ id s.term s.base s.log -∗
      lpfull γ id s.term s.base s.log fp -∗
      logRecs γ s.base s.log -∗
      commitIn γ (fp ++ s.log) s.commit s.term -∗
      baseOk γ s.base -∗
      isCommitted γ (cprefix fp s) -∗
      isMessage γ m := by
  intro Hr Hok Hid
  iintro #Hl #Hp #Hlf #Hrecs #Hc #Hb #Hcm
  ihave #Hlf2 := Hlf
  iunfold lpfull at Hlf2
  icases Hlf2 with ⟨%F0, -, #Hfr, %Hfull⟩
  ihave #HrF := logRecs_full γ s.base fp s.log Hfull.1 $$ Hfr Hrecs
  have HwF := full_wf _ _ _ Hfull.1 Hfull.2.2.1
  rcases Hok with ⟨Hty, Hfrom, Hterm, -, Hidx, Hcm', -, Hpre, Hpay⟩ | Hsnap
  · unfold isMessage
    rw [Hty]
    dsimp only
    rw [Hfrom, Hterm]
    isplitr; · ipureintro; exact Hpay
    isplitr; · iexact Hl
    isplitl
    · iexists s.base, s.log, fp
      isplitr; · iexact Hp
      isplitr; · ipureintro; exact ⟨Hidx, Hpre⟩
      isplitr; · iexact Hlf
      isplitr; · iapply commitIn_le γ _ s.commit m.commit s.term HwF Hcm' $$ HrF Hc
      iapply isCommitted_mono γ ((fp ++ s.log).take (uint.Z m.commit).toNat) (cprefix fp s)
        (take_prefix_le _ _ _ (Int.toNat_le_toNat Hcm')) $$ Hcm
    · ipureintro; exact Hid
  · ihave #Hc' := commitIn_committed γ _ _ _ $$ Hc
    icases snapOk_message γ id s m Hr Hsnap $$ Hc' Hrecs Hb with ⟨-, #Hmeta, %Hidx⟩
    obtain ⟨Hty, Hfrom, Hterm, -, -, Hle, -⟩ := Hsnap
    unfold isMessage
    rw [Hty]
    dsimp only
    rw [Hfrom, Hterm]
    isplitr; · iexact Hl
    isplitr; · iexact Hmeta
    isplitl
    · iexists s.base, s.log, fp
      isplitr; · iexact Hp
      isplitr; · ipureintro; exact Hidx
      isplitr; · iexact Hlf
      isplitr; · iapply commitIn_le γ _ s.commit m.index s.term HwF Hle $$ HrF Hc
      iapply isCommitted_mono γ ((fp ++ s.log).take (uint.Z m.index).toNat) (cprefix fp s)
        (take_prefix_le _ _ _ (Int.toNat_le_toNat Hle)) $$ Hcm
    · ipureintro; exact Hid

/-- A full log at its commit index has the history of an acknowledgement there, at any
term at least the commit fact's. -/
theorem hist_of_commit (γ : RaftElectionNames) (F : List raftpb.Entry) (c tm : w64) (B : Int) :
    PlogWf base0 F → uint.Z tm < B →
    ⊢ logRecs (GF := GF) γ base0 F -∗ commitIn γ F c tm -∗ hist γ F tm c B := by
  intro HwF HB
  iintro #HrF Hc
  unfold commitIn
  icases Hc with (%H0 | ⟨%t, %n, %G, #Hq, %Hc⟩)
  · unfold hist
    iintro %j %Hj
    exact absurd Hj (by omega)
  · ihave #Hq2 := Hq
    iunfold cq at Hq2
    icases Hq2 with ⟨%Hn, #Hfl, -⟩
    have HsG : (plogTermAt base0 G c).isSome :=
      full_term_at_some G c n (by rw [Hn]; rfl) Hc.1
    iapply hist_of_agree γ F G tm c B HwF HsG Hc.2.2 $$ HrF
    unfold okL
    by_cases Htt : t = tm
    · subst Htt
      ileft; iexists t
      isplitr; · ipureintro; omega
      iexact Hfl
    · iright; iexists t, n
      isplitr
      · ipureintro
        have : uint.Z t ≠ uint.Z tm := fun h => Htt (uint_Z_inj.mp h)
        omega
      iexact Hq

/-- An acknowledgement justified by the log, in full-log terms. -/
theorem ackAgree_full (γ : RaftElectionNames) (b : entryID) (es fp : List raftpb.Entry)
    (t i : w64) :
    FullOk b fp → uint.Z b.index' ≤ uint.Z i →
    ⊢ ackAgree (GF := GF) γ b es t i -∗
      ∃ X, leadFull γ t X ∗
        ⌜(plogTermAt base0 X i).isSome ∧
          plogTermAt base0 X i = plogTermAt base0 (fp ++ es) i⌝ := by
  intro Hf Hb
  unfold ackAgree
  iintro ⟨-, %ldr, %bL, %l, #Hp, %Hsq, %fpX, #Hpf⟩
  obtain ⟨Hs, Heq⟩ := Hsq
  ihave %HfX : ⌜FullOk bL fpX⌝ $$ []
  · iunfold lpfull at Hpf
    icases Hpf with ⟨%F0, -, -, %H⟩
    ipureintro; exact H.1
  iexists fpX ++ l
  isplitr
  · iapply leadFull_intro $$ Hp Hpf
  ipureintro
  obtain ⟨x, Hx⟩ := Option.isSome_iff_exists.mp Hs
  have HbL := (plogTermAt_some_range _ _ _ _ Hx).1
  rw [full_term_at bL fpX l i HfX HbL, full_term_at b fp es i Hf Hb]
  exact ⟨Hs, Heq⟩

/- A non-leader's own acknowledgement of its term above its commit index is justified by
its log. -/
/-- A node not yet voted in its term is in no winning quorum of it. -/
theorem vote_excl (γ : RaftElectionNames) (id : w64) (s : PState) (γv : GName)
    (voted : GMap w64 w64) (ldr : w64) (q : GSet w64) :
    γ.reVotes !! id = some γv → VoteHistOk voted s →
    ⊢ ghostMapAuth (GF := GF) γv (1 : Qp).half voted -∗ isWin γ ldr s.term q -∗
      ⌜s.vote = W64 0 → id ∉ q⌝ := by
  intro Hname Hhist
  iintro Ha Hw
  by_cases H0 : s.vote = W64 0
  · by_cases Hin : id ∈ q
    · iunfold isWin at Hw
      icases Hw with ⟨%γw, -, -, #Hq⟩
      ihave #Hf := BigSepM.bigSepM_lookup (Φ := fun v _ => isVote (GF := GF) γ v s.term ldr)
        ((GMap.elem_of_gset _ _).mp Hin) $$ Hq
      iunfold isVote at Hf
      icases Hf with ⟨%γv', %Hγv', Hf⟩
      rw [Hname] at Hγv'; cases Hγv'
      ihave %Hl := ghost_map_lookup $$ Ha Hf
      have H2 := Hhist.2
      simp only [H0, ite_true] at H2
      exact absurd (H2.symm.trans Hl) (by simp)
    · ipureintro; exact fun _ => Hin
  · ipureintro; exact fun H => absurd H H0

theorem ownLogGhost_ack_agree (γ : RaftElectionNames) (id : w64) (s : PState) (kl : Option w64)
    (i : w64) :
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗ isAcked γ id s.term i -∗
      ∀ (_ : s.role ≠ .leader ∧ uint.Z s.commit < uint.Z i),
        ackAgree γ s.base s.log s.term i := by
  unfold isAcked
  iintro H (%H0 | ⟨⟨%γa', %Hγa', #Hfrag⟩, -⟩)
  · iintro %Hr
    have := Hr.2
    exact absurd H0 (by have := uint_Z_nonneg s.commit; omega)
  · unfold ownLogGhost
    icases H with ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
    iNamed H
    rw [Haname] at Hγa'; cases Hγa'
    ihave %Hk := ghost_map_lookup $$ Hacks Hfrag
    iintro %Hr
    rw [acksOk_nl γ s acks Hr.1]
    ihave #Hk' := BigSepM.bigSepM_lookup (Φ := fun (k : w64 × w64) (_ : Unit) => ackOk (GF := GF) γ s k)
      Hk $$ Hacks_ok
    unfold ackOk
    iapply Hk' $$ %(⟨rfl, Hr.2⟩ : (s.term, i).1 = s.term ∧ uint.Z s.commit < uint.Z (s.term, i).2)

/-- Histories across a log change that keeps the log below `c`, puts a leader's log `Y`
(of a term in range) on `[c, L]`, and drops what is past `L` -- where the old log
disagreed with `Y` at some `k` in `[c, L]` (the cut of `Step.appAccept`, the snapshot
index of `Step.snapRestore`). -/
theorem hist_replace (γ : RaftElectionNames) (F F' Y : List raftpb.Entry) (t i T : w64)
    (B B' c : Int) (k L : w64) :
    B ≤ B' → uint.Z t ≤ uint.Z T → uint.Z T < B' →
    0 < uint.Z k → c ≤ uint.Z k ∧ uint.Z k ≤ uint.Z L →
    (∀ j : w64, uint.Z j < c → plogTermAt base0 F' j = plogTermAt base0 F j) →
    (∀ j : w64, c ≤ uint.Z j ∧ uint.Z j ≤ uint.Z L →
       plogTermAt base0 F' j = plogTermAt base0 Y j ∧ (plogTermAt base0 Y j).isSome) →
    plogTermAt base0 F k ≠ plogTermAt base0 Y k →
    (∀ j : w64, uint.Z L < uint.Z j → plogTermAt base0 F' j = none) →
    ⊢ leadFull (GF := GF) γ T Y -∗ hist γ F t i B -∗ hist γ F' t i B' := by
  intro HB Ht HT Hk0 Hk Hlow Hmid Hdiff Hhigh
  iintro #HY #Hh
  ihave #HokY : (∀ j', okL (GF := GF) γ t B' j' Y) $$ []
  · iintro %j'
    unfold okL
    ileft; iexists T
    isplitr; · ipureintro; omega
    iexact HY
  unfold hist
  iintro %j %Hj
  by_cases Hjc : uint.Z j < c
  · icases Hh $$ %j %Hj with (⟨%X, #HX, %Hs⟩ | ⟨%j', %X1, %X2, %Hj', #H1, #H2, %Hd⟩)
    · ileft; iexists X
      isplitr; · iapply okL_mono γ t B B' j X HB $$ HX
      ipureintro; rw [Hlow j Hjc]; exact Hs
    · iright; iexists j', X1, X2
      isplitr; · ipureintro; exact Hj'
      isplitr; · iapply okL_mono γ t B B' j' X1 HB $$ H1
      isplitr; · iapply okL_mono γ t B B' j' X2 HB $$ H2
      ipureintro; exact Hd
  · by_cases HjL : uint.Z j ≤ uint.Z L
    · obtain ⟨Heq, Hs⟩ := Hmid j ⟨by omega, HjL⟩
      ileft; iexists Y
      isplitr; · iapply HokY
      ipureintro; rw [Heq]; exact ⟨Hs, rfl⟩
    · iright
      have HsY := (Hmid k Hk).2
      icases Hh $$ %k %(⟨Hk0, by omega⟩ : 0 < uint.Z k ∧ uint.Z k ≤ uint.Z i) with
        (⟨%X, #HX, %Hs⟩ | ⟨%j', %X1, %X2, %Hj', #H1, #H2, %Hd⟩)
      · iexists k, X, Y
        isplitr; · ipureintro; omega
        isplitr; · iapply okL_mono γ t B B' k X HB $$ HX
        isplitr; · iapply HokY
        ipureintro; exact ⟨Hs.1, HsY, by rw [Hs.2]; exact Hdiff⟩
      · iexists j', X1, X2
        isplitr; · ipureintro; omega
        isplitr; · iapply okL_mono γ t B B' j' X1 HB $$ H1
        isplitr; · iapply okL_mono γ t B B' j' X2 HB $$ H2
        ipureintro; exact Hd

end ghost

end EtcdGrove
end Perennial
