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
module

public import Proof.go_etcd_io.raft.v3.Protocol.GhostState

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section ghost
variable [GooseExts]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-! ### The log ghost state across a step -/

/-- (Lean helper.) `acksOk` of a non-leader, and of a leader, unfolded. -/
private theorem acksOk_nl (γ : RaftNames) (s : PState) (acks : GMap (w64 × w64) Unit) :
    s.role ≠ .leader → acksOk (GF := GF) γ s acks = iprop([∗map] k ↦ _u ∈ acks, ackOk γ s k) := by
  intro H
  unfold acksOk
  split
  · contradiction
  · rfl

private theorem acksOk_l (γ : RaftNames) (s : PState) (acks : GMap (w64 × w64) Unit) :
    s.role = .leader → acksOk (GF := GF) γ s acks = iprop(True) := by
  intro H
  unfold acksOk
  rw [H]

/-- `acksOk` across a step that never lowers the term or the commit index and demotes a
leader only into a higher term. Within one term the caller says how a justification
survives the new log (`Hkeep`); across a term change there is nothing to keep: nothing
of the new term has been acknowledged yet (`AcksTerm`). -/
theorem acksOk_upd (γ : RaftNames) (s s' : PState) (acks : GMap (w64 × w64) Unit) :
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

theorem klOk_step (γ : RaftNames) (id : w64) (s s' : PState) (kl kl' : Option w64) :
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
private theorem leadLogOwn_nl (γ : RaftNames) (s : PState) (terms : GMap w64 TermRec) :
    s.role ≠ .leader → leadLogOwn (GF := GF) γ s terms = iprop(True) := by
  intro H
  unfold leadLogOwn
  split
  · contradiction
  · rfl

private theorem matchedOk_nl (γ : RaftNames) (id : w64) (s : PState) (fp : List EntryM) :
    s.role ≠ .leader → matchedOk (GF := GF) γ id s fp = iprop(True) := by
  -- PORT(durability stage II): proof (`matchedOk` takes the node and its full prefix (R3))
  sorry

theorem ownLogGhost_upd (γ : RaftNames) (id : w64) (s s' : PState) (kl kl' : Option w64) (W : DurMaps) :
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
    ⊢ ownLogGhost (GF := GF) γ id s kl W -∗
      □ (⌜s'.term = s.term⌝ -∗ ∀ i,
           ⌜uint.Z s'.commit < uint.Z i⌝ -∗
           ackAgree γ s.base s.log s.term i -∗
           ackAgree γ s'.base s'.log s.term i) -∗
      logRecs γ s'.base s'.log -∗
      □ (∀ fp, matchedOk γ id s fp -∗ matchedOk γ id s' fp) -∗
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
      ownLogGhost γ id s' kl' W := by
  -- PORT(durability stage II): proof (the body of `ownLogGhost` changed (durability I-1))
  sorry

theorem ownLogGhost_recs (γ : RaftNames) (id : w64) (s : PState) (kl : Option w64) (W : DurMaps) :
    ⊢ ownLogGhost (GF := GF) γ id s kl W -∗ ⌜LogOk s⌝ ∗ logRecs γ s.base s.log := by
  -- PORT(durability stage II): proof (the body of `ownLogGhost` changed (durability I-1))
  sorry

theorem ownLogGhost_wf (γ : RaftNames) (id : w64) (s : PState) (kl : Option w64) (W : DurMaps) :
    ⊢ ownLogGhost (GF := GF) γ id s kl W -∗ ⌜PlogWf s.base s.log⌝ := by
  -- PORT(durability stage II): proof (the body of `ownLogGhost` changed (durability I-1))
  sorry

theorem ownLogGhost_matched (γ : RaftNames) (id : w64) (s : PState) (kl : Option w64) (W : DurMaps) :
    ⊢ ownLogGhost (GF := GF) γ id s kl W -∗
      ∃ fp, ⌜FullOk s.base fp⌝ ∗ logRecs γ base0 fp ∗ matchedOk γ id s fp := by
  -- PORT(durability stage II): proof (`matchedOk` takes the node and its full prefix (R3))
  sorry

theorem ownLogGhost_base (γ : RaftNames) (id : w64) (s : PState) (kl : Option w64) (W : DurMaps) :
    ⊢ ownLogGhost (GF := GF) γ id s kl W -∗ baseOk γ s.base := by
  -- PORT(durability stage II): proof (the body of `ownLogGhost` changed (durability I-1))
  sorry

/-- The node's committed prefix, with the compacted prefix it is of. -/
theorem ownLogGhost_cmt (γ : RaftNames) (id : w64) (s : PState) (kl : Option w64) (W : DurMaps) :
    ⊢ ownLogGhost (GF := GF) γ id s kl W -∗
      ∃ fp, ⌜FullOk s.base fp⌝ ∗ logRecs γ base0 fp ∗ isCommitted γ (cprefix fp s) := by
  -- PORT(durability stage II): proof (the body of `ownLogGhost` changed (durability I-1))
  sorry

theorem ownLogGhost_inv (γ : RaftNames) (id : w64) (s : PState) (kl : Option w64) (W : DurMaps) :
    ⊢ ownLogGhost (GF := GF) γ id s kl W -∗ raftCommitInv γ := by
  -- PORT(durability stage II): proof (the body of `ownLogGhost` changed (durability I-1))
  sorry

/-- The compacted prefix is determined by the base (`FullOk_unique`), so a committed
prefix can be read with any compacted prefix that has records. -/
theorem cprefix_transfer (γ : RaftNames) (fp1 fp2 : List EntryM) (s : PState) :
    FullOk s.base fp1 → FullOk s.base fp2 →
    ⊢ logRecs (GF := GF) γ base0 fp1 -∗ logRecs γ base0 fp2 -∗
      isCommitted γ (cprefix fp1 s) -∗ isCommitted γ (cprefix fp2 s) := by
  intro H1 H2
  iintro #Hr1 #Hr2 #Hc
  icases FullOk_unique γ s.base fp1 fp2 H1 H2 $$ Hr1 Hr2 with %Heq
  subst Heq
  iexact Hc

omit [GooseExts] in
theorem take_prefix_le {A : Type _} (l : List A) (n m : Nat) :
    n ≤ m → l.take n <+: l.take m := by
  intro H
  have : l.take n = (l.take m).take n := by rw [List.take_take, Nat.min_eq_left H]
  rw [this]; exact List.take_prefix _ _

/-- A log that grows past the commit index keeps its committed prefix. -/
theorem cprefix_app (fp : List EntryM) (s : PState) (es : List EntryM) :
    uint.Z s.commit ≤ ((fp ++ s.log).length : Int) →
    (fp ++ s.log ++ es).take (uint.Z s.commit).toNat = cprefix fp s := by
  intro H
  unfold cprefix
  apply List.take_append_of_le_length
  omega

/-- Learning the leader of the term, from one of its messages: the bound goes up to the
term plus one. The caller supplies that the node is not in the winning quorum if it has
not voted (`vote_excl`). -/
theorem ownLogGhost_learn (γ : RaftNames) (id : w64) (s : PState) (kl : Option w64) (W : DurMaps)
    (ldr : w64) (q : GSet w64) :
    s.role ≠ .leader →
    ⊢ isWin (GF := GF) γ ldr s.term q -∗ ⌜s.vote = W64 0 → id ∉ q⌝ -∗
      ownLogGhost γ id s kl W -∗ ownLogGhost γ id s (some ldr) W := by
  -- PORT(durability stage II): proof (the body of `ownLogGhost` changed (durability I-1))
  sorry

/-- The same, for a step that leaves the log alone. The caller says how the commit fact
moves to the new commit index. -/
theorem ownLogGhost_mono' (γ : RaftNames) (id : w64) (s s' : PState)
    (kl kl' : Option w64) (W : DurMaps) :
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
    ⊢ ownLogGhost (GF := GF) γ id s kl W -∗ □ (∀ fp, matchedOk γ id s fp -∗ matchedOk γ id s' fp) -∗
      (∀ fp, ⌜FullOk s.base fp ∧ PlogWf s.base s.log⌝ -∗
         logRecs γ base0 fp -∗
         commitIn γ (fp ++ s.log) s.commit s.term -∗
         commitIn γ (fp ++ s.log) s'.commit s'.term) -∗
      (∀ fp, ⌜FullOk s.base fp ∧ PlogWf s.base s.log⌝ -∗
         logRecs γ base0 fp -∗
         isCommitted γ (cprefix fp s) -∗ isCommitted γ (cprefix fp s')) -∗
      ownLogGhost γ id s' kl' W := by
  -- PORT(durability stage II): proof (the body of `ownLogGhost` changed (durability I-1))
  sorry

/-- The same, when `Match` and the commit index do not change either, at the same
term ... -/
theorem ownLogGhost_mono (γ : RaftNames) (id : w64) (s s' : PState) (kl : Option w64) (W : DurMaps) :
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
    ⊢ ownLogGhost (GF := GF) γ id s kl W -∗ ownLogGhost γ id s' kl W := by
  -- PORT(durability stage II): proof (the body of `ownLogGhost` changed (durability I-1))
  sorry

/-- ... or at a higher term, where the known leader is forgotten. -/
theorem ownLogGhost_mono_up (γ : RaftNames) (id : w64) (s s' : PState) (kl : Option w64) (W : DurMaps) :
    s'.log = s.log →
    s'.base = s.base →
    s'.commit = s.commit →
    s'.role = .follower →
    uint.Z s.term < uint.Z s'.term →
    ⊢ ownLogGhost (GF := GF) γ id s kl W -∗ ownLogGhost γ id s' none W := by
  -- PORT(durability stage II): proof (the body of `ownLogGhost` changed (durability I-1))
  sorry

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
theorem ack_invs_insert (γ : RaftNames) (s : PState) (kl : Option w64)
    (F : List EntryM) (acks : GMap (w64 × w64) Unit)
    (vlogs : GMap Nat ((w64 × Bool) × List EntryM)) (i : w64) :
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
the history `histsOk` asks of it. (2026-10-31, durability stage I-1: the acknowledgement is a
pending promise, added to the virtual maps; its fragment, behind theirs, is what its message
carries until it is entered.) -/
theorem ownLogGhost_ack (γ : RaftNames) (id : w64) (s : PState) (kl : Option w64) (W : DurMaps)
    (i : w64) (Hnc : s.role ≠ .candidate)
    (Hli : s.role = .leader → uint.Z i ≤ plogLastIndexZ s.base s.log) :
    ⊢ ackOk (GF := GF) γ s (s.term, i) -∗
      (∀ fp, ⌜FullOk s.base fp ∧ PlogWf s.base s.log⌝ -∗
         logRecs γ base0 fp -∗
         commitIn γ (fp ++ s.log) s.commit s.term -∗
         hist γ (fp ++ s.log) s.term i (bnd s kl)) -∗
      ownLogGhost γ id s kl W -∗
      ownLogGhost γ id s kl (W.add (.ack s.term i)) ∗ promJust γ id W (.ack s.term i) ∗
      □ (durFrags γ id (W.add (.ack s.term i)) -∗ isAcked γ id s.term i) := by
  -- PORT(durability stage II): proof (restated: produces a pending `Prom.ack` (durability I-1))
  sorry

theorem pleaderEntry_term (s : PState) : (pleaderEntry s).Term' = s.term := rfl

/-- (Lean helper.) `leadLogOwn` and `campOwn` of a leader, unfolded. -/
private theorem leadLogOwn_l (γ : RaftNames) (s : PState) (terms : GMap w64 TermRec) :
    s.role = .leader → leadLogOwn (GF := GF) γ s terms =
      iprop(∃ γt, ∃ (M : GMap w64 (EntryM × w64)), ∃ l0,
        ⌜terms !! s.term = some ((γt, s.base), l0)⌝ ∗
        ghostMapAuth γt 1 M ∗
        ([∗map] i ↦ e ∈ M, i ↪[γt]□ e) ∗
        ⌜∀ i, (M !! i).isSome → uint.Z i ≤ plogLastIndexZ s.base s.log⌝ ∗
        ⌜l0 <+: s.log⌝ ∗
        leadFrags γt l0 s.log) := by
  intro H
  unfold leadLogOwn
  rw [H]

private theorem campOwn_l (γ : RaftNames) (id : w64) (camps : GMap w64 (List EntryM × w64))
    (s : PState) (F : List EntryM) :
    s.role = .leader → campOwn (GF := GF) γ id camps s F =
      iprop(∃ F0, isCamp γ id s.term F0 ∗
       ⌜F0 <+: F ∧ plogLastIndexZ base0 F0 < plogLastIndexZ base0 F ∧
         (plogLast base0 F).term' = s.term⌝) := by
  -- PORT(durability stage II): proof (`campOwn` takes the virtual campaign map)
  sorry

/-- A leader's whole log is a log of the leader of its term, with its full log and the
commit fact about it. -/
theorem ownLogGhost_lead_full (γ : RaftNames) (id : w64) (s : PState) (kl : Option w64) (W : DurMaps) :
    s.role = .leader →
    ⊢ isLeader (GF := GF) γ id s.term -∗ ownLogGhost γ id s kl W -∗
      (∃ fp, leadPrefix γ id s.term s.base s.log ∗
         lpfull γ id s.term s.base s.log fp ∗
         commitIn γ (fp ++ s.log) s.commit s.term) ∗
      ownLogGhost γ id s kl W := by
  -- PORT(durability stage II): proof (the body of `ownLogGhost` changed (durability I-1))
  sorry

/-- A leader stepping down at its term (2026-10-14, stage B5: `StepR.stepDown`): its term
log is dropped (`TermsOk`'s keys allow a non-candidate at its term); its acknowledgements of
its term, within its log (`LeadAcksOk`), are justified by its own prefix. -/
theorem ownLogGhost_stepDown (γ : RaftNames) (id : w64) (s s' : PState) (kl : Option w64) (W : DurMaps)
    (Hr : s.role = .leader) (Hr' : s'.role = .follower) (Hte : s'.term = s.term)
    (Hv : s'.vote = s.vote) (Hb : s'.base = s.base) (Hlg : s'.log = s.log)
    (Hc : s'.commit = s.commit) :
    ⊢ isLeader (GF := GF) γ id s.term -∗ ownLogGhost γ id s kl W -∗ ownLogGhost γ id s' kl W := by
  -- PORT(durability stage II): proof (the body of `ownLogGhost` changed (durability I-1))
  sorry

/-- A full log with records that starts with a non-empty bootstrap log has an entry of term `1`
at index `1`: a bound on its terms bounds `1` (2026-10-16, stage R8b, D12). -/
theorem boot_term_le (γ : RaftNames) (F : List EntryM) (T : w64) :
    PlogWf base0 F → γ.reBoot <+: F →
    (∀ (j x : w64), plogTermAt base0 F j = some x → uint.Z x ≤ uint.Z T) →
    ⊢ logRecs (GF := GF) γ base0 F -∗ ⌜γ.reBoot ≠ [] → 1 ≤ uint.Z T⌝ := by
  intro HwF Hbpre Htle
  iintro #HrF
  icases logRecs_boot_wf γ F HwF $$ HrF with %Hbw
  ipureintro
  intro Hne
  obtain ⟨-, Hones⟩ := Hbw Hbpre
  obtain ⟨e0, He0⟩ : ∃ e0, γ.reBoot[0]? = some e0 := by
    cases h : γ.reBoot with
    | nil => exact absurd h Hne
    | cons e0 _ => exact ⟨e0, rfl⟩
  have He0F := prefix_lookup_Some He0 Hbpre
  have Ht1 := plogTermAt_lookup base0 F (W64 1) 0 e0 He0F (by rw [base0_index]; rfl)
  have := Htle (W64 1) e0.Term' Ht1
  rw [Hones e0 (List.mem_of_getElem? He0)] at this
  rw [show uint.Z (W64 1) = 1 from rfl] at this
  omega

/-- The bootstrap log in a node's full log (2026-10-16, stage R8b, D12): the commit index is
past it (`ownLogGhost`'s conjunct), so, with the records, it is a prefix of the full log, and a
non-empty one puts the term at `≥ 1` (`TermsLe`). -/
theorem ownLogGhost_boot (γ : RaftNames) (id : w64) (s : PState) (kl : Option w64) (W : DurMaps) :
    ⊢ ownLogGhost (GF := GF) γ id s kl W -∗
      ⌜(γ.reBoot.length : Int) ≤ uint.Z s.commit ∧ (γ.reBoot ≠ [] → 1 ≤ uint.Z s.term)⌝ ∗
      ∃ fp, ⌜FullOk s.base fp ∧ γ.reBoot <+: fp ++ s.log⌝ ∗ logRecs γ base0 fp := by
  -- PORT(durability stage II): proof (the body of `ownLogGhost` changed (durability I-1))
  sorry

/-- `Step.campaign`, on the log ghost state: record the campaign log (the full log,
unchanged since) and, for the self-vote, the vote-time log -- with the histories of
every earlier acknowledgement; the new term has no known leader. (2026-10-31, durability stage
I-1: the campaign record and the self-vote are pending promises, `Prom.camp` and `Prom.vote`, the
latter's justification left to the caller, which has the vote's freshness.) -/
theorem ownLogGhost_campaign (γ : RaftNames) (id : w64) (s : PState) (kl : Option w64) (W : DurMaps) :
    s.role ≠ .leader →
    uint.Z s.term + 1 < 2 ^ 64 →
    ⊢ ownLogGhost (GF := GF) γ id s kl W -∗
      ∃ F, ⌜W.camps !! (s.term + W64 1) = none⌝ ∗
        ownLogGhost γ id (pbecomeCandidate id s) none
          (virt W [.camp (s.term + W64 1) F s.commit, .vote (s.term + W64 1) id false F]) ∗
        promJust γ id W (.camp (s.term + W64 1) F s.commit) ∗
        logRecs γ base0 F ∗
        ⌜PlogWf base0 F ∧ plogLast base0 F = plogLast s.base s.log⌝ ∗
        ([∗map] k ↦ _u ∈ W.acks, ∀ (_ : uint.Z k.1 < uint.Z (s.term + W64 1)),
          hist γ F k.1 k.2 (vbnd (s.term + W64 1) false)) ∗
        -- (2026-10-14, stage B5) the campaign log's prefix and commit justification
        (∃ fp, ⌜FullOk s.base fp ∧ F = fp ++ s.log⌝ ∗ logRecs γ base0 fp ∗
          commitIn γ F s.commit s.term) := by
  -- PORT(durability stage II): proof (restated: produces pending promises (durability I-1))
  sorry

/-- A first vote, on the log ghost state: record the vote-time log, which has the
histories of all acknowledgements, at the node's bound -- the term, or the term plus one
if it knows the term's leader. (2026-10-31, durability stage I-1: a pending `Prom.vote` for `c`,
with the histories its justification needs; the caller has the vote's freshness.) -/
theorem ownLogGhost_vote (γ : RaftNames) (id : w64) (s : PState) (kl : Option w64) (W : DurMaps)
    (c : w64) :
    ⊢ ownLogGhost (GF := GF) γ id s kl W -∗
      ∃ F, ownLogGhost γ id s kl (W.add (.vote s.term c kl.isSome F)) ∗
        logRecs γ base0 F ∗ klOk γ id s kl ∗
        ⌜PlogWf base0 F ∧
          ∀ x, plogUpToDate base0 F x = plogUpToDate s.base s.log x⌝ ∗
        ([∗map] k ↦ _u ∈ W.acks, ∀ (_ : uint.Z k.1 < uint.Z s.term),
          hist γ F k.1 k.2 (vbnd s.term kl.isSome)) := by
  -- PORT(durability stage II): proof (restated: produces a pending `Prom.vote` (durability I-1))
  sorry

omit [GooseExts] in
/-- (Lean helper.) The true branch of an `if` in a BI. -/
private theorem ite_pos_elim {PROP : Type _} [BI PROP] {c : Prop} [Decidable c] (P Q : PROP)
    (h : c) : (if c then P else Q) ⊢ P := by
  rw [ite_eq_left_iff.mpr (fun hn => absurd h hn)]

/-- (Lean helper.) One entry's record in a log with records, at any base. -/
private theorem logRecs_lookup_b (γ : RaftNames) (b : entryID) (es : List EntryM)
    (k : Nat) (e : EntryM) :
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
theorem snapOk_message (γ : RaftNames) (id : w64) (s : PState) (m : Msg) :
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
theorem replOk_message (γ : RaftNames) (id : w64) (s : PState) (m : Msg)
    (fp : List EntryM) :
    PlogWfR s.base s.log →
    ReplOk id s m → id ≠ W64 0 →
    -- (2026-10-14, stage B5) in the dynamic mode, an `MsgApp`'s I1 at its `Commit`
    (γ.reDyn ≠ none → m.ty = .app → ConfI1 (fp ++ s.log) (uint.Z m.commit).toNat) →
    -- (D19p, 2026-10-18) a snapshot's sender and receiver within the tracked bound
    (m.ty = .snap → ∀ T, γ.reTracked = some T → id ∈ T ∧ m.dst ∈ T) →
    ⊢ isLeader (GF := GF) γ id s.term -∗
      leadPrefix γ id s.term s.base s.log -∗
      lpfull γ id s.term s.base s.log fp -∗
      logRecs γ s.base s.log -∗
      commitIn γ (fp ++ s.log) s.commit s.term -∗
      baseOk γ s.base -∗
      isCommitted γ (cprefix fp s) -∗
      isMessage γ m := by
  intro Hr Hok Hid Hi1 Htr
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
      isplitr
      · iapply isCommitted_mono γ ((fp ++ s.log).take (uint.Z m.commit).toNat) (cprefix fp s)
          (take_prefix_le _ _ _ (Int.toNat_le_toNat Hcm')) $$ Hcm
      unfold dynOn
      by_cases hD : γ.reDyn = none
      · ileft; ipureintro; exact hD
      · iright; ipureintro; exact Hi1 hD Hty
    · ipureintro; exact Hid
  · ihave #Hc' := commitIn_committed γ _ _ _ $$ Hc
    icases snapOk_message γ id s m Hr Hsnap $$ Hc' Hrecs Hb with ⟨-, #Hmeta, %Hidx⟩
    obtain ⟨Hty, Hfrom, Hterm, Hdst, -, Hle, -⟩ := Hsnap
    have Htr' := Htr Hty
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
    isplitr
    · ipureintro; exact Hid
    ipureintro; exact ⟨Hdst, Htr'⟩

/-- A full log at its commit index has the history of an acknowledgement there, at any
term at least the commit fact's. -/
theorem hist_of_commit (γ : RaftNames) (F : List EntryM) (c tm : w64) (B : Int) :
    PlogWf base0 F → uint.Z tm < B →
    ⊢ logRecs (GF := GF) γ base0 F -∗ commitIn γ F c tm -∗ hist γ F tm c B := by
  intro HwF HB
  iintro #HrF #Hc
  ihave #Hcj := commitIn_j γ F c tm $$ Hc
  unfold commitJ
  icases Hcj with (%H0 | ⟨%t, %n, %G, #Hq, %Hc⟩)
  · -- the boot arm (2026-10-16, stage R8b): the history names the bootstrap log
    obtain ⟨Hcb, Hct⟩ := H0
    have HsB : (plogTermAt base0 γ.reBoot c).isSome :=
      plogTermAt_in_range _ _ _ ⟨by rw [base0_index]; exact uint_Z_nonneg c, by
        unfold plogLastIndexZ; rw [base0_index]; omega⟩
    iapply hist_of_agree γ F γ.reBoot tm c B HwF HsB Hct $$ HrF
    unfold okL
    iright; iright; ipureintro; exact ⟨Hcb, rfl⟩
  · icases cq_base γ t n G $$ Hq with ⟨%Hn, #Hfl⟩
    have HsG : (plogTermAt base0 G c).isSome :=
      full_term_at_some G c n (by rw [Hn]; rfl) Hc.1
    iapply hist_of_agree γ F G tm c B HwF HsG Hc.2.2 $$ HrF
    unfold okL
    by_cases Htt : t = tm
    · subst Htt
      ileft; iexists t
      isplitr; · ipureintro; omega
      iexact Hfl
    · iright; ileft; iexists t, n
      isplitr
      · ipureintro
        have : uint.Z t ≠ uint.Z tm := fun h => Htt (uint_Z_inj.mp h)
        omega
      iexact Hq

/-- An acknowledgement justified by the log, in full-log terms. -/
theorem ackAgree_full (γ : RaftNames) (b : entryID) (es fp : List EntryM)
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
/-- A node not yet voted in its term is in no winning quorum of it. (2026-10-31, durability R2:
through the slot invariant's entered votes, which the virtual maps extend.) -/
theorem vote_excl (E : CoPset) (γ : RaftNames) (id : w64) (s : PState) (γs : SlotNames)
    (V : DurMaps) (πc : List Prom) (ldr : w64) (q : GSet w64) :
    γ.reSlot !! id = some γs → ↑(slotN γ id) ⊆ E → VoteHistOk (virt V πc).voted s →
    ⊢ slotInv (GF := GF) γ id -∗ ghostVar γs.1 (1 : Qp).half V -∗ isWin γ ldr s.term q ={E}=∗
      ghostVar γs.1 (1 : Qp).half V ∗ ⌜s.vote = W64 0 → id ∉ q⌝ := by
  -- PORT(durability stage II): proof (restated: a lookup in the slot (durability R2))
  sorry

/-- A non-leader's own acknowledgement of its term above its commit index agrees with its log.
(2026-10-31, durability R2: the fragment is an entered one, found through the slot.) -/
theorem ownLogGhost_ack_agree (E : CoPset) (γ : RaftNames) (id : w64) (s : PState)
    (kl : Option w64) (γs : SlotNames) (V : DurMaps) (πc : List Prom) (i : w64) :
    γ.reSlot !! id = some γs → ↑(slotN γ id) ⊆ E →
    ⊢ slotInv (GF := GF) γ id -∗ ghostVar γs.1 (1 : Qp).half V -∗
      ownLogGhost γ id s kl (virt V πc) -∗ isAcked γ id s.term i ={E}=∗
      ghostVar γs.1 (1 : Qp).half V ∗ ownLogGhost γ id s kl (virt V πc) ∗
      ∀ (_ : s.role ≠ .leader ∧ uint.Z s.commit < uint.Z i),
        ackAgree γ s.base s.log s.term i := by
  -- PORT(durability stage II): proof (restated: a lookup in the slot (durability R2))
  sorry

/-- Histories across a log change that keeps the log below `c`, puts a leader's log `Y`
(of a term in range) on `[c, L]`, and drops what is past `L` -- where the old log
disagreed with `Y` at some `k` in `[c, L]` (the cut of `Step.appAccept`, the snapshot
index of `Step.snapRestore`). -/
theorem hist_replace (γ : RaftNames) (F F' Y : List EntryM) (t i T : w64)
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
