/-
# Entering a batch, restarting and stopping a node (2026-10-31, durability stage I-1)

`notes/raft-durability-proof-plan.md`, I-1, as amended by its review 1. The lemmas that move a
node's promises between its volatile half (`ownRaftGhost`), its slot (`slotInv`, `raftIdSlot`) and its
durable half (`ownDurGhost`, `raftState`'s sealed body), all defined in `Protocol/GhostState.lean`:

- `ownRaftGhost_cut`, at a `Ready`: the outbox drained (as `ownRaftGhost_drain`), the promises made
  since the last cut queued in the slot as a batch entering `S'` (`pendBatch`), the drained
  messages' facts behind the batch's fragments.
- `raft_enter`, when the client enters the batch: its promises minted in the authorities, the
  durable half moved to `S'`, the batch's fragments out (which release the drained messages).
- `raft_restart`, `raft_start_boot`: a node's volatile half built from the durable half and the
  vacant slot (R8: the durable half given back), at a restart from storage at a base `b` and commit
  `c` (`restartP`), or at a cluster's bootstrap (`bootPState`).
- `raft_stop`: the volatile half and the whole generation give back the vacant slot, the
  generation bumped (R8), so that a batch cut and not entered is dead.
- R4's restart lemmas: `S.commit`'s certificate at a lower stored commit, and the agreement of the
  acknowledgements of `S.term` above it, from Leader Completeness.

Statements only: the proofs are stage II's (`-- PORT(durability stage II)`).
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.Facts

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section enter
variable [GooseExts]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- The slot invariant is inside raft's namespace. -/
theorem slotN_raftN (γ : RaftNames) (id : w64) : (↑(slotN γ id) : CoPset) ⊆ ↑(raftN γ) :=
  fun p hp => nclose_subseteq (raftN γ) "slot" p (nclose_subseteq _ _ p hp)

/-- The slot invariant opens inside a ghost step (the commit invariant's registry half open). -/
theorem slotN_sub (γ : RaftNames) (id : w64) :
    (↑(slotN γ id) : CoPset) ⊆ ⊤ \ ↑(raftRegN γ) :=
  slotN_sub_reg

/-- (stage II helper) One entry's record out of `logRecs`. -/
private theorem logRecs_elem' (γ : RaftNames) (b : entryID) (es : List EntryM)
    (k : Nat) (x : EntryM) :
    es[k]? = some x → uint.Z b.index' + (k : Int) + 1 < 2 ^ 64 →
    logRecs (GF := GF) γ b es ⊢ ∃ pt, ⌜plogTermAt b es (pidx b k) = some pt⌝ ∗ isEntryR γ x pt := by
  intro Hk Hr
  unfold logRecs
  refine (BigSepL.bigSepL_lookup (Φ := fun k e =>
    if uint.Z b.index' + (k : Int) + 1 < 2 ^ 64
    then iprop(∃ pt, ⌜plogTermAt b es (pidx b k) = some pt⌝ ∗ isEntryR (GF := GF) γ e pt)
    else iprop(True)) Hk).trans ?_
  simp only [Hr, ↓reduceIte]
  exact .rfl

/-- (stage II helper) `logRecs` from each in-range entry's record. -/
private theorem logRecs_intro' (γ : RaftNames) (b : entryID) (es : List EntryM) :
    ⊢ □ (∀ (k : Nat) (x : EntryM),
          ⌜es[k]? = some x ∧ uint.Z b.index' + (k : Int) + 1 < 2 ^ 64⌝ →
          ∃ pt, ⌜plogTermAt b es (pidx b k) = some pt⌝ ∗ isEntryR (GF := GF) γ x pt) -∗
      logRecs γ b es := by
  iintro #H
  unfold logRecs
  iapply BigSepL.bigSepL_forall_elim
  iintro %k %x Hk
  ipure Hk
  split
  · rename_i Hr
    iapply H $$ %k %x
    ipureintro; exact ⟨Hk, Hr⟩
  · itrivial

/-- (stage II helper) The records of a full log's suffix after its first `m` entries, at the base
`b` of that prefix. -/
theorem logRecs_drop (γ : RaftNames) (F : List EntryM) (b : entryID) (m : Nat) :
    FullOk b (F.take m) → uint.Z b.index' = m →
    ⊢ logRecs (GF := GF) γ base0 F -∗ logRecs γ b (F.drop m) := by
  intro Hfull Hbm
  iintro #H
  iapply logRecs_intro'
  imodintro
  iintro %k %x %Hk
  obtain ⟨Hk, Hr⟩ := Hk
  rw [List.getElem?_drop] at Hk
  have Hr' : uint.Z (base0 : entryID).index' + ((m + k : Nat) : Int) + 1 < 2 ^ 64 := by
    rw [base0_index]; push_cast; omega
  ihave ⟨%pt, %Hpt, #He⟩ := logRecs_elem' γ base0 F (m + k) x Hk Hr' $$ H
  iexists pt; iframe He; ipureintro
  have Hlt : (m : Int) + k < 2 ^ 64 := by omega
  have Hp : pidx b k = pidx base0 (m + k) := by
    unfold pidx; rw [base0_index, Hbm]; congr 1; push_cast; omega
  have Hj : uint.Z b.index' ≤ uint.Z (pidx base0 (m + k)) := by
    unfold pidx; rw [base0_index, Hbm]
    rw [uint_Z_W64 _ (by push_cast; omega) (by push_cast; omega)]; push_cast; omega
  rw [Hp, ← full_term_at b (F.take m) (F.drop m) _ Hfull Hj, List.take_append_drop]
  exact Hpt

/-- The state a node restarts in from a storage holding `S` from the base `b` with the commit
index `c`: a follower of `S.term`, with `S`'s vote, no leader, an empty tally and outbox. -/
def restartP (S : RaftState) (b : entryID) (c : w64) : PState :=
  { initPState with term := S.term, vote := S.vote, base := b, log := S.entsFrom b, commit := c }

/-- **The cut** (at a `Ready`, `InvRawnodeReady`'s handout, beside `ownRaftGhost_drain`): the outbox
drained to `o'`, its messages `out` with their read credits and tickets, and the promises made since
the last cut queued in generation `g`'s free slot, as a batch entering `S'` -- the cut state's term,
vote and commit, its full log (`DurFull`, given the node's full prefix `fp`) -- with the node's
virtual maps `W`, behind whose fragments the drained messages' facts are. -/
theorem ownRaftGhost_cut (E : CoPset) (γ : RaftNames) (id : w64) (s : PState) {md : Bool}
    (q : Qp) (g : Nat) (S' : RaftState) (o' out : List Msg) :
    ↑(slotN γ id) ⊆ E →
    (o' ++ out).Perm s.outbox →
    S'.term = s.term → S'.vote = s.vote → S'.commit = s.commit →
    ⊢ (□ ∀ fp, ⌜FullOk s.base fp⌝ -∗ logRecs (GF := GF) γ base0 fp -∗ ⌜DurFull S' (fp ++ s.log)⌝) -∗
      slotLive γ id q g -∗ slotFree γ id g -∗ ownRaftGhost γ id s md ={E}=∗
      slotLive γ id q g ∗ ∃ W, pendBatch γ id g S' W ∗
        ownRaftGhost γ id { s with outbox := o' } md ∗
        ([∗list] m ∈ out, □ (durFrags γ id W -∗ isMessage γ m)) ∗
        rdCred γ (rdCount s.outbox - rdCount o') ∗ msgsTks γ out := by
  -- PORT(durability stage II): proof (new lemma)
  sorry

/-- **Entering a batch** (the client's *enter*, under the node's generation): its promises minted
in order in the authorities (`vote_insert`, `ghost_map_insert_persist` of the acknowledgements,
campaign records and vote-time logs, the event history's appends), from their justifications; the
durable half moved to the batch's state; the batch's fragments out, which discharge its drained
messages' wands; the generation's queue free again. -/
theorem raft_enter (E : CoPset) (γ : RaftNames) (id : w64) (S : RaftState) (q : Qp) (g : Nat)
    (S' : RaftState) (W : DurMaps) :
    ↑(raftN γ) ⊆ E →
    ⊢ ownDurGhost (GF := GF) γ id S -∗ slotLive γ id q g -∗ pendBatch γ id g S' W ={E}=∗
      ownDurGhost γ id S' ∗ slotLive γ id q g ∗ slotFree γ id g ∗ durFrags γ id W := by
  -- PORT(durability stage II): proof (new lemma)
  sorry

/-- (stage II helper) **`durPers` re-based** at a base `b` within `S`'s log and a lower commit `c`:
the same full log, cut at `b` (`fp ++ S.entsFrom b`), with `S.commit`'s certificate lowered to `c`
(R4's first half), and the rest of the durable invariants unchanged. -/
theorem durPers_rebase (γ : RaftNames) (id : w64) (S : RaftState) (Ed : DurMaps)
    (b : entryID) (c : w64) :
    uint.Z S.base.index' ≤ uint.Z b.index' → uint.Z b.index' ≤ uint.Z c →
    uint.Z c ≤ uint.Z S.commit →
    plogTermAt S.base S.ents b.index' = some b.term' →
    ⊢ durPers (GF := GF) γ id S Ed -∗
      ∃ (kd : Option w64) (fp : List EntryM),
        ⌜VoteHistOkD Ed.voted S ∧
          (∀ k, (Ed.acks !! k).isSome → uint.Z k.1 ≤ uint.Z S.term) ∧
          (∀ T, (Ed.camps !! T).isSome → uint.Z T ≤ uint.Z S.term) ∧
          EvsOk S.term Ed ∧
          FullOk b fp ∧ PlogWf b (S.entsFrom b) ∧
          (∀ (j x : w64), plogTermAt base0 (fp ++ S.entsFrom b) j = some x →
            uint.Z x ≤ uint.Z S.term) ∧
          uint.Z c ≤ plogLastIndexZ b (S.entsFrom b)⌝ ∗
        logRecs γ b (S.entsFrom b) ∗ baseOk γ b ∗ logRecs γ base0 fp ∗
        ([∗map] x ∈ Ed.vlogs, ⌜uint.Z x.1.1 ≤ uint.Z S.term⌝ ∗
          [∗map] k ↦ _u ∈ Ed.acks, ∀ (_ : uint.Z k.1 < uint.Z x.1.1),
            hist γ x.2 k.1 k.2 (vbnd x.1.1 x.1.2)) ∗
        ([∗map] k ↦ _u ∈ Ed.acks, hist γ (fp ++ S.entsFrom b) k.1 k.2 (bndD S kd)) ∗
        klOkD γ id S kd ∗
        commitIn γ (fp ++ S.entsFrom b) c S.term ∗
        isCommitted γ ((fp ++ S.entsFrom b).take (uint.Z c).toNat) ∗
        raftCommitInv γ := by
  intro Hb1 Hb2 Hb3 Hbt
  iintro #Hd
  unfold durPers
  icases Hd with ⟨%kd, %fp0, %Hp, #HrS, -, #Hfp0, #Hvl, #Hhs, #Hkl, -, #Hci, #Hc, #Hinv⟩
  obtain ⟨Hvh, Hak, Hcp, Hev, HfullS, HwfS, Hterms, -, HcL⟩ := Hp
  have HwfF : PlogWf base0 (fp0 ++ S.ents) := full_wf _ _ _ HfullS HwfS
  ihave #HrF := logRecs_full γ S.base fp0 S.ents HfullS $$ Hfp0 HrS
  have Hbt' : plogTermAt base0 (fp0 ++ S.ents) b.index' = some b.term' := by
    rw [full_term_at _ _ _ _ HfullS Hb1]; exact Hbt
  have HlastF : plogLastIndexZ base0 (fp0 ++ S.ents) = plogLastIndexZ S.base S.ents :=
    full_last_index _ _ _ HfullS
  generalize HF : fp0 ++ S.ents = F at HwfF Hbt' Hterms HlastF
  have HbZ := uint_Z_nonneg b.index'
  obtain ⟨m, Hm⟩ : ∃ m : Nat, (m : Int) = uint.Z b.index' := ⟨_, Int.toNat_of_nonneg HbZ⟩
  have HfB : FullOk b (F.take m) := by
    have := FullOk_take F b.term' b.index' HwfF Hbt'
    rw [show (uint.Z b.index').toNat = m by omega] at this
    cases b; exact this
  have Hlen0 : (fp0.length : Int) = uint.Z S.base.index' := HfullS.1
  have Hdrop : F.drop m = S.entsFrom b := by
    unfold RaftState.entsFrom
    rw [← HF, List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append]
    congr 1; omega
  have Hfeq : F.take m ++ S.entsFrom b = F := by rw [← Hdrop, List.take_append_drop]
  have Hwfb : PlogWf b (S.entsFrom b) := by
    rw [← Hdrop]
    intro k e Hk
    rw [List.getElem?_drop] at Hk
    have := HwfF _ _ Hk
    rw [base0_index] at this
    push_cast at this ⊢; omega
  have HlenTake : (F.take m).length = m := by
    have := HfB.1; rw [← Hm] at this; omega
  have Hlastb : plogLastIndexZ b (S.entsFrom b) = plogLastIndexZ base0 F := by
    rw [← full_last_index b (F.take m) (S.entsFrom b) HfB, Hfeq]
  iexists kd, F.take m
  rw [Hfeq]
  isplitr
  · ipureintro
    refine ⟨Hvh, Hak, Hcp, Hev, HfB, Hwfb, Hterms, ?_⟩
    rw [Hlastb, HlastF]; omega
  isplitr
  · rw [← Hdrop]; iapply logRecs_drop γ F b m HfB Hm.symm $$ HrF
  isplitr
  · unfold baseOk
    by_cases H0 : uint.Z b.index' = 0
    · ileft; ipureintro; exact H0
    · iright
      obtain ⟨e, He, Hei, Het⟩ := plogTermAt_some_entry base0 F b.index' b.term'
        (PlogWf_wfR _ _ HwfF) Hbt' (by rw [base0_index]; omega)
      rw [base0_index] at He
      ihave ⟨%pt, -, #Her⟩ := logRecs_lookup γ F _ e He
        (by have := uint_Z_lt b.index'; omega) $$ HrF
      unfold isSnapMeta
      iexists e
      isplitr
      · unfold isEntry; iexists pt; iexact Her
      ipureintro; exact ⟨Het, Hei⟩
  isplitr; · iapply logRecs_take γ F m $$ HrF
  iframe Hvl Hhs Hkl Hinv
  isplitr
  · iapply commitIn_le γ F S.commit c S.term HwfF Hb3 $$ HrF Hci
  · iapply isCommitted_mono γ (F.take (uint.Z c).toNat) (F.take (uint.Z S.commit).toNat)
      (List.take_prefix_take_left (by omega)) $$ Hc

/-- **R4, the commit at a restart**: `S.commit`'s certificate gives one of a lower stored commit
`c` at a base `b` within `S`'s log, at `S.term` (in `S`'s full log, as the restarted node's). -/
theorem durPers_restart_commit (γ : RaftNames) (id : w64) (S : RaftState) (Ed : DurMaps)
    (b : entryID) (c : w64) :
    uint.Z S.base.index' ≤ uint.Z b.index' → uint.Z b.index' ≤ uint.Z c →
    uint.Z c ≤ uint.Z S.commit →
    plogTermAt S.base S.ents b.index' = some b.term' →
    ⊢ durPers (GF := GF) γ id S Ed -∗
      ∃ fp, ⌜FullOk b fp⌝ ∗ logRecs γ base0 fp ∗ logRecs γ b (S.entsFrom b) ∗ baseOk γ b ∗
        commitIn γ (fp ++ S.entsFrom b) c S.term ∗
        isCommitted γ ((fp ++ S.entsFrom b).take (uint.Z c).toNat) := by
  intro Hb1 Hb2 Hb3 Hbt
  iintro #Hd
  icases durPers_rebase γ id S Ed b c Hb1 Hb2 Hb3 Hbt $$ Hd with
    ⟨%kd, %fp, %Hp, #Hr, #Hb, #Hfp, -, -, -, #Hci, #Hc, -⟩
  iexists fp
  iframe Hr Hb Hfp Hci Hc
  ipureintro; exact Hp.2.2.2.2.1

/-- **R4, the acknowledgements at a restart**: every acknowledgement of `S.term` above a lower
stored commit `c` agrees with the restarted log -- above `S.commit` by `durPers`, in
`(c, S.commit]` by Leader Completeness (the committed prefix is in the log of `S.term`'s leader,
whose log the acknowledgement's `ackIn` names). -/
theorem durPers_restart_acks (E : CoPset) (γ : RaftNames) (id : w64) (S : RaftState) (Ed : DurMaps)
    (b : entryID) (c : w64) :
    ↑(raftN γ) ⊆ E →
    uint.Z S.base.index' ≤ uint.Z b.index' → uint.Z b.index' ≤ uint.Z c →
    uint.Z c ≤ uint.Z S.commit →
    plogTermAt S.base S.ents b.index' = some b.term' →
    ⊢ durPers (GF := GF) γ id S Ed -∗ durFrags γ id Ed ={E}=∗
      [∗map] k ↦ _u ∈ Ed.acks, ∀ (_ : k.1 = S.term ∧ uint.Z c < uint.Z k.2),
        ackAgree γ b (S.entsFrom b) k.1 k.2 := by
  -- PORT(durability stage II): proof (new lemma)
  sorry

/-- (stage II helper) -/
instance durFrags_timeless (γ : RaftNames) (id : w64) (W : DurMaps) :
    Timeless (durFrags (GF := GF) γ id W) := by
  unfold durFrags; infer_instance

/-- (stage II helper) Two ghost map authorities agree, kept. -/
private theorem auth_agree_keep {K V : Type} [DecidableEq K] [Pos.Countable K] [Pos.Countable V]
    (γm : GName) (q1 q2 : Qp) (m1 m2 : GMap K V) :
    iprop(ghostMapAuth (GF := GF) γm q1 m1 ∗ ghostMapAuth γm q2 m2) ⊢
      iprop(ghostMapAuth (GF := GF) γm q1 m1 ∗ ghostMapAuth γm q2 m2) ∗ ⌜m1 = m2⌝ :=
  persistent_entails_left (by iintro ⟨H1, H2⟩; iapply ghostMapAuth_agree $$ H1 H2)

/-- (stage II helper) Two event-history authorities agree, kept. -/
private theorem evs_agree_keep (γe : GName) (q1 q2 : Qp) (l1 l2 : List Aev) :
    iprop(monoListAuthOwn (GF := GF) γe q1 l1 ∗ monoListAuthOwn γe q2 l2) ⊢
      iprop(monoListAuthOwn (GF := GF) γe q1 l1 ∗ monoListAuthOwn γe q2 l2) ∗ ⌜l1 = l2⌝ :=
  persistent_entails_left (by
    iintro ⟨H1, H2⟩
    ihave %H := monoListAuthOwn_agree _ _ _ _ _ $$ H1 H2
    ipureintro; exact H.2)

/-- (stage II helper) Two shares of a node's promise authorities are at the same maps. -/
theorem durShares_agree (γ : RaftNames) (id : w64) (q1 q2 : Qp) (E1 E2 : DurMaps) :
    ⊢ durShares (GF := GF) γ id q1 E1 -∗ durShares γ id q2 E2 -∗
      durShares γ id q1 E1 ∗ durShares γ id q2 E2 ∗ ⌜E1 = E2⌝ := by
  unfold durShares
  iintro ⟨%γv, %γa, %γc, %γl, %γe, %Hn, Hv, Ha, Hc, Hl, He⟩
    ⟨%γv', %γa', %γc', %γl', %γe', %Hn', Hv', Ha', Hc', Hl', He'⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := Hn
  obtain ⟨h1', h2', h3', h4', h5'⟩ := Hn'
  rw [h1] at h1'; rw [h2] at h2'; rw [h3] at h3'; rw [h4] at h4'; rw [h5] at h5'
  cases h1'; cases h2'; cases h3'; cases h4'; cases h5'
  icases auth_agree_keep γv _ _ E1.voted E2.voted $$ [$Hv $Hv'] with ⟨⟨Hv, Hv'⟩, %E1v⟩
  icases auth_agree_keep γa _ _ E1.acks E2.acks $$ [$Ha $Ha'] with ⟨⟨Ha, Ha'⟩, %E1a⟩
  icases auth_agree_keep γc _ _ E1.camps E2.camps $$ [$Hc $Hc'] with ⟨⟨Hc, Hc'⟩, %E1c⟩
  icases auth_agree_keep γl _ _ E1.vlogs E2.vlogs $$ [$Hl $Hl'] with ⟨⟨Hl, Hl'⟩, %E1l⟩
  icases evs_agree_keep γe _ _ E1.evs E2.evs $$ [$He $He'] with ⟨⟨He, He'⟩, %E1e⟩
  isplitl [Hv Ha Hc Hl He]
  · iexists γv, γa, γc, γl, γe
    iframe Hv Ha Hc Hl He
    ipureintro; exact ⟨h1, h2, h3, h4, h5⟩
  isplitl
  · iexists γv, γa, γc, γl, γe
    iframe Hv' Ha' Hc' Hl' He'
    ipureintro; exact ⟨h1, h2, h3, h4, h5⟩
  ipureintro
  cases E1; cases E2
  simp only at E1v E1a E1c E1l E1e
  subst E1v E1a E1c E1l E1e; rfl

/-- (stage II helper) Every key of a map whose fragments carry `campKey` is an entered campaign's
term. -/
theorem keys_camps {V : Type} (γ : RaftNames) (id : w64) (q : Qp) (E : DurMaps)
    (Φ : w64 → V → IProp GF) :
    ∀ m : GMap w64 V,
      durShares (GF := GF) γ id q E ∗ ([∗map] t ↦ x ∈ m, Φ t x ∗ campKey γ id t) ⊢
        durShares γ id q E ∗ ⌜∀ t, (m !! t).isSome → (E.camps !! t).isSome⌝ := by
  intro m
  induction m using GMap.map_ind with
  | h0 =>
    iintro ⟨H, -⟩
    iframe H
    ipureintro; intro t h; simp at h
  | hins k v m Hk IH =>
    iintro ⟨Hsh, Hm⟩
    icases (BigSepM.bigSepM_insert (Φ := fun t x => iprop(Φ t x ∗ campKey (GF := GF) γ id t)) Hk).1
      $$ Hm with ⟨⟨-, Hck⟩, Hm⟩
    iunfold campKey at Hck
    icases Hck with ⟨%F, %kk, Hck⟩
    iunfold isCampK at Hck
    icases Hck with ⟨%γc, %Hc, #Hf, -⟩
    icases durShares_camp γ id q E γc k F kk Hc.1 $$ Hsh Hf with ⟨%HE, Hsh⟩
    icases IH $$ [Hsh Hm] with ⟨Hsh, %HIH⟩
    · iframe Hsh; iexact Hm
    iframe Hsh
    ipureintro
    intro t ht
    by_cases htk : k = t
    · subst htk; rw [HE]; rfl
    · rw [GMap.lookup_insert_ne _ _ htk] at ht
      exact HIH t ht

/-- (stage II helper) A key bounded by the entered campaigns, at a follower of `S.term`. -/
private theorem key_ok_follower (S : RaftState) (E : DurMaps) (s : PState) (t : w64) :
    (∀ T, (E.camps !! T).isSome → uint.Z T ≤ uint.Z S.term) → s.term = S.term →
    s.role = .follower → (E.camps !! t).isSome →
    uint.Z t < uint.Z s.term ∨ (t = s.term ∧ s.role ≠ .candidate) := by
  intro Hc Ht Hr Hs
  have := Hc t Hs
  rw [Ht, Hr]
  by_cases h : uint.Z t < uint.Z S.term
  · left; exact h
  · right; exact ⟨uint_Z_inj.mp (by omega), by decide⟩

/-- **A restart** (in `RestartNode`, when its update fires; R8: the durable half given back,
unchanged): the vacant slot and the durable half at `S` give the volatile half of a follower of
`S.term` restarted from a storage holding `S` from the base `b` with the commit `c`
(`restartP`: `kl` forgotten, the durable `kd` taken; an empty outbox and tally), with the whole
generation and its free queue slot. Amendment 1: the bootstrap log within the stored commit. -/
theorem raft_restart (E : CoPset) (γ : RaftNames) (id : w64) (S : RaftState) {md : Bool}
    (b : entryID) (c : w64) :
    ↑(raftN γ) ⊆ E →
    γ.reDyn.isSome = md →
    uint.Z S.base.index' ≤ uint.Z b.index' → uint.Z b.index' ≤ uint.Z c →
    uint.Z c ≤ uint.Z S.commit →
    plogTermAt S.base S.ents b.index' = some b.term' →
    (γ.reBoot.length : Int) ≤ uint.Z c →
    ⊢ ownDurGhost (GF := GF) γ id S -∗ raftIdSlot γ id ={E}=∗
      ownDurGhost γ id S ∗ ownRaftGhost γ id (restartP S b c) md ∗
      ∃ g, slotLive γ id 1 g ∗ slotFree γ id g := by
  intro HE Hmd Hb1 Hb2 Hb3 Hbt Hboot
  iintro Hdur Hslot
  unfold ownDurGhost
  icases Hdur with ⟨%E1, Hsh1, #Hdp⟩
  unfold raftIdSlot
  icases Hslot with ⟨%γs, %V, %g, %Hγs, %Hnz, Hvirt, Hlive, Hfree, #Hsinv, #Hcinv, #Hrci,
    ⟨%γm, %terms, %Htm, Hterms, #Htf⟩, ⟨%γw, %wins, %Hwn, Hwins, #Hwf⟩,
    ⟨%γl, %lcm, %Hln, Hlcm, #Hlf⟩, ⟨%γq, %rqm, %Hqn, Hrqm, #Hqf⟩⟩
  iunfold slotLive at Hlive
  icases Hlive with ⟨%γs1, %H1, Hl⟩
  rw [Hγs] at H1; cases H1
  iunfold slotFree at Hfree
  icases Hfree with ⟨%γs2, %H2, Hfr⟩
  rw [Hγs] at H2; cases H2
  -- the slot: the queue is free, so the virtual half is the entered maps, the durable half's
  have HsE : (↑(slotN γ id) : CoPset) ⊆ E := fun p hp => HE p (slotN_raftN γ id p hp)
  ihave #Hsi := Hsinv
  iunfold slotInv at Hsi
  iinv Hsi with H Hclose
  iunfold slotBody at H
  icases H with ⟨%γs', %E0, %g0, %Mq, >%Hγs', >Hsh0, #>Hfr0, >Hv0, >Hg0, >Hq, >%Hdom, >%Hcur, Hb⟩
  rw [Hγs] at Hγs'; cases Hγs'
  icombine Hl Hg0 gives %Hgg
  obtain ⟨-, Hgg⟩ := Hgg
  subst Hgg
  icombine Hq Hfr gives %HMq
  icombine Hvirt Hv0 gives %HV
  obtain ⟨-, HV⟩ := HV
  have HMq' : Mq !! g = some none := HMq
  rw [HMq'] at HV
  simp only [virtQ] at HV
  subst HV
  icases durShares_agree γ id _ _ V E1 $$ Hsh0 Hsh1 with ⟨Hsh0, Hsh1, %HE1⟩
  subst HE1
  imod Hclose $$ [Hsh0 Hv0 Hg0 Hq Hb] with -
  · inext
    unfold slotBody
    iexists γs, V, g, Mq
    iframe Hsh0 Hfr0 Hv0 Hg0 Hq Hb
    ipureintro; exact ⟨Hγs, Hdom, Hcur⟩
  -- the durable invariants, re-based at `b` and `c`
  icases durPers_rebase γ id S V b c Hb1 Hb2 Hb3 Hbt $$ Hdp with
    ⟨%kd, %fp, %Hp, #Hrb, #Hbb, #Hfp, #Hvl, #Hhs, #Hkl, #Hci, #Hcm, -⟩
  obtain ⟨Hvh, Hak, Hcp, Hev, HfB, Hwfb, Hterms_le, HcL⟩ := Hp
  imod durPers_restart_acks E γ id S V b c HE Hb1 Hb2 Hb3 Hbt $$ Hdp Hfr0 with #Hacks
  -- the leader-side keys: entered campaigns' terms
  icases keys_camps γ id _ V (fun t (x : TermRec) => iprop(t ↪[γm]□ x)) terms $$ [$Hsh1 $Htf]
    with ⟨Hsh1, %Ktm⟩
  icases keys_camps γ id _ V (fun t (x : GSet w64) => iprop(t ↪[γw]□ x)) wins $$ [$Hsh1 $Hwf]
    with ⟨Hsh1, %Kwn⟩
  icases keys_camps γ id _ V (fun t (x : GName) => iprop(t ↪[γl]□ x)) lcm $$ [$Hsh1 $Hlf]
    with ⟨Hsh1, %Kln⟩
  icases keys_camps γ id _ V (fun t (x : GName) => iprop(t ↪[γq]□ x)) rqm $$ [$Hsh1 $Hqf]
    with ⟨Hsh1, %Kqn⟩
  imod rdCred_zero (GF := GF) γ with Hcr0
  have Hterm : (restartP S b c).term = S.term := rfl
  have Hrole : (restartP S b c).role = .follower := rfl
  have Hbase : (restartP S b c).base = b := rfl
  have Hlog : (restartP S b c).log = S.entsFrom b := rfl
  have Hcommit : (restartP S b c).commit = c := rfl
  have Hvote : (restartP S b c).vote = S.vote := rfl
  imodintro
  isplitl [Hsh1]
  · iexists V; iframe Hsh1 Hdp
  isplitr [Hl Hfr]
  rotate_left
  · iexists g
    isplitl [Hl]
    · unfold slotLive; iexists γs; iframe Hl; ipureintro; exact Hγs
    · unfold slotFree; iexists γs; iframe Hfr; ipureintro; exact Hγs
  unfold ownRaftGhost
  iexists γs, V, [], kd
  simp only [virt_nil]
  isplitr; · ipureintro; exact Hγs
  isplitr; · iexact Hsinv
  isplitl [Hvirt]; · iexact Hvirt
  isplitr; · unfold promsJust; iapply (BigSepL.bigSepL_nil).2; iempintro
  isplitr; · ipureintro; exact PromsFresh_nil V
  isplitr; · ipureintro; exact Hnz
  isplitr
  · ipureintro; unfold VoteHistOk; rw [Hterm, Hvote]; exact Hvh
  isplitr
  · rw [show (restartP S b c).outbox = [] from rfl]
    iapply (BigSepL.bigSepL_nil).2; iempintro
  isplitr
  · rw [show (restartP S b c).votes = ∅ from rfl, granted_empty]
    iapply (BigSepM.bigSepM_empty).2; iempintro
  isplitr; · unfold leaderWit; rw [Hrole]; iempintro
  isplitl [Hterms Hwins]
  · unfold ownLogGhost
    iexists γm, terms, fp, γw, wins
    iframe Hterms Hwins Htf Hwf Hcinv
    isplitr; · ipureintro; exact Htm
    isplitr
    · ipureintro; intro t ht; exact key_ok_follower S V _ t Hcp Hterm Hrole (Ktm t ht)
    isplitr; · unfold leadLogOwn; rw [Hrole]; iempintro
    isplitr; · ipureintro; intro k hk; rw [Hterm]; exact Hak k hk
    isplitr
    · unfold acksOk; rw [Hrole]
      unfold ackOk; rw [Hterm, Hcommit, Hbase, Hlog]
      iexact Hacks
    isplitr
    · ipureintro; unfold LogOk; rw [Hbase, Hlog, Hcommit]
      exact ⟨PlogWf_wfR _ _ Hwfb, Hb2, HcL⟩
    isplitr; · rw [Hbase, Hlog]; iexact Hrb
    isplitr; · unfold matchedOk; rw [Hrole]; iempintro
    isplitr; · rw [Hlog, Hcommit, Hterm]; iexact Hci
    isplitr; · rw [Hbase]; iexact Hbb
    isplitr
    · ipureintro
      rw [Hbase, Hlog]
      refine ⟨HfB, Hwfb, fun j x Hx => ⟨by rw [Hterm]; exact Hterms_le j x Hx, ?_⟩⟩
      intro h; rw [Hrole] at h; cases h
    isplitr; · iexact Hfp
    isplitr; · ipureintro; intro T hT; rw [Hterm]; exact Hcp T hT
    isplitr; · unfold campOwn; rw [Hrole]; iempintro
    isplitr; · unfold vlogsOk; rw [Hterm]; iexact Hvl
    isplitr
    · unfold histsOk; rw [Hlog]
      have Hbnd : bnd (restartP S b c) kd = bndD S kd := by cases kd <;> rfl
      rw [Hbnd]; iexact Hhs
    isplitr; · ipureintro; exact Hwn
    isplitr
    · ipureintro; intro t ht; exact key_ok_follower S V _ t Hcp Hterm Hrole (Kwn t ht)
    isplitr
    · unfold klOk
      cases kd with
      | none => ipureintro; rw [Hrole]; decide
      | some ldr =>
        iunfold klOkD at Hkl
        isplitr
        · rw [Hterm, Hvote]; iexact Hkl
        · ipureintro; intro h; rw [Hrole] at h; cases h
    isplitr; · ipureintro; rw [Hterm]; exact Hev
    isplitr; · unfold cprefix; rw [Hlog, Hcommit]; iexact Hcm
    isplitr
    · ipureintro
      unfold LeadAcksOk
      exact ⟨fun h => (by rw [Hrole] at h; cases h), fun h => (by rw [Hrole] at h; cases h)⟩
    · ipureintro; rw [Hcommit]; exact Hboot
  isplitr; · ipureintro; intro _ h; exact Hnz h.symm
  isplitr; · ipureintro; intro _; rfl
  isplitr
  · ipureintro
    unfold RoleOk
    exact ⟨fun h => absurd Hrole h, fun h => (by rw [Hrole] at h; cases h)⟩
  isplitl [Hlcm]
  · unfold lcmOwn
    iexists γl, lcm
    iframe Hlcm Hlf
    isplitr; · ipureintro; exact Hln
    isplitr
    · ipureintro; intro t ht; exact key_ok_follower S V _ t Hcp Hterm Hrole (Kln t ht)
    unfold lcmLead; rw [Hrole]; iempintro
  isplitl [Hrqm Hcr0]
  · unfold rdOwn
    iexists γq, rqm
    iframe Hrqm Hqf Hrci
    isplitr; · ipureintro; exact Hqn
    isplitr
    · ipureintro; intro t ht; exact key_ok_follower S V _ t Hcp Hterm Hrole (Kqn t ht)
    isplitr; · unfold rdLead; rw [Hrole]; ipureintro; rfl
    isplitr
    · rw [show (restartP S b c).rd.states = [] from rfl]; iapply (BigSepL.bigSepL_nil).2; iempintro
    isplitr
    · rw [show (restartP S b c).rd.pend = [] from rfl]; iapply (BigSepL.bigSepL_nil).2; iempintro
    isplitl [Hcr0]
    · rw [show (restartP S b c).rd.pend.length + rdCount (restartP S b c).outbox = 0 from rfl]
      iexact Hcr0
    rw [show (restartP S b c).outbox = [] from rfl]; iapply msgsTks_nil
  ipureintro; exact Hmd

/-- (stage II helper; **not provable as stated**, `sorry`, back to stage I) Every entry of the
bootstrap log is of term `1`. Allocation knows it (`BootWf.terms`), but nothing persistent keeps it:
the commit invariant's boot arm (`committedJust`'s first disjunct) holds only `PlogWf base0
γ.reBoot`, and `RaftNames` has no such field. With the committed log still exactly `γ.reBoot`
(no commit fact yet), no resource reachable from `raftCommitInv` names the boot entries' terms
(their records `isEntryR` need them). Repair: add `∀ e ∈ γ.reBoot, e.Term' = W64 1` to
`committedJust`'s boot arm (allocation has it). -/
private theorem boot_terms (E : CoPset) (γ : RaftNames) :
    ↑(raftN γ) ⊆ E → ⊢ raftCommitInv (GF := GF) γ ={E}=∗ ⌜∀ e ∈ γ.reBoot, e.Term' = W64 1⌝ := by
  -- PORT(durability stage II): unprovable as stated (see the docstring); back to stage I
  sorry

/-- (stage II helper) -/
instance committedJust_persistent' (γ : RaftNames) (l : List EntryM) :
    Persistent (committedJust (GF := GF) γ l) := by
  unfold committedJust; infer_instance

/-- (stage II helper) The bootstrap log is committed, well-formed and has its records. -/
private theorem boot_facts (E : CoPset) (γ : RaftNames) :
    ↑(raftN γ) ⊆ E →
    ⊢ raftCommitInv (GF := GF) γ ={E}=∗
      isCommitted γ γ.reBoot ∗ logRecs γ base0 γ.reBoot ∗
      ⌜PlogWf base0 γ.reBoot ∧ ∀ e ∈ γ.reBoot, e.Term' = W64 1⌝ := by
  intro HE
  iintro #Hci
  imod boot_terms E γ HE $$ Hci with %Hones
  ihave #Hli := raftCommitInv_log γ $$ Hci
  have HlE : (↑(raftLogN γ) : CoPset) ⊆ E := raftLogN_of HE
  unfold raftLogInv
  iinv Hli with H Hclose
  unfold raftLogInvBody
  icases H with ⟨%l, >Hauth, >Hj, >Htbl, >Hwt, >Hrest⟩
  icases (persistent_entails_left (P := ownCommitted (GF := GF) γ l) (Q := isCommitted γ l)
    (by iintro H; iapply ownCommitted_lb $$ H)) $$ Hauth with ⟨Hauth, #Hcl⟩
  icases Hj with #Hj
  ihave #Hj' := Hj
  iunfold committedJust at Hj'
  icases Hj' with (%Ha | ⟨%t, %n, %G, %ldr, #Hq, %HlG, -, -⟩)
  · obtain ⟨Hl, Hwf⟩ := Ha
    subst Hl
    have Hlen : (γ.reBoot.length : Int) < 2 ^ 64 := by
      have := PlogWf_range _ _ Hwf; unfold plogLastIndexZ at this; rw [base0_index] at this; omega
    iunfold logRest at Hrest
    icases Hrest with ⟨#Hd, Hrl⟩
    ihave #Hrecs : logRecs γ base0 γ.reBoot $$ []
    · iapply logRecs_boot_intro γ γ.reBoot rfl Hwf Hlen Hones
      unfold entsData
      icases Hd with ⟨%ods, #Hds⟩
      iapply BigSepL.bigSepL_forall_elim
      iintro %k %e Hk
      ipure Hk
      icases entsData_lookup γ γ.reBoot ods k e Hk $$ Hds with ⟨%o, -, #Ho⟩
      unfold entData; iexists o; iexact Ho
    imod Hclose $$ [Hauth Hj Htbl Hwt Hd Hrl] with -
    · inext; iexists γ.reBoot
      iframe Hauth Hj Htbl Hwt
      unfold logRest; iframe Hd Hrl
    imodintro
    iframe Hcl Hrecs
    ipureintro; exact ⟨Hwf, Hones⟩
  · icases cq_boot γ t n G $$ Hq with %Hb
    icases cq_cqAt γ t n G $$ Hq with ⟨%a, %cc, %qq, #Hqa⟩
    icases cqAt_parts γ t n G a cc qq $$ Hqa with ⟨%MH, %Hpq, -, #Hlf, -⟩
    have Hnt := Hpq.1
    icases leadFull_wf γ t G $$ Hlf with ⟨%HG, #HrG⟩
    obtain ⟨Gt, HGt⟩ := Hb.1
    have Hpre : γ.reBoot <+: l := by
      rw [HlG]
      by_cases Hb0 : γ.reBoot = []
      · rw [Hb0]; exact List.nil_prefix
      have Ht2 := Hb.2 Hb0
      have Hn0' := uint_Z_nonneg n
      have Hgt : (γ.reBoot.length : Int) < uint.Z n := by
        refine Int.not_le.mp (fun Hle => ?_)
        by_cases Hn0 : uint.Z n = 0
        · have Hn : n = (base0 : entryID).index' := uint_Z_inj.mp (by rw [base0_index]; exact Hn0)
          rw [Hn, plogTermAt_base] at Hnt
          cases Hnt
          rw [show uint.Z (base0 : entryID).term' = 0 from rfl] at Ht2; omega
        · obtain ⟨e, He, -, Het⟩ := plogTermAt_some_entry _ _ _ _ (PlogWf_wfR _ _ HG.1) Hnt
            (by rw [base0_index]; omega)
          rw [base0_index, ← HGt, List.getElem?_append_left (by omega)] at He
          have := Hones e (List.mem_of_getElem? He)
          rw [← Het, this, show uint.Z (W64 1) = 1 from rfl] at Ht2; omega
      rw [← HGt, List.take_append, List.take_of_length_le (by omega)]
      exact List.prefix_append _ _
    have Hwf : PlogWf base0 γ.reBoot := by
      intro k e Hk
      exact HG.1 k e (by rw [← HGt, List.getElem?_append_left (List.getElem?_eq_some_iff.mp Hk).1]; exact Hk)
    ihave #Hcb := isCommitted_mono γ γ.reBoot l Hpre $$ Hcl
    ihave #Hrecs : logRecs γ base0 γ.reBoot $$ []
    · have Ht : G.take γ.reBoot.length = γ.reBoot := by rw [← HGt]; simp
      rw [← Ht]; iapply logRecs_take γ G _ $$ HrG
    imod Hclose $$ [Hauth Hj Htbl Hwt Hrest] with -
    · inext; iexists l
      iframe Hauth Hj Htbl Hwt Hrest
    imodintro
    iframe Hcb Hrecs
    ipureintro; exact ⟨Hwf, Hones⟩

/-- **A first start from the bootstrap log** (`StartNode`, I-7): a node that has stored nothing
starts at the cluster's bootstrap state (`bootPState`: term `1`, the bootstrap log committed), which
its first `Ready` writes. -/
theorem raft_start_boot (E : CoPset) (γ : RaftNames) (id : w64) {md : Bool} :
    ↑(raftN γ) ⊆ E →
    γ.reDyn.isSome = md →
    ⊢ ownDurGhost (GF := GF) γ id RaftState.init -∗ raftIdSlot γ id ={E}=∗
      ownDurGhost γ id RaftState.init ∗ ownRaftGhost γ id (bootPState γ.reBoot) md ∗
      ∃ g, slotLive γ id 1 g ∗ slotFree γ id g := by
  intro HE Hmd
  iintro Hdur Hslot
  unfold ownDurGhost
  icases Hdur with ⟨%E1, Hsh1, #Hdp⟩
  unfold raftIdSlot
  icases Hslot with ⟨%γs, %V, %g, %Hγs, %Hnz, Hvirt, Hlive, Hfree, #Hsinv, #Hcinv, #Hrci,
    ⟨%γm, %terms, %Htm, Hterms, #Htf⟩, ⟨%γw, %wins, %Hwn, Hwins, #Hwf⟩,
    ⟨%γl, %lcm, %Hln, Hlcm, #Hlf⟩, ⟨%γq, %rqm, %Hqn, Hrqm, #Hqf⟩⟩
  iunfold slotLive at Hlive
  icases Hlive with ⟨%γs1, %H1, Hl⟩
  rw [Hγs] at H1; cases H1
  iunfold slotFree at Hfree
  icases Hfree with ⟨%γs2, %H2, Hfr⟩
  rw [Hγs] at H2; cases H2
  have HsE : (↑(slotN γ id) : CoPset) ⊆ E := fun p hp => HE p (slotN_raftN γ id p hp)
  ihave #Hsi := Hsinv
  iunfold slotInv at Hsi
  iinv Hsi with H Hclose
  iunfold slotBody at H
  icases H with ⟨%γs', %E0, %g0, %Mq, >%Hγs', >Hsh0, #>Hfr0, >Hv0, >Hg0, >Hq, >%Hdom, >%Hcur, Hb⟩
  rw [Hγs] at Hγs'; cases Hγs'
  icombine Hl Hg0 gives %Hgg
  obtain ⟨-, Hgg⟩ := Hgg
  subst Hgg
  icombine Hq Hfr gives %HMq
  icombine Hvirt Hv0 gives %HV
  obtain ⟨-, HV⟩ := HV
  have HMq' : Mq !! g = some none := HMq
  rw [HMq'] at HV
  simp only [virtQ] at HV
  subst HV
  icases durShares_agree γ id _ _ V E1 $$ Hsh0 Hsh1 with ⟨Hsh0, Hsh1, %HE1⟩
  subst HE1
  imod Hclose $$ [Hsh0 Hv0 Hg0 Hq Hb] with -
  · inext
    unfold slotBody
    iexists γs, V, g, Mq
    iframe Hsh0 Hfr0 Hv0 Hg0 Hq Hb
    ipureintro; exact ⟨Hγs, Hdom, Hcur⟩
  -- the initial state's durable invariants: every promise at term `0`
  ihave #Hdp' := Hdp
  iunfold durPers at Hdp'
  icases Hdp' with ⟨%kd, %fp0, %Hp, -, -, -, #Hvl, #Hhs, -, -, -, -, -⟩
  obtain ⟨Hvh, Hak, Hcp, Hev, Hfull0, -, -, -, -⟩ := Hp
  have Hfp0 : fp0 = [] := by
    have := Hfull0.1
    rw [show uint.Z RaftState.init.base.index' = 0 from rfl] at this
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst Hfp0
  have Hi0 : uint.Z RaftState.init.term = 0 := rfl
  -- the bootstrap log
  imod boot_facts E γ HE $$ Hcinv with ⟨#Hcb, #Hrb, %Hbt⟩
  obtain ⟨Hwfb, Hones⟩ := Hbt
  have Hlenb : (γ.reBoot.length : Int) < 2 ^ 64 := by
    have := PlogWf_range _ _ Hwfb; unfold plogLastIndexZ at this; rw [base0_index] at this; omega
  have HWL : uint.Z (W64 (γ.reBoot.length : Int)) = γ.reBoot.length := uint_Z_W64 _ (by omega) Hlenb
  -- the leader-side keys: entered campaigns' terms, so `0`
  icases keys_camps γ id _ V (fun t (x : TermRec) => iprop(t ↪[γm]□ x)) terms $$ [$Hsh1 $Htf]
    with ⟨Hsh1, %Ktm⟩
  icases keys_camps γ id _ V (fun t (x : GSet w64) => iprop(t ↪[γw]□ x)) wins $$ [$Hsh1 $Hwf]
    with ⟨Hsh1, %Kwn⟩
  icases keys_camps γ id _ V (fun t (x : GName) => iprop(t ↪[γl]□ x)) lcm $$ [$Hsh1 $Hlf]
    with ⟨Hsh1, %Kln⟩
  icases keys_camps γ id _ V (fun t (x : GName) => iprop(t ↪[γq]□ x)) rqm $$ [$Hsh1 $Hqf]
    with ⟨Hsh1, %Kqn⟩
  imod rdCred_zero (GF := GF) γ with Hcr0
  have Hterm : (bootPState γ.reBoot).term = W64 1 := rfl
  have Hrole : (bootPState γ.reBoot).role = .follower := rfl
  have Hbase : (bootPState γ.reBoot).base = base0 := rfl
  have Hlog : (bootPState γ.reBoot).log = γ.reBoot := rfl
  have Hcommit : (bootPState γ.reBoot).commit = W64 (γ.reBoot.length : Int) := rfl
  have Hvote : (bootPState γ.reBoot).vote = W64 0 := rfl
  have H1 : uint.Z (W64 1) = 1 := rfl
  have Hkey : ∀ t, (V.camps !! t).isSome →
      uint.Z t < uint.Z (bootPState γ.reBoot).term ∨
        (t = (bootPState γ.reBoot).term ∧ (bootPState γ.reBoot).role ≠ .candidate) := by
    intro t ht; left; have := Hcp t ht; rw [Hi0] at this; rw [Hterm, H1]; omega
  imodintro
  isplitl [Hsh1]
  · iexists V; iframe Hsh1 Hdp
  isplitr [Hl Hfr]
  rotate_left
  · iexists g
    isplitl [Hl]
    · unfold slotLive; iexists γs; iframe Hl; ipureintro; exact Hγs
    · unfold slotFree; iexists γs; iframe Hfr; ipureintro; exact Hγs
  unfold ownRaftGhost
  iexists γs, V, [], none
  simp only [virt_nil]
  isplitr; · ipureintro; exact Hγs
  isplitr; · iexact Hsinv
  isplitl [Hvirt]; · iexact Hvirt
  isplitr; · unfold promsJust; iapply (BigSepL.bigSepL_nil).2; iempintro
  isplitr; · ipureintro; exact PromsFresh_nil V
  isplitr; · ipureintro; exact Hnz
  isplitr
  · ipureintro
    unfold VoteHistOk; rw [Hterm, Hvote]
    refine ⟨fun t ht => ?_, ?_⟩
    · have := Hvh.1 t ht; rw [Hi0] at this; rw [H1]; omega
    · simp only [↓reduceIte]
      cases h : V.voted !! W64 1 with
      | none => rfl
      | some _ => have := Hvh.1 (W64 1) (by rw [h]; rfl); rw [Hi0, H1] at this; omega
  isplitr
  · rw [show (bootPState γ.reBoot).outbox = [] from rfl]
    iapply (BigSepL.bigSepL_nil).2; iempintro
  isplitr
  · rw [show (bootPState γ.reBoot).votes = ∅ from rfl, granted_empty]
    iapply (BigSepM.bigSepM_empty).2; iempintro
  isplitr; · unfold leaderWit; rw [Hrole]; iempintro
  isplitl [Hterms Hwins]
  · unfold ownLogGhost
    iexists γm, terms, [], γw, wins
    iframe Hterms Hwins Htf Hwf Hcinv
    isplitr; · ipureintro; exact Htm
    isplitr; · ipureintro; intro t ht; exact Hkey t (Ktm t ht)
    isplitr; · unfold leadLogOwn; rw [Hrole]; iempintro
    isplitr
    · ipureintro; intro k hk; have := Hak k hk; rw [Hi0] at this; rw [Hterm, H1]; omega
    isplitr
    · unfold acksOk; rw [Hrole]
      iapply (BigSepM.bigSepM_forall (Φ := fun k (_ : Unit) => ackOk (GF := GF) γ (bootPState γ.reBoot) k)).2
      iintro %k %u %hk
      unfold ackOk
      iintro %Hc
      exfalso
      have := Hak k (by rw [show V.acks !! k = some u from hk]; rfl)
      rw [Hi0, Hc.1, Hterm, H1] at this; omega
    isplitr
    · ipureintro; unfold LogOk plogLastIndexZ; rw [Hbase, Hlog, Hcommit, base0_index, HWL]
      exact ⟨PlogWf_wfR _ _ Hwfb, Int.natCast_nonneg _, by omega⟩
    isplitr; · rw [Hbase, Hlog]; iexact Hrb
    isplitr; · unfold matchedOk; rw [Hrole]; iempintro
    isplitr
    · unfold commitIn
      isplitr
      · unfold commitJ; ileft; ipureintro
        rw [Hlog, Hcommit, HWL, List.nil_append]; exact ⟨Int.le_refl _, rfl⟩
      · unfold dynOn
        iright; unfold witsB; iintro %k %Hk %Hb; exfalso
        have := Hk.2
        rw [Hcommit, HWL] at this
        simp at this
        omega
    isplitr; · rw [Hbase]; unfold baseOk; ileft; ipureintro; rfl
    isplitr
    · ipureintro
      rw [Hlog, Hbase]
      refine ⟨FullOk_base0, Hwfb, ?_⟩
      intro j x Hx
      rw [List.nil_append] at Hx
      refine ⟨?_, fun h => by rw [Hrole] at h; cases h⟩
      rw [Hterm, H1]
      have := uint_Z_nonneg j
      by_cases Hj0 : uint.Z j = 0
      · have Hj : j = base0.index' := uint_Z_inj.mp (by rw [base0_index]; exact Hj0)
        subst Hj
        rw [plogTermAt_base] at Hx
        cases Hx
        rw [show uint.Z (base0 : entryID).term' = 0 from rfl]; omega
      · obtain ⟨e, He, -, Hxt⟩ := plogTermAt_some_entry _ _ _ _ (PlogWf_wfR _ _ Hwfb) Hx
          (by rw [base0_index]; omega)
        rw [← Hxt, Hones e (List.mem_of_getElem? He), H1]; omega
    isplitr; · unfold logRecs; iapply (BigSepL.bigSepL_nil).2; iempintro
    isplitr
    · ipureintro; intro T hT; have := Hcp T hT; rw [Hi0] at this; rw [Hterm, H1]; omega
    isplitr; · unfold campOwn; rw [Hrole]; iempintro
    isplitr
    · unfold vlogsOk
      iapply BigSepM.bigSepM_impl $$ Hvl
      imodintro
      iintro %k %x %_ ⟨%Hx, #Hr⟩
      iframe Hr
      ipureintro; rw [Hi0] at Hx; rw [Hterm, H1]; omega
    isplitr
    · unfold histsOk
      rw [Hlog, List.nil_append]
      iapply BigSepM.bigSepM_impl $$ Hhs
      imodintro
      iintro %k %u %_ #Hh
      rw [List.nil_append]
      iapply hist_mono γ γ.reBoot k.1 k.2 (bndD RaftState.init kd) (bnd (bootPState γ.reBoot) none)
        (by unfold bnd bndD; rw [Hterm, H1, Hi0]; split <;> omega)
      iapply hist_keep γ _ γ.reBoot k.1 k.2 _ ?_ $$ Hh
      intro j Hj Hs
      exfalso
      have Hn : plogTermAt base0 RaftState.init.ents j = none := by
        unfold plogTermAt
        rw [base0_index]
        simp only [show ¬ (uint.Z j < 0) by omega, show ¬ (uint.Z j = 0) by omega, ↓reduceIte]
        rfl
      rw [Hn] at Hs; cases Hs
    isplitr; · ipureintro; exact Hwn
    isplitr; · ipureintro; intro t ht; exact Hkey t (Kwn t ht)
    isplitr; · unfold klOk; ipureintro; rw [Hrole]; decide
    isplitr; · ipureintro; exact EvsOk_mono _ _ V (by rw [Hi0, Hterm, H1]; omega) Hev
    isplitr
    · unfold cprefix; rw [Hlog, Hcommit, HWL]
      simp only [Int.toNat_natCast, List.nil_append, List.take_length]; iexact Hcb
    isplitr
    · ipureintro
      unfold LeadAcksOk
      exact ⟨fun h => (by rw [Hrole] at h; cases h), fun h => (by rw [Hrole] at h; cases h)⟩
    · ipureintro; rw [Hcommit, HWL]; exact Int.le_refl _
  isplitr; · ipureintro; intro _ h; exact Hnz h.symm
  isplitr; · ipureintro; intro _; rfl
  isplitr
  · ipureintro
    unfold RoleOk
    exact ⟨fun h => absurd Hrole h, fun h => (by rw [Hrole] at h; cases h)⟩
  isplitl [Hlcm]
  · unfold lcmOwn
    iexists γl, lcm
    iframe Hlcm Hlf
    isplitr; · ipureintro; exact Hln
    isplitr; · ipureintro; intro t ht; exact Hkey t (Kln t ht)
    unfold lcmLead; rw [Hrole]; iempintro
  isplitl [Hrqm Hcr0]
  · unfold rdOwn
    iexists γq, rqm
    iframe Hrqm Hqf Hrci
    isplitr; · ipureintro; exact Hqn
    isplitr; · ipureintro; intro t ht; exact Hkey t (Kqn t ht)
    isplitr; · unfold rdLead; rw [Hrole]; ipureintro; rfl
    isplitr
    · rw [show (bootPState γ.reBoot).rd.states = [] from rfl]
      iapply (BigSepL.bigSepL_nil).2; iempintro
    isplitr
    · rw [show (bootPState γ.reBoot).rd.pend = [] from rfl]
      iapply (BigSepL.bigSepL_nil).2; iempintro
    isplitl [Hcr0]
    · rw [show (bootPState γ.reBoot).rd.pend.length + rdCount (bootPState γ.reBoot).outbox = 0
        from rfl]
      iexact Hcr0
    rw [show (bootPState γ.reBoot).outbox = [] from rfl]; iapply msgsTks_nil
  ipureintro; exact Hmd

/-- **A stop** (R8; review 1's N6: the read credits and proposal tickets the volatile half holds
are dropped): the volatile half and the whole generation give back the vacant slot -- the
leader-side authorities with their keys' campaigns, the virtual maps reset to the entered ones --
with the generation bumped, so that a batch cut in it and not entered can no longer be. -/
theorem raft_stop (E : CoPset) (γ : RaftNames) (id : w64) (s : PState) {md : Bool} (g : Nat) :
    ↑(raftN γ) ⊆ E →
    ⊢ slotLive (GF := GF) γ id 1 g -∗ ownRaftGhost γ id s md ={E}=∗ raftIdSlot γ id := by
  intro HE
  have HsE : (↑(slotN γ id) : CoPset) ⊆ E := fun p hp => HE p (slotN_raftN γ id p hp)
  iintro Hlive Hg
  unfold ownRaftGhost
  icases Hg with ⟨%γs, %V, %πc, %kl, %Hsname, #Hslot, Hvirt, -, -, %Hidnz, -, -, -, -, Hlg, -, -, -,
    Hlcm, Hrd, -⟩
  unfold ownLogGhost
  icases Hlg with ⟨%γm, %terms, %fp, %γw, %wins, %Htname, Hterms, #Htfrags, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, %Hwname, Hwins, #Hwfrags, -, -, -, #Hinv, -⟩
  unfold lcmOwn
  icases Hlcm with ⟨%γl, %lcm, %Hγl, Hlcma, #Hlcmf, -, -⟩
  unfold rdOwn
  icases Hrd with ⟨%γq, %rqm, %Hγq, Hrqa, #Hrqf, -, -, -, -, -, #Hcinv, -⟩
  unfold slotLive
  icases Hlive with ⟨%γs', %Hγs', Hgen⟩
  rw [Hsname] at Hγs'; cases Hγs'
  unfold slotInv
  iinv Hslot with H Hclose
  unfold slotBody
  icases H with ⟨%γs', %E0, %g0, %Mq, >%Hγs', >Hsh, #Hfr, >Hv', >Hg', >Hq, >%Hdom, >%Hcur, -⟩
  rw [Hsname] at Hγs'; cases Hγs'
  ihave %Hgg := ghostVar_agree _ _ _ _ _ $$ Hgen Hg'
  subst Hgg
  imod ghostVar_update_halves E0 γs.1 _ _ $$ Hvirt Hv' with ⟨Hvirt, Hv'⟩
  imod ghostVar_update_halves (g + 1) γs.2.2 _ _ $$ Hgen Hg' with ⟨Hgen, Hg'⟩
  have Hfresh : Mq.lookup (g + 1) = none := by
    cases h : Mq.lookup (g + 1) with
    | none => rfl
    | some x =>
      have := Hdom (g + 1) (by
        show (Mq !! (g + 1)).isSome = true
        rw [show Mq !! (g + 1) = Mq.lookup (g + 1) from rfl, h]; rfl)
      omega
  imod ghost_map_insert (g + 1) (none : Option RaftBatch) Hfresh $$ Hq with ⟨Hq, Hfree⟩
  imod Hclose $$ [Hsh Hv' Hg' Hq] with -
  · inext
    iexists γs, E0, g + 1, Mq.insert (g + 1) none
    have Hl : (Mq.insert (g + 1) (none : Option RaftBatch)) !! (g + 1) = some none :=
      GMap.lookup_insert _ _ _
    rw [Hl]
    iframe Hsh Hfr Hg' Hq
    isplitr; · ipureintro; exact Hsname
    isplitl [Hv']; · simp only [virtQ]; iexact Hv'
    isplitr
    · ipureintro
      intro k hk
      by_cases hkg : k = g + 1
      · omega
      · have : (Mq.insert (g + 1) (none : Option RaftBatch)) !! k = Mq !! k :=
          GMap.lookup_insert_ne _ _ (Ne.symm hkg)
        rw [this] at hk
        have := Hdom k hk
        omega
    isplitr; · ipureintro; rfl
    iintro %b %hb
    cases hb
  imodintro
  unfold raftIdSlot slotInv slotBody
  iexists γs, E0, g + 1
  iframe Hvirt Hslot Hinv Hcinv
  isplitr; · ipureintro; exact Hsname
  isplitr; · ipureintro; exact Hidnz
  isplitl [Hgen]
  · unfold slotLive; iexists γs; iframe Hgen; ipureintro; exact Hsname
  isplitl [Hfree]
  · unfold slotFree; iexists γs; iframe Hfree; ipureintro; exact Hsname
  isplitl [Hterms]
  · iexists γm, terms; iframe Hterms Htfrags; ipureintro; exact Htname
  isplitl [Hwins]
  · iexists γw, wins; iframe Hwins Hwfrags; ipureintro; exact Hwname
  isplitl [Hlcma]
  · iexists γl, lcm; iframe Hlcma Hlcmf; ipureintro; exact Hγl
  · iexists γq, rqm; iframe Hrqa Hrqf; ipureintro; exact Hγq

end enter

end EtcdGrove
end Perennial
