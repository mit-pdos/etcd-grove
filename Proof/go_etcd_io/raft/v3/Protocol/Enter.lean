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

/-- (stage II helper) Two cuts of one full log agree above both bases. -/
private theorem plog_rebase_eq (b1 b2 : entryID) (fp1 es1 fp2 es2 : List EntryM) (i : w64) :
    FullOk b1 fp1 → FullOk b2 fp2 → fp1 ++ es1 = fp2 ++ es2 →
    uint.Z b1.index' ≤ uint.Z i → uint.Z b2.index' ≤ uint.Z i →
    plogTermAt b1 es1 i = plogTermAt b2 es2 i ∧ plogLastIndexZ b1 es1 = plogLastIndexZ b2 es2 := by
  intro H1 H2 He Hi1 Hi2
  refine ⟨?_, ?_⟩
  · rw [← full_term_at b1 fp1 es1 i H1 Hi1, ← full_term_at b2 fp2 es2 i H2 Hi2, He]
  · rw [← full_last_index b1 fp1 es1 H1, ← full_last_index b2 fp2 es2 H2, He]

/-- The justifications of a pending list, head and tail. -/
theorem promsJust_cons (γ : RaftNames) (id : w64) (W : DurMaps) (p : Prom) (π : List Prom) :
    promsJust (GF := GF) γ id W (p :: π) ⊣⊢ promJust γ id W p ∗ promsJust γ id (W.add p) π := by
  unfold promsJust
  exact BigSepL.bigSepL_cons

/-- (stage II helper, 2026-11-01, approved repair 1) **The acknowledgements' leaders of a pending
list's maps** (`ackInF`), given the fragments of maps above them: the entered ones' (given), and
each pending acknowledgement's from its justification. -/
theorem acksInF_virt (γ : RaftNames) (id : w64) (W : DurMaps) :
    ∀ (π : List Prom) (V : DurMaps), PromsFresh V π → DurLe (virt V π) W →
    ⊢ promsJust (GF := GF) γ id V π -∗
      □ (durFrags γ id W -∗ [∗map] k ↦ _u ∈ V.acks, ackInF γ k.1 k.2) -∗
      □ (durFrags γ id W -∗ [∗map] k ↦ _u ∈ (virt V π).acks, ackInF γ k.1 k.2)
  | [], V, _, _ => by
    iintro - #H
    rw [virt_nil]; iexact H
  | p :: π, V, Hfr, Hle => by
    rw [PromsFresh_cons] at Hfr
    obtain ⟨Hf1, Hf2⟩ := Hfr
    rw [virt_cons] at Hle ⊢
    have HleV : DurLe V W :=
      DurLe_trans _ _ _ (DurLe_add V p Hf1) (DurLe_trans _ _ _ (DurLe_virt _ π Hf2) Hle)
    iintro #Hj #H
    icases (promsJust_cons γ id V p π).1 $$ Hj with ⟨#Hj1, #Hj2⟩
    iapply acksInF_virt γ id W π (V.add p) Hf2 Hle $$ Hj2
    imodintro
    iintro #Hf
    ihave #Hm := H $$ Hf
    cases p with
    | ack T i =>
      iunfold promJust at Hj1
      ihave #Hn := Hj1 $$ []
      · iapply durFrags_mono γ id V W HleV $$ Hf
      iunfold promNeed at Hn
      rw [show (V.add (.ack T i)).acks = <[(T, i) := ()]> V.acks from rfl]
      iapply (BigSepM.bigSepM_insert_elim (Φ := fun (k : w64 × w64) (_ : Unit) =>
        ackInF (GF := GF) γ k.1 k.2) (m := V.acks) (i := (T, i)) (x := ())) $$ Hn Hm
    | vote T c d Fv => rw [show (V.add (.vote T c d Fv)).acks = V.acks from rfl]; iexact Hm
    | camp T F k => rw [show (V.add (.camp T F k)).acks = V.acks from rfl]; iexact Hm

/-- (stage II helper) **The durable invariants at the cut**, from the volatile ones: the cut
state `S'` has the node's term, vote and commit, and its full log (`DurFull`), with its base at
most the commit; the acknowledgements of the term above the commit agree with the log -- a
non-leader's by `acksOk`, a leader's own from its own prefix (`ownLogGhost_lead_full`). -/
theorem cut_durPers (γ : RaftNames) (id : w64) (s : PState) (kl : Option w64) (W : DurMaps)
    (S' : RaftState) :
    S'.term = s.term → S'.vote = s.vote → S'.commit = s.commit →
    uint.Z S'.base.index' ≤ uint.Z s.commit → VoteHistOk W.voted s →
    ⊢ (□ ∀ fp, ⌜FullOk s.base fp⌝ -∗ logRecs (GF := GF) γ base0 fp -∗ ⌜DurFull S' (fp ++ s.log)⌝) -∗
      leaderWit γ id s -∗ ownLogGhost γ id s kl W -∗
      □ (durFrags γ id W -∗ [∗map] k ↦ _u ∈ W.acks, ackInF γ k.1 k.2) -∗
      ownLogGhost γ id s kl W ∗ durPers γ id S' W := by
  intro Ht Hv Hc Hbc Hvh
  iintro #Hdf #Hlw Hlg #Hai
  -- a leader's own prefix, for its own acknowledgements
  ihave HL : iprop((□ (⌜s.role = .leader⌝ -∗ ∃ fpL, leadPrefix (GF := GF) γ id s.term s.base s.log ∗
      lpfull γ id s.term s.base s.log fpL)) ∗ ownLogGhost γ id s kl W) $$ [Hlg]
  · by_cases Hr : s.role = .leader
    · unfold leaderWit
      rw [Hr]
      icases ownLogGhost_lead_full γ id s kl W Hr $$ Hlw Hlg with ⟨⟨%fpL, #Hp, #Hpf, -⟩, Hlg⟩
      iframe Hlg
      imodintro; iintro -; iexists fpL; iframe Hp Hpf
    · iframe Hlg
      imodintro; iintro %h; exact absurd h Hr
  icases HL with ⟨#HL, Hlg⟩
  unfold ownLogGhost
  icases Hlg with ⟨%γm, %terms, %fp, %γw, %wins, H⟩
  iNamed H
  obtain ⟨HfullB, HwfS, Htle⟩ := Hfull
  ihave %HDF := Hdf $$ %fp %HfullB Hfrecs
  obtain ⟨Hents, HfB'⟩ := HDF
  have HwfF : PlogWf base0 (fp ++ s.log) := full_wf _ _ _ HfullB HwfS
  ihave #HrF := logRecs_full γ s.base fp s.log HfullB $$ Hfrecs Hrecs
  have Hm : (uint.nat S'.base.index' : Int) = uint.Z S'.base.index' := uint_nat_eq _
  generalize Hmd : uint.nat S'.base.index' = m at Hents HfB' Hm
  generalize HF : fp ++ s.log = F at HwfF Hents HfB' Htle
  have Hfeq : F.take m ++ S'.ents = F := by rw [Hents, List.take_append_drop]
  have HlastS : plogLastIndexZ S'.base S'.ents = plogLastIndexZ s.base s.log := by
    rw [← full_last_index S'.base (F.take m) S'.ents HfB', Hfeq, ← HF,
      full_last_index s.base fp s.log HfullB]
  have HcI := Hlog_ok.2.1
  have HcL := Hlog_ok.2.2
  have Hsb : uint.Z s.base.index' ≤ uint.Z s.commit := HcI
  -- the log's two cuts agree above both bases
  have Hre : ∀ i : w64, uint.Z s.commit < uint.Z i →
      plogTermAt s.base s.log i = plogTermAt S'.base S'.ents i ∧
      plogLastIndexZ s.base s.log = plogLastIndexZ S'.base S'.ents := by
    intro i hi
    exact plog_rebase_eq s.base S'.base fp s.log (F.take m) S'.ents i HfullB HfB'
      (by rw [HF, Hfeq]) (by omega) (by omega)
  isplitl [Hterms Htlog Hwins]
  · iexists γm, terms, fp, γw, wins
    rw [HF]
    iframe Hterms Htlog Hwins Htfrags Hacks_ok Hrecs Hmatched Hbase Hfrecs Hcown Hvlogs_ok Hhists
      Hwfrags Hkl Hinv
    isplitr; · ipureintro; exact Htname
    isplitr; · ipureintro; exact Hterms_ok
    isplitr; · ipureintro; exact Hacks_term
    isplitr; · ipureintro; exact Hlog_ok
    isplitr; · iexact Hcommit
    isplitr; · ipureintro; exact ⟨HfullB, HwfS, Htle⟩
    isplitr; · ipureintro; exact Hcamps_ok
    isplitr; · ipureintro; exact Hwname
    isplitr; · ipureintro; exact Hwins_ok
    isplitr; · ipureintro; exact Hevs
    isplitr; · iexact Hcmt
    isplitr; · ipureintro; exact Hlacks
    ipureintro; exact Hboot
  unfold durPers
  iexists kl, F.take m
  rw [Hfeq]
  isplitr
  · ipureintro
    refine ⟨?_, fun k hk => by rw [Ht]; exact Hacks_term k hk, fun T hT => by rw [Ht]; exact Hcamps_ok T hT,
      by rw [Ht]; exact Hevs, HfB', ?_, fun j x Hx => by rw [Ht]; exact (Htle j x Hx).1,
      by rw [Hc]; exact Hbc, by rw [HlastS, Hc]; exact HcL⟩
    · unfold VoteHistOkD; rw [Ht, Hv]; exact Hvh
    · rw [Hents]
      intro k e Hk
      rw [List.getElem?_drop] at Hk
      have := HwfF _ _ Hk
      rw [base0_index] at this
      push_cast at this ⊢; omega
  isplitr
  · rw [Hents]; iapply logRecs_drop γ F S'.base m HfB' Hm.symm $$ HrF
  isplitr
  · unfold baseOk
    by_cases H0 : uint.Z S'.base.index' = 0
    · ileft; ipureintro; exact H0
    · iright
      have Hbt : plogTermAt base0 F S'.base.index' = some S'.base.term' := by
        rw [← Hfeq, full_term_at _ _ _ _ HfB' (Int.le_refl _), plogTermAt_base]
      obtain ⟨e, He, Hei, Het⟩ := plogTermAt_some_entry base0 F S'.base.index' S'.base.term'
        (PlogWf_wfR _ _ HwfF) Hbt (by rw [base0_index]; have := uint_Z_nonneg S'.base.index'; omega)
      rw [base0_index] at He
      ihave ⟨%pt, -, #Her⟩ := logRecs_lookup γ F _ e He
        (by have := uint_Z_lt S'.base.index'; omega) $$ HrF
      unfold isSnapMeta
      iexists e
      isplitr
      · unfold isEntry; iexists pt; iexact Her
      ipureintro; exact ⟨Het, Hei⟩
  isplitr; · iapply logRecs_take γ F m $$ HrF
  isplitr; · iunfold vlogsOk at Hvlogs_ok; rw [Ht]; iexact Hvlogs_ok
  isplitr
  · iunfold histsOk at Hhists
    have Hb : bndD S' kl = bnd s kl := by cases kl <;> simp [bnd, bndD, Ht]
    rw [Hb]; iexact Hhists
  isplitr
  · cases kl with
    | none => unfold klOkD; itrivial
    | some ldr =>
      unfold klOkD
      iunfold klOk at Hkl
      icases Hkl with ⟨#Hw, -⟩
      rw [Ht, Hv]; iexact Hw
  isplitr
  · by_cases Hr : s.role = .leader
    · iapply (BigSepM.bigSepM_forall (Φ := fun (k : w64 × w64) (_ : Unit) =>
        iprop(∀ (_ : k.1 = S'.term ∧ uint.Z S'.commit < uint.Z k.2),
          ackAgree (GF := GF) γ S'.base S'.ents k.1 k.2))).2
      iintro %k %u %hk %Hk
      obtain ⟨Hk1, Hk2⟩ := Hk
      rw [Ht] at Hk1; rw [Hc] at Hk2
      have Hli := Hlacks.2 Hr k.2 (by rw [← Hk1]; rw [show W.acks !! k = some u from hk]; rfl)
      obtain ⟨Hte, Hle⟩ := Hre k.2 Hk2
      icases HL $$ %Hr with ⟨%fpL, #Hp, #Hpf⟩
      rw [Hk1]
      iapply ackAgree_intro γ S'.base S'.ents s.term k.2 id s.base s.log fpL
        (by rw [← Hle]; exact Hli) (plogTermAt_in_range _ _ _ ⟨by omega, Hli⟩) Hte $$ Hp Hpf
    · have Hacks' : acksOk (GF := GF) γ s W.acks = iprop([∗map] k ↦ _u ∈ W.acks, ackOk γ s k) := by
        unfold acksOk; split
        · rename_i h; exact absurd h Hr
        · rfl
      ihave #Hao : ([∗map] k ↦ _u ∈ W.acks, ackOk (GF := GF) γ s k) $$ []
      · rw [← Hacks']; iexact Hacks_ok
      iapply BigSepM.bigSepM_impl $$ Hao
      imodintro
      iintro %k %u %_ #Hok %Hk
      obtain ⟨Hk1, Hk2⟩ := Hk
      rw [Ht] at Hk1; rw [Hc] at Hk2
      unfold ackOk
      ihave #Ha := Hok $$ %(And.intro Hk1 Hk2)
      obtain ⟨Hte, Hle⟩ := Hre k.2 Hk2
      unfold ackAgree
      icases Ha with ⟨%Hi, %X, #HX, %Hag⟩
      isplitr; · ipureintro; rw [← Hle]; exact Hi
      iexists X
      iframe HX
      ipureintro; exact ⟨Hag.1, Hag.2.trans Hte⟩
  isplitr; · rw [Hc, Ht]; iexact Hcommit
  iframe Hinv Hai
  rw [Hc, ← HF]; iunfold cprefix at Hcmt; iexact Hcmt

/-- (2026-11-02, stage II (p)) `durI1` reads only the state's base and entries, and the commit. -/
theorem durI1_congr (γ : RaftNames) {S S' : RaftState} {c c' : w64} (hb : S'.base = S.base)
    (he : S'.ents = S.ents) (hc : c' = c) : durI1 (GF := GF) γ S c ⊢ durI1 γ S' c' := by
  unfold durI1; rw [hb, he, hc]

/-- (2026-11-02, stage II (p)) `ConfI1` is monotone in the commit. -/
theorem ConfI1.mono {l : List EntryM} {c c' : Nat} (H : ConfI1 l c) (h : c ≤ c') : ConfI1 l c' :=
  fun k1 k2 e1 e2 hlt h1 h2 c1 c2 => Nat.lt_of_lt_of_le (H k1 k2 e1 e2 hlt h1 h2 c1 c2) h

/-- (2026-11-02, stage II (p)) **`durI1` of a state whose full log is `F`** (`DurFull`), from I1 of
`F` and `F`'s records: every full prefix of the state's base with records is `F`'s
(`FullOk_unique`). -/
theorem durI1_of_full (γ : RaftNames) (S : RaftState) (F : List EntryM) (c : w64) :
    DurFull S F → (γ.reDyn.isSome = true → ConfI1 F (uint.nat c)) →
    ⊢ logRecs (GF := GF) γ base0 F -∗ durI1 γ S c := by
  intro Hdf HI
  iintro #HrF
  unfold durI1
  iintro !> %fp %Hfp #Hr
  obtain ⟨He, Hfo⟩ := Hdf
  ihave #Ht := logRecs_take γ F (uint.nat S.base.index') $$ HrF
  icases FullOk_unique γ S.base fp _ Hfp Hfo $$ Hr Ht with %Hfe
  ipureintro
  rw [Hfe, He, List.take_append_drop]
  exact HI

/-- (2026-11-02, stage II (p)) **I1 at a restart**: the durable half's I1 at `S.wcommit`
(`durI1`), re-based at a base `b` within `S`'s log, at a commit `c ≥ S.wcommit` (`ConfI1.mono`). -/
theorem durI1_rebase (γ : RaftNames) (id : w64) (S : RaftState) (Ed : DurMaps) (b : entryID)
    (c : w64) :
    uint.Z S.base.index' ≤ uint.Z b.index' → plogTermAt S.base S.ents b.index' = some b.term' →
    uint.nat S.wcommit ≤ uint.nat c →
    ⊢ durPers (GF := GF) γ id S Ed -∗ durI1 γ S S.wcommit -∗
      □ ∀ fp, ⌜FullOk b fp⌝ -∗ logRecs γ base0 fp -∗
        ⌜γ.reDyn.isSome = true → ConfI1 (fp ++ S.entsFrom b) (uint.nat c)⌝ := by
  intro Hb1 Hbt Hwc
  iintro #Hd #HI
  unfold durPers
  icases Hd with ⟨%kd, %fp0, %Hp, #HrS, -, #Hfp0, -⟩
  obtain ⟨-, -, -, -, HfullS, HwfS, -⟩ := Hp
  have HwfF : PlogWf base0 (fp0 ++ S.ents) := full_wf _ _ _ HfullS HwfS
  iunfold durI1 at HI
  ihave %HI0 := HI $$ %fp0 %HfullS Hfp0
  have Hbt' : plogTermAt base0 (fp0 ++ S.ents) b.index' = some b.term' := by
    rw [full_term_at _ _ _ _ HfullS Hb1]; exact Hbt
  generalize HF : fp0 ++ S.ents = F at HwfF Hbt' HI0
  ihave #HrF : logRecs γ base0 F $$ []
  · rw [← HF]; iapply logRecs_full γ S.base fp0 S.ents HfullS $$ Hfp0 HrS
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
  iintro !> %fp %Hfp #Hr
  ihave #Ht := logRecs_take γ F m $$ HrF
  icases FullOk_unique γ b fp _ Hfp HfB $$ Hr Ht with %Hfe
  ipureintro
  intro hd
  rw [Hfe, ← Hdrop, List.take_append_drop]
  exact (HI0 hd).mono Hwc

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
    -- (2026-11-01, stage II(d), approved stage-I repair) the cut state's base is at most the
    -- commit (the storage's snapshot is), and every message left in the outbox is self-addressed
    -- (synchronous mode: the `Ready` takes all of `r.msgs`; only self-addressed ones wait for
    -- `Advance`)
    uint.Z S'.base.index' ≤ uint.Z s.commit → (∀ m ∈ o', m.dst = id) →
    ⊢ (□ ∀ fp, ⌜FullOk s.base fp⌝ -∗ logRecs (GF := GF) γ base0 fp -∗ ⌜DurFull S' (fp ++ s.log)⌝) -∗
      -- (2026-11-02, stage II (p)) I1 of the batch's log at its commit
      durI1 γ S' S'.commit -∗
      slotLive γ id q g -∗ slotFree γ id g -∗ ownRaftGhost γ id s md ={E}=∗
      slotLive γ id q g ∗ ∃ W, pendBatch γ id g S' W ∗
        ownRaftGhost γ id { s with outbox := o' } md ∗
        ([∗list] m ∈ out, □ (durFrags γ id W -∗ isMessage γ m)) ∗
        rdCred γ (rdCount s.outbox - rdCount o') ∗ msgsTks γ out := by
  intro HE Hp Ht Hv Hc Hbc Hself
  iintro #Hdf #HI1 Hlive Hfree Hown
  iunfold ownRaftGhost at Hown
  icases Hown with ⟨%γs, %V, %πc, %kl, H⟩
  iNamed H
  have Hsub : o'.Subperm s.outbox := (List.sublist_append_left o' out).subperm.trans Hp.subperm
  have Hsub2 : out.Subperm s.outbox := (List.sublist_append_right o' out).subperm.trans Hp.subperm
  -- the drained messages, behind the batch's fragments; the kept ones, self-addressed
  ihave #Houtw : ([∗list] m ∈ out, □ (durFrags γ id (virt V πc) -∗ isMessage (GF := GF) γ m)) $$ []
  · iapply BigSepL.bigSepL_forall_elim
    iintro %k %x %Hk
    obtain ⟨j, Hj⟩ := List.mem_iff_getElem?.mp (Hsub2.subset (List.mem_of_getElem? Hk))
    iapply outMsgOk_wand
    iapply BigSepL.bigSepL_lookup (Φ := fun _ m => outMsgOk (GF := GF) γ id s πc (virt V πc) m) Hj
      $$ Hout
  ihave #Ho' : ([∗list] m ∈ o', outMsgOk (GF := GF) γ id { s with outbox := o' } []
      (virt (virt V πc) []) m) $$ []
  · iapply BigSepL.bigSepL_forall_elim
    iintro %k %x %Hk
    have Hxd : x.dst = id := Hself x (List.mem_of_getElem? Hk)
    obtain ⟨j, Hj⟩ := List.mem_iff_getElem?.mp (Hsub.subset (List.mem_of_getElem? Hk))
    ihave #Hw := outMsgOk_wand γ id s πc (virt V πc) x $$ []
    · iapply BigSepL.bigSepL_lookup (Φ := fun _ m => outMsgOk (GF := GF) γ id s πc (virt V πc) m) Hj
        $$ Hout
    unfold outMsgOk
    iright
    rw [virt_nil]
    iframe Hw
    ipureintro; intro h; exact absurd Hxd h
  icases rdOwn_drain γ id s o' out Hp $$ Hrd with ⟨Hrd, Hcr, Htk⟩
  -- the slot: the batch queued in the free generation
  iunfold slotLive at Hlive
  icases Hlive with ⟨%γs1, %H1, Hl⟩
  rw [Hsname] at H1; cases H1
  iunfold slotFree at Hfree
  icases Hfree with ⟨%γs2, %H2, Hfr⟩
  rw [Hsname] at H2; cases H2
  ihave #Hsi := Hslot
  iunfold slotInv at Hsi
  iinv Hsi with H Hclose
  iunfold slotBody at H
  icases H with ⟨%γs', %E0, %g0, %Mq, >%Hγs', >Hsh0, #>Hfr0, #>Hai, >Hv0, >Hg0, >Hq, >%Hdom, >%Hcur, >%Hb⟩
  rw [Hsname] at Hγs'; cases Hγs'
  icombine Hl Hg0 gives %Hgg
  obtain ⟨-, Hgg⟩ := Hgg
  subst Hgg
  icombine Hq Hfr gives %HMq
  have HMq' : Mq !! g = some none := HMq
  icombine Hvirt Hv0 gives %HV
  obtain ⟨-, HV⟩ := HV
  rw [HMq'] at HV
  simp only [virtQ] at HV
  subst HV
  -- the batch's durable invariants (the acknowledgements' leaders: the entered ones' from the
  -- slot, the pending ones' from their justifications)
  ihave #HaiW := acksInF_virt γ id (virt V πc) πc V Hfresh (DurLe_refl _) $$ Hpend []
  · imodintro; iintro -; iexact Hai
  icases cut_durPers γ id s kl (virt V πc) S' Ht Hv Hc Hbc Hhist $$ Hdf Hlead Hlg HaiW
    with ⟨Hlg, #Hdp⟩
  imod ghost_map_update (some ((S', virt V πc, V) : RaftBatch)) $$ Hq Hfr with ⟨Hq, Hpf⟩
  imod ghostVar_update_halves (virt V πc) γs.1 _ _ $$ Hvirt Hv0 with ⟨Hvirt, Hv0⟩
  imod Hclose $$ [Hsh0 Hv0 Hg0 Hq] with -
  · inext
    unfold slotBody
    iexists γs, V, g, Mq.insert g (some ((S', virt V πc, V) : RaftBatch))
    have Hl0 : (Mq.insert g (some ((S', virt V πc, V) : RaftBatch))) !! g =
        some (some ((S', virt V πc, V) : RaftBatch)) := GMap.lookup_insert _ _ _
    rw [Hl0]
    simp only [virtQ]
    iframe Hsh0 Hfr0 Hai Hv0 Hg0 Hq
    ipureintro
    refine ⟨Hsname, ?_, rfl, fun b hb => ?_⟩
    · intro k hk
      by_cases hkg : k = g
      · omega
      · have : (Mq.insert g (some ((S', virt V πc, V) : RaftBatch))) !! k = Mq !! k :=
          GMap.lookup_insert_ne _ _ (Ne.symm hkg)
        rw [this] at hk
        exact Hdom k hk
    · cases hb; exact ⟨rfl, DurLe_virt V πc Hfresh⟩
  imodintro
  isplitl [Hl]
  · unfold slotLive; iexists γs; iframe Hl; ipureintro; exact Hsname
  iexists virt V πc
  iframe Hcr Htk Houtw
  isplitl [Hpf]
  · unfold pendBatch
    iexists γs, V
    iframe Hpf
    isplitr; · ipureintro; exact Hsname
    unfold batchOk
    iexists πc
    iframe Hpend Hdp HI1
    ipureintro; exact ⟨rfl, Hfresh⟩
  iapply ownRaftGhost_intro γ id _ γs (virt V πc) [] kl Hsname Hidnz Hmode (PromsFresh_nil _)
    $$ Hslot Hvirt [] [] [] [] [] [Hlg] [] [] [] [Hlcm] [Hrd]
  · unfold promsJust; iapply (BigSepL.bigSepL_nil).2; iempintro
  · ipureintro; rw [virt_nil]; exact Hhist
  · iexact Ho'
  · iexact Htally
  · rw [show leaderWit (GF := GF) γ id { s with outbox := o' } = leaderWit γ id s from rfl]
    iexact Hlead
  · rw [virt_nil]
    iapply ownLogGhost_mono γ id s _ kl _ (by rfl) (by rfl) (by rfl)
      (by intro h; exact ⟨h, rfl, rfl⟩) (by intro h; exact ⟨h, rfl⟩) (by exact fun h => h) (by rfl)
      (by exact fun h => h) $$ Hlg
  · ipureintro; exact Hlead_ok
  · ipureintro; exact Hfollower_votes
  · ipureintro; exact Hrole_ok
  · rw [show lcmOwn (GF := GF) γ id { s with outbox := o' } = lcmOwn γ id s from rfl]
    iexact Hlcm
  · iexact Hrd

/-! ### Entering a batch: minting its promises (stage II helpers) -/

/-- Every acknowledgement in the event history is in the acknowledgement map (`EvsOk`'s third
part). -/
def AcksEvs (X : DurMaps) : Prop := ∀ t i, Aev.ack t i ∈ X.evs → (X.acks !! (t, i)).isSome

theorem AcksEvs_add (X : DurMaps) (p : Prom) : AcksEvs X → AcksEvs (X.add p) := by
  intro H t i Hm
  cases p with
  | vote T c d Fv =>
    simp only [DurMaps.add, List.mem_append, List.mem_singleton] at Hm ⊢
    rcases Hm with Hm | Hm
    · exact H t i Hm
    · cases Hm
  | ack T i' =>
    simp only [DurMaps.add, List.mem_append, List.mem_singleton] at Hm ⊢
    by_cases Hk : (T, i') = (t, i)
    · rw [Hk, GMap.lookup_insert]; rfl
    · rw [GMap.lookup_insert_ne _ _ Hk]
      rcases Hm with Hm | Hm
      · exact H t i Hm
      · cases Hm; exact absurd rfl Hk
  | camp T F k => exact H t i Hm

theorem EvSorted_prefix (L1 L2 : List Aev) : L1 <+: L2 → EvSorted L2 → EvSorted L1 := by
  intro Hp H p1 p2 e1 e2 Hlt H1 H2
  obtain ⟨t, rfl⟩ := Hp
  have h1 := (List.getElem?_eq_some_iff.mp H1).1
  have h2 := (List.getElem?_eq_some_iff.mp H2).1
  exact H p1 p2 e1 e2 Hlt (by rw [List.getElem?_append_left h1]; exact H1)
    (by rw [List.getElem?_append_left h2]; exact H2)

private theorem auth_halves_q {K V : Type} [DecidableEq K] [Pos.Countable K] [Pos.Countable V]
    (γm : GName) (q : Qp) (m : GMap K V) :
    (ghostMapAuth (GF := GF) γm q m : IProp GF) ⊣⊢ ghostMapAuth γm q.half m ∗ ghostMapAuth γm q.half m := by
  conv => lhs; rw [← Qp.half_add_half q]
  exact (ghostMapAuth_fractional γm m).fractional _ _

private theorem evs_halves (γe : GName) (l : List Aev) :
    (monoListAuthOwn (GF := GF) γe 1 l : IProp GF) ⊣⊢
      monoListAuthOwn γe (1 : Qp).half l ∗ monoListAuthOwn γe (1 : Qp).half l := by
  conv => lhs; rw [← Qp.half_add_half 1]
  exact (monoListAuthOwn_fractional γe l).fractional _ _

/-- Two halves of the promise authorities make the whole (the vote map's half). -/
theorem durShares_combine (γ : RaftNames) (id : w64) (X : DurMaps) :
    durShares (GF := GF) γ id (1 : Qp).half X ∗ durShares γ id (1 : Qp).half X ⊣⊢
      durShares γ id 1 X := by
  unfold durShares
  constructor
  · iintro ⟨⟨%γv, %γa, %γc, %γl, %γe, %Hn, Hv, Ha, Hc, Hl, He⟩,
      ⟨%γv', %γa', %γc', %γl', %γe', %Hn', Hv', Ha', Hc', Hl', He'⟩⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := Hn
    obtain ⟨h1', h2', h3', h4', h5'⟩ := Hn'
    rw [h1] at h1'; rw [h2] at h2'; rw [h3] at h3'; rw [h4] at h4'; rw [h5] at h5'
    cases h1'; cases h2'; cases h3'; cases h4'; cases h5'
    iexists γv, γa, γc, γl, γe
    isplitr; · ipureintro; exact ⟨h1, h2, h3, h4, h5⟩
    isplitl [Hv Hv']
    · iapply (auth_halves_q γv (1 : Qp).half X.voted).2; iframe Hv Hv'
    isplitl [Ha Ha']
    · iapply (ghostMapAuth_halves (GF := GF) γa X.acks).2; iframe Ha Ha'
    isplitl [Hc Hc']
    · iapply (ghostMapAuth_halves (GF := GF) γc X.camps).2; iframe Hc Hc'
    isplitl [Hl Hl']
    · iapply (ghostMapAuth_halves (GF := GF) γl X.vlogs).2; iframe Hl Hl'
    · iapply (evs_halves γe X.evs).2; iframe He He'
  · iintro ⟨%γv, %γa, %γc, %γl, %γe, %Hn, Hv, Ha, Hc, Hl, He⟩
    icases (auth_halves_q γv (1 : Qp).half X.voted).1 $$ Hv with ⟨Hv, Hv'⟩
    icases (ghostMapAuth_halves (GF := GF) γa X.acks).1 $$ Ha with ⟨Ha, Ha'⟩
    icases (ghostMapAuth_halves (GF := GF) γc X.camps).1 $$ Hc with ⟨Hc, Hc'⟩
    icases (ghostMapAuth_halves (GF := GF) γl X.vlogs).1 $$ Hl with ⟨Hl, Hl'⟩
    icases (evs_halves γe X.evs).1 $$ He with ⟨He, He'⟩
    isplitl [Hv Ha Hc Hl He]
    · iexists γv, γa, γc, γl, γe; iframe Hv Ha Hc Hl He; ipureintro; exact Hn
    · iexists γv, γa, γc, γl, γe; iframe Hv' Ha' Hc' Hl' He'; ipureintro; exact Hn

/-- Entering one promise: minted in the authorities from its justification, with its fragments
(a vote through the vote table, with its vote-time log and its event first). -/
theorem mint_one (Em : CoPset) (γ : RaftNames) (id : w64) (X : DurMaps) (p : Prom) :
    ↑(raftLogN γ) ⊆ Em → PromFresh X p → AcksEvs X → EvSorted (X.add p).evs →
    ⊢ raftCommitInv (GF := GF) γ -∗ durShares γ id 1 X -∗ durFrags γ id X -∗ promJust γ id X p
      ={Em}=∗ durShares γ id 1 (X.add p) ∗ durFrags γ id (X.add p) := by
  intro HlE Hfresh Hae Hsort
  iintro #Hci Hsh #Hfr #Hj
  iunfold promJust at Hj
  ihave #Hneed := Hj $$ Hfr
  unfold durShares
  icases Hsh with ⟨%γv, %γa, %γc, %γl, %γe, %Hn, Hv, Ha, Hc, Hl, He⟩
  obtain ⟨Hγv, Hγa, Hγc, Hγl, Hγe⟩ := Hn
  iunfold durFrags at Hfr
  icases Hfr with ⟨#Hfv, #Hfa, #Hfc, #Hfl, %γe', %Hγe', #Hlb⟩
  rw [Hγe] at Hγe'; cases Hγe'
  cases p with
  | camp T F k =>
    simp only [PromFresh] at Hfresh
    iunfold promNeed at Hneed
    icases Hneed with ⟨%Hck, #Hcm⟩
    imod ghost_map_insert_persist T ((F, k) : List EntryM × w64) Hfresh $$ Hc with ⟨Hc, #Hf⟩
    imodintro
    simp only [DurMaps.add]
    isplitl [Hv Ha Hc Hl He]
    · iexists γv, γa, γc, γl, γe
      iframe Hv Ha Hc Hl He
      ipureintro; exact ⟨Hγv, Hγa, Hγc, Hγl, Hγe⟩
    unfold durFrags
    iframe Hfv Hfa Hfl
    isplitr
    · iapply (BigSepM.bigSepM_insert (Φ := fun t (x : List EntryM × w64) =>
        isCampK (GF := GF) γ id t x.1 x.2) Hfresh).2
      iframe Hfc
      unfold isCampK
      iexists γc
      iframe Hf Hcm
      ipureintro; exact ⟨Hγc, Hck⟩
    iexists γe; iframe Hlb; ipureintro; exact Hγe
  | ack T i =>
    imod monoListAuthOwn_update_app [Aev.ack T i] $$ He with ⟨He, #Hlbn⟩
    have Hsort' : EvSorted (X.evs ++ [Aev.ack T i]) := Hsort
    ihave #Hackn : ackEv (GF := GF) γ id T i $$ []
    · unfold ackEv
      iexists γe, (X.evs ++ [Aev.ack T i])
      iframe Hlbn
      ipureintro; exact ⟨Hγe, by simp, Hsort'⟩
    cases hk : X.acks !! (T, i) with
    | none =>
      imod ghost_map_insert_persist (T, i) () hk $$ Ha with ⟨Ha, #Hf⟩
      imodintro
      simp only [DurMaps.add]
      isplitl [Hv Ha Hc Hl He]
      · iexists γv, γa, γc, γl, γe
        iframe Hv Ha Hc Hl He
        ipureintro; exact ⟨Hγv, Hγa, Hγc, Hγl, Hγe⟩
      unfold durFrags
      iframe Hfv Hfc Hfl
      isplitr
      · iapply (BigSepM.bigSepM_insert (Φ := fun (k : w64 × w64) (_ : Unit) =>
          isAcked (GF := GF) γ id k.1 k.2) hk).2
        iframe Hfa
        unfold isAcked
        iright
        iframe Hackn
        iexists γa; iframe Hf; ipureintro; exact Hγa
      iexists γe; iframe Hlbn; ipureintro; exact Hγe
    | some u =>
      have Hid : Std.insert X.acks (T, i) () = X.acks := by
        cases u; exact GMap.insert_id _ _ _ hk
      imodintro
      simp only [DurMaps.add]
      rw [show (<[(T, i) := ()]> X.acks : GMap (w64 × w64) Unit) = X.acks from Hid]
      isplitl [Hv Ha Hc Hl He]
      · iexists γv, γa, γc, γl, γe
        iframe Hv Ha Hc Hl He
        ipureintro; exact ⟨Hγv, Hγa, Hγc, Hγl, Hγe⟩
      unfold durFrags
      iframe Hfv Hfa Hfc Hfl
      iexists γe; iframe Hlbn; ipureintro; exact Hγe
  | vote T c d Fv =>
    simp only [PromFresh] at Hfresh
    have Hsort' : EvSorted (X.evs ++ [Aev.vote T d Fv]) := Hsort
    iunfold promNeed at Hneed
    icases Hneed with ⟨%Fc, #Hcamp, #Hrec, %Hwfu, #Hd, #Hdyn, #Hhs⟩
    imod ghost_map_insert_persist (vlogKey X.vlogs) (((T, d), Fv) : (w64 × Bool) × List EntryM)
      (vlogKey_fresh X.vlogs) $$ Hl with ⟨Hl, #Hvlf⟩
    imod monoListAuthOwn_update_app [Aev.vote T d Fv] $$ He with ⟨He, #Hlbn⟩
    ihave #Hvlog : isVlog (GF := GF) γ id (vlogKey X.vlogs) T d Fv $$ []
    · unfold isVlog; iexists γl; iframe Hvlf; ipureintro; exact Hγl
    ihave #Hvev : voteEv (GF := GF) γ id T d Fv $$ []
    · unfold voteEv
      iexists γe, X.evs
      iframe Hlbn
      isplitr; · ipureintro; exact Hγe
      iintro %t %i %Hti
      obtain ⟨Hm, Hlt⟩ := Hti
      obtain ⟨u, hu⟩ : ∃ u, X.acks !! (t, i) = some u := by
        have := Hae t i Hm
        cases h : X.acks !! (t, i) with
        | none => rw [h] at this; cases this
        | some u => exact ⟨u, rfl⟩
      ihave Hh := BigSepM.bigSepM_lookup (Φ := fun (k : w64 × w64) (_ : Unit) =>
        iprop(∀ (_ : uint.Z k.1 < uint.Z T), hist (GF := GF) γ Fv k.1 k.2 (vbnd T d))) hu $$ Hhs
      iapply Hh $$ %Hlt
    ihave #Hvj : voteJust (GF := GF) γ id T c $$ []
    · unfold voteJust
      iexists (vlogKey X.vlogs), d, Fv, Fc
      iframe Hvlog Hcamp Hrec Hvev Hdyn
      isplitr; · ipureintro; exact Hwfu
      cases d with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      | true =>
        simp only [↓reduceIte]
        icases Hd with (%Hf | #Hw)
        · cases Hf
        · iexact Hw
    -- the vote, into the vote table
    ihave #Hli := raftCommitInv_log γ $$ Hci
    unfold raftLogInv
    have HlE' := HlE
    iinv Hli with H Hclose
    iunfold raftLogInvBody at H
    icases H with ⟨%l, >Hauth, >Hjust, >Htbl, >Hwt, >Hrest⟩
    imod votesTbl_insert γ id γv X.voted T c Hγv Hfresh $$ Hvj Htbl Hv with ⟨Htbl, Hv, #Hvf⟩
    imod Hclose $$ [Hauth Hjust Htbl Hwt Hrest] with -
    · inext; unfold raftLogInvBody; iexists l; iframe Hauth Hjust Htbl Hwt Hrest
    imodintro
    simp only [DurMaps.add]
    isplitl [Hv Ha Hc Hl He]
    · iexists γv, γa, γc, γl, γe
      iframe Hv Ha Hc Hl He
      ipureintro; exact ⟨Hγv, Hγa, Hγc, Hγl, Hγe⟩
    unfold durFrags
    iframe Hfa Hfc
    isplitr
    · iapply (BigSepM.bigSepM_insert (Φ := fun (t : w64) (c : w64) => isVote (GF := GF) γ id t c)
        Hfresh).2
      iframe Hfv
      unfold isVote; iexists γv; iframe Hvf; ipureintro; exact Hγv
    isplitr
    · iapply (BigSepM.bigSepM_insert (Φ := fun (n : Nat) (x : (w64 × Bool) × List EntryM) =>
        isVlog (GF := GF) γ id n x.1.1 x.1.2 x.2) (vlogKey_fresh X.vlogs)).2
      iframe Hfl Hvlog
    iexists γe; iframe Hlbn; ipureintro; exact Hγe

/-- Entering a pending list, in order. -/
theorem mint_list (Em : CoPset) (γ : RaftNames) (id : w64) :
    ∀ (π : List Prom) (X : DurMaps),
    ↑(raftLogN γ) ⊆ Em → PromsFresh X π → AcksEvs X → EvSorted (virt X π).evs →
    ⊢ raftCommitInv (GF := GF) γ -∗ durShares γ id 1 X -∗ durFrags γ id X -∗ promsJust γ id X π
      ={Em}=∗ durShares γ id 1 (virt X π) ∗ durFrags γ id (virt X π)
  | [], X, _, _, _, _ => by
    iintro #_ Hsh #Hfr #_
    imodintro
    rw [virt_nil]
    iframe Hsh Hfr
  | p :: π, X, HlE, Hfr, Hae, Hsort => by
    rw [PromsFresh_cons] at Hfr
    obtain ⟨Hf1, Hf2⟩ := Hfr
    rw [virt_cons] at Hsort ⊢
    have Hs1 : EvSorted (X.add p).evs :=
      EvSorted_prefix _ _ (DurLe_virt (X.add p) π Hf2).2.2.2.2 Hsort
    iintro #Hci Hsh #Hfrg #Hj
    icases (promsJust_cons γ id X p π).1 $$ Hj with ⟨#Hj1, #Hj2⟩
    imod mint_one Em γ id X p HlE Hf1 Hae Hs1 $$ Hci Hsh Hfrg Hj1 with ⟨Hsh, #Hfrg'⟩
    iapply mint_list Em γ id π (X.add p) HlE Hf2 (AcksEvs_add X p Hae) Hsort
      $$ Hci Hsh Hfrg' Hj2

/-- **Entering a batch** (the client's *enter*, under the node's generation): its promises minted
in order in the authorities (`vote_insert`, `ghost_map_insert_persist` of the acknowledgements,
campaign records and vote-time logs, the event history's appends), from their justifications; the
durable half moved to the batch's state; the batch's fragments out, which discharge its drained
messages' wands; the generation's queue free again. -/
theorem raft_enter (E : CoPset) (γ : RaftNames) (id : w64) (S : RaftState) (q : Qp) (g : Nat)
    (S' : RaftState) (W : DurMaps) :
    ↑(raftN γ) ⊆ E →
    -- (2026-11-02, stage II (p)) the batch moves `wcommit` to its commit, or writes nothing
    -- (`RaftState.next_wcommit`)
    (S'.wcommit = S'.commit ∨ (S'.wcommit = S.wcommit ∧ S'.base = S.base ∧ S'.ents = S.ents)) →
    ⊢ ownDurGhost (GF := GF) γ id S -∗ slotLive γ id q g -∗ pendBatch γ id g S' W ={E}=∗
      ownDurGhost γ id S' ∗ slotLive γ id q g ∗ slotFree γ id g ∗ durFrags γ id W := by
  intro HE HwS
  have HsE : (↑(slotN γ id) : CoPset) ⊆ E := fun p hp => HE p (slotN_raftN γ id p hp)
  have HlE : (↑(raftLogN γ) : CoPset) ⊆ E \ ↑(slotN γ id) := by
    intro p hp
    rw [Iris.Std.LawfulSet.mem_diff]
    refine ⟨raftLogN_of HE p hp, fun h => ?_⟩
    have h1 := nclose_subseteq (raftN γ .@ "slot") id p h
    exact ndot_ne_disjoint (raftN γ) (show "log" ≠ "slot" by decide) p ⟨hp, h1⟩
  iintro Hdur Hlive Hpend
  unfold ownDurGhost
  icases Hdur with ⟨%E1, Hsh1, #Hdp, #Hsinv, #HI1⟩
  iunfold slotLive at Hlive
  icases Hlive with ⟨%γs, %Hγs, Hl⟩
  iunfold pendBatch at Hpend
  icases Hpend with ⟨%γs2, %Ep, %H2, Hpf, #Hbo⟩
  rw [Hγs] at H2; cases H2
  ihave #Hsi := Hsinv
  iunfold slotInv at Hsi
  iinv Hsi with H Hclose
  iunfold slotBody at H
  icases H with ⟨%γs', %E0, %g0, %Mq, >%Hγs', >Hsh0, #>Hfr0, #>Hai0, >Hv0, >Hg0, >Hq, >%Hdom, >%Hcur, >%Hb⟩
  rw [Hγs] at Hγs'; cases Hγs'
  icombine Hl Hg0 gives %Hgg
  obtain ⟨-, Hgg⟩ := Hgg
  subst Hgg
  icombine Hq Hpf gives %HMq
  have HMq' : Mq !! g = some (some ((S', W, Ep) : RaftBatch)) := HMq
  obtain ⟨HEp, -⟩ := Hb _ HMq'
  simp only at HEp
  subst Ep
  iunfold batchOk at Hbo
  icases Hbo with ⟨%π, %Hπ, #Hj, #Hdp', #HI1'⟩
  obtain ⟨HW, Hfresh⟩ := Hπ
  simp only at HW Hfresh
  icases durShares_agree γ id _ _ E0 E1 $$ Hsh0 Hsh1 with ⟨Hsh0, Hsh1, %HE1⟩
  subst HE1
  ihave #Hdp0 := Hdp
  iunfold durPers at Hdp0
  icases Hdp0 with ⟨%kd, %fp0, %Hp0, -, -, -, -, -, -, -, -, -, #Hci, -⟩
  have Hae : AcksEvs E0 := Hp0.2.2.2.1.2.2
  ihave #Hdp'' := Hdp'
  iunfold durPers at Hdp''
  icases Hdp'' with ⟨%kd', %fp', %Hp', -, -, -, -, -, -, -, -, -, -, #HaiW⟩
  have Hsort : EvSorted (virt E0 π).evs := by rw [← HW]; exact Hp'.2.2.2.1.1
  icases (durShares_combine γ id E0).1 $$ [Hsh0 Hsh1] with Hsh
  · iframe Hsh0 Hsh1
  imod mint_list (E \ ↑(slotN γ id)) γ id π E0 HlE Hfresh Hae Hsort $$ Hci Hsh Hfr0 Hj
    with ⟨Hsh, #HfrW⟩
  rw [← HW]
  ihave #HaiW' := HaiW $$ HfrW
  icases (durShares_combine γ id W).2 $$ Hsh with ⟨Hsh0, Hsh1⟩
  imod ghost_map_update (none : Option RaftBatch) $$ Hq Hpf with ⟨Hq, Hfree⟩
  have HvQ : virtQ E0 (Mq !! g) = W := by rw [HMq']; rfl
  rw [HvQ]
  imod Hclose $$ [Hsh0 Hv0 Hg0 Hq] with -
  · inext
    unfold slotBody
    iexists γs, W, g, Mq.insert g none
    have Hl0 : (Mq.insert g (none : Option RaftBatch)) !! g = some none := GMap.lookup_insert _ _ _
    rw [Hl0]
    simp only [virtQ]
    iframe Hsh0 HfrW HaiW' Hv0 Hg0 Hq
    ipureintro
    refine ⟨Hγs, ?_, rfl, fun b hb => by cases hb⟩
    intro k hk
    by_cases hkg : k = g
    · omega
    · have : (Mq.insert g (none : Option RaftBatch)) !! k = Mq !! k :=
        GMap.lookup_insert_ne _ _ (Ne.symm hkg)
      rw [this] at hk
      exact Hdom k hk
  imodintro
  isplitl [Hsh1]
  · iexists W; iframe Hsh1 Hdp' Hsinv
    rcases HwS with hw | ⟨hw, hb, he⟩
    · iapply durI1_congr γ rfl rfl hw $$ HI1'
    · iapply durI1_congr γ hb he hw $$ HI1
  isplitl [Hl]
  · unfold slotLive; iexists γs; iframe Hl; ipureintro; exact Hγs
  isplitl [Hfree]
  · unfold slotFree; iexists γs; iframe Hfree; ipureintro; exact Hγs
  iexact HfrW

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
  icases Hd with ⟨%kd, %fp0, %Hp, #HrS, -, #Hfp0, #Hvl, #Hhs, #Hkl, -, #Hci, #Hc, #Hinv, -⟩
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

/-- (stage II helper) A cut of `S`'s full log at a base `b` within its log: the same full log. -/
private theorem entsFrom_full (S : RaftState) (fp0 : List EntryM) (b : entryID) :
    FullOk S.base fp0 → PlogWf S.base S.ents → uint.Z S.base.index' ≤ uint.Z b.index' →
    plogTermAt S.base S.ents b.index' = some b.term' →
    ∃ fpb, FullOk b fpb ∧ fpb ++ S.entsFrom b = fp0 ++ S.ents := by
  intro HfullS HwfS Hb1 Hbt
  have HwfF : PlogWf base0 (fp0 ++ S.ents) := full_wf _ _ _ HfullS HwfS
  have Hbt' : plogTermAt base0 (fp0 ++ S.ents) b.index' = some b.term' := by
    rw [full_term_at _ _ _ _ HfullS Hb1]; exact Hbt
  generalize HF : fp0 ++ S.ents = F at HwfF Hbt'
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
  exact ⟨F.take m, HfB, by rw [← Hdrop, List.take_append_drop]⟩

/-- (stage II helper) A resource threaded through a map of persistent facts, element by element. -/
private theorem bigSepM_keep (R : IProp GF) (Φ Ψ : w64 × w64 → Unit → IProp GF)
    [∀ k x, Persistent (Φ k x)] [∀ k x, Persistent (Ψ k x)] :
    ∀ m : GMap (w64 × w64) Unit, (∀ k x, R ∗ Φ k x ⊢ R ∗ Ψ k x) →
      R ∗ ([∗map] k ↦ x ∈ m, Φ k x) ⊢ R ∗ [∗map] k ↦ x ∈ m, Ψ k x := by
  intro m Hstep
  induction m using GMap.map_ind with
  | h0 =>
    iintro ⟨HR, -⟩
    iframe HR
    iapply (BigSepM.bigSepM_empty).2; iempintro
  | hins k v m Hk IH =>
    iintro ⟨HR, Hm⟩
    icases (BigSepM.bigSepM_insert (Φ := Φ) Hk).1 $$ Hm with ⟨#H1, #Hm⟩
    icases Hstep k v $$ [$HR $H1] with ⟨HR, #H1'⟩
    icases IH $$ [$HR $Hm] with ⟨HR, #Hm'⟩
    iframe HR
    iapply (BigSepM.bigSepM_insert (Φ := Ψ) Hk).2
    iframe H1' Hm'

/-- (stage II helper) **One acknowledgement at a restart** (R4, repair 1): an acknowledgement
`(S.term, i)` above the stored commit `c` agrees with the restarted log `(b, es)` (a cut of the full
log `F`): above `S.commit` by `durPers`'s `ackAgree`; in `(c, S.commit]` because its leader's log
(`ackInF`) holds the committed prefix up to `S.commit` -- by `S.commit`'s certificate: the
bootstrap log; a commit fact of `S.term` (the same leader's log, `leadPrefix_agree`); or a commit
fact of an earlier term, which Leader Completeness (`lc_core`, the vote table) puts in it. -/
private theorem restart_ack_one (γ : RaftNames) (S : RaftState) (F : List EntryM) (b : entryID)
    (es : List EntryM) (c : w64) (k : w64 × w64) :
    PlogWf base0 F → uint.Z S.commit ≤ plogLastIndexZ base0 F →
    uint.Z S.base.index' ≤ uint.Z S.commit →
    (∀ j, uint.Z S.base.index' ≤ uint.Z j → plogTermAt S.base S.ents j = plogTermAt base0 F j) →
    plogLastIndexZ S.base S.ents = plogLastIndexZ base0 F →
    (∀ j, uint.Z b.index' ≤ uint.Z j → plogTermAt b es j = plogTermAt base0 F j) →
    plogLastIndexZ b es = plogLastIndexZ base0 F →
    uint.Z b.index' ≤ uint.Z c →
    iprop(votesTbl (GF := GF) γ ∗ logRecs γ base0 F ∗ commitIn γ F S.commit S.term) ∗
      iprop((∀ (_ : k.1 = S.term ∧ uint.Z S.commit < uint.Z k.2), ackAgree γ S.base S.ents k.1 k.2) ∗
        ackInF γ k.1 k.2) ⊢
    iprop(votesTbl γ ∗ logRecs γ base0 F ∗ commitIn γ F S.commit S.term) ∗
      iprop(∀ (_ : k.1 = S.term ∧ uint.Z c < uint.Z k.2), ackAgree γ b es k.1 k.2) := by
  intro HwF HcF HsC HtS HlS HtB HlB Hbc
  iintro ⟨⟨Htbl, #HrF, #Hci⟩, ⟨#Hag, #Hai⟩⟩
  by_cases Hk : ¬ (k.1 = S.term ∧ uint.Z c < uint.Z k.2)
  · iframe Htbl HrF Hci
    iintro %h; exact absurd h Hk
  obtain ⟨Hk1, Hk2⟩ := Classical.not_not.mp Hk
  by_cases Hhi : uint.Z S.commit < uint.Z k.2
  · -- above `S.commit`: `durPers`'s own agreement, re-based
    ihave #Ha := Hag $$ %(And.intro Hk1 Hhi)
    iunfold ackAgree at Ha
    icases Ha with ⟨%Hi, %X, #HX, %HagE⟩
    iframe Htbl HrF Hci
    iintro %_
    unfold ackAgree
    isplitr; · ipureintro; rw [HlB, ← HlS]; exact Hi
    iexists X
    iframe HX
    ipureintro
    refine ⟨HagE.1, ?_⟩
    rw [HagE.2, HtS k.2 (by omega), HtB k.2 (by omega)]
  -- in `(c, S.commit]`: the acknowledgement's leader's full log
  iunfold ackInF at Hai
  icases Hai with (%H0 | ⟨%X, #HX, %HiX⟩)
  · exfalso; have := uint_Z_nonneg c; omega
  icases leadFull_wf γ _ _ $$ HX with ⟨%HwL, #HrL⟩
  have HlenL : plogLastIndexZ base0 X = (X.length : Int) := by
    unfold plogLastIndexZ; rw [base0_index]; simp
  have HlenF : plogLastIndexZ base0 F = (F.length : Int) := by
    unfold plogLastIndexZ; rw [base0_index]; simp
  have HsX : (plogTermAt base0 X k.2).isSome :=
    plogTermAt_in_range _ _ _ ⟨by rw [base0_index]; exact uint_Z_nonneg _, HiX⟩
  -- the leader's full log agrees with `F` at the index, by `S.commit`'s certificate
  ihave Hagr : iprop(votesTbl (GF := GF) γ ∗
      ⌜plogTermAt base0 X k.2 = plogTermAt base0 F k.2⌝) $$ [Htbl]
  · ihave #Hcj := commitIn_j γ F S.commit S.term $$ Hci
    unfold commitJ
    icases Hcj with (%Hb0 | ⟨%t', %n, %G, #Hq, %Hcn⟩)
    · -- the bootstrap log, which both start with
      iframe Htbl
      icases logRecs_boot_termAt γ F HwF $$ HrF with %HbF
      icases logRecs_boot_termAt γ _ HwL.1 $$ HrL with %HbL
      ipureintro
      rw [← HbL k.2 (by omega) (by omega), ← HbF k.2 (by omega) (by omega)]
    obtain ⟨Hcn, Htt, HGF⟩ := Hcn
    icases cq_base γ t' n G $$ Hq with ⟨%HGn, #HGl⟩
    icases leadFull_wf γ t' G $$ HGl with ⟨%HwG, #HrG⟩
    have Hn := (plogTermAt_some_range _ _ _ _ HGn).2
    icases full_match γ G F S.commit HwG.1 HwF
        (plogTermAt_in_range _ _ _ ⟨by rw [base0_index]; exact uint_Z_nonneg _, by omega⟩) HGF
        $$ HrG HrF with %HGFall
    by_cases Hne : t' = S.term
    · -- a commit fact of `S.term`: two full logs of the same leader
      have Ht' : t' = k.1 := Hne.trans Hk1.symm
      subst Ht'
      icases leadFull_agree γ k.1 X G k.2 HsX
          (plogTermAt_in_range _ _ _ ⟨by rw [base0_index]; exact uint_Z_nonneg _, by omega⟩)
          $$ HX HGl with %HXG
      iframe Htbl
      ipureintro
      rw [HXG, HGFall k.2 (by omega)]
    · -- a commit fact of an earlier term: Leader Completeness
      have Hlt : uint.Z t' < uint.Z k.1 := by
        have : uint.Z t' ≠ uint.Z S.term := fun h => Hne (uint_Z_inj.mp h)
        rw [Hk1]; omega
      icases leadFull_camp γ k.1 X $$ HX with ⟨%ldr2, %F0, #Hl2, #Hc0, %Hpre⟩
      icases isCamp_ok γ ldr2 k.1 F0 $$ Hc0 with %Hcok
      have Hcl := camp_last k.1 F0 Hcok
      icases lc_core γ ((uint.Z k.1).toNat + 1) k.1 t' n G ldr2 F0 X
          (by have := uint_Z_nonneg k.1; omega) Hlt HwL.1
          (by rw [plogTermAt_prefix _ F0 _ _ Hpre (by rw [Hcl]; rfl)]; exact Hcl)
          $$ Htbl Hq Hl2 Hc0 HrL with %HnL
      have Hnr := (plogTermAt_some_range _ _ _ _ HnL).2
      icases full_match γ X G n HwL.1 HwG.1 (by rw [HnL]; rfl) (by rw [HnL, HGn])
          $$ HrL HrG with %HLG
      iframe Htbl
      ipureintro
      rw [HLG k.2 (by omega), HGFall k.2 (by omega)]
  icases Hagr with ⟨Htbl, %Hagr⟩
  iframe Htbl HrF Hci
  iintro %_
  unfold ackAgree
  isplitr; · ipureintro; rw [HlB]; omega
  iexists X
  iframe HX
  ipureintro
  refine ⟨HsX, ?_⟩
  rw [Hagr, HtB k.2 (by omega)]

/-- **R4, the acknowledgements at a restart**: every acknowledgement of `S.term` above a lower
stored commit `c` agrees with the restarted log -- above `S.commit` by `durPers`, in
`(c, S.commit]` by Leader Completeness (the committed prefix is in the log of `S.term`'s leader,
which the acknowledgement's `ackInF`, kept by `durPers`, names: repair 1, 2026-11-01). -/
theorem durPers_restart_acks (E : CoPset) (γ : RaftNames) (id : w64) (S : RaftState) (Ed : DurMaps)
    (b : entryID) (c : w64) :
    ↑(raftN γ) ⊆ E →
    uint.Z S.base.index' ≤ uint.Z b.index' → uint.Z b.index' ≤ uint.Z c →
    uint.Z c ≤ uint.Z S.commit →
    plogTermAt S.base S.ents b.index' = some b.term' →
    ⊢ durPers (GF := GF) γ id S Ed -∗ durFrags γ id Ed ={E}=∗
      [∗map] k ↦ _u ∈ Ed.acks, ∀ (_ : k.1 = S.term ∧ uint.Z c < uint.Z k.2),
        ackAgree γ b (S.entsFrom b) k.1 k.2 := by
  intro HE Hb1 Hb2 Hb3 Hbt
  have HlE : (↑(raftLogN γ) : CoPset) ⊆ E := raftLogN_of HE
  iintro #Hd #Hfr
  iunfold durPers at Hd
  icases Hd with ⟨%kd, %fp0, %Hp, #HrS, -, #Hfp0, -, -, -, #Hag, #Hci, -, #Hinv, #HaiW⟩
  obtain ⟨-, -, -, -, HfullS, HwfS, -, HsC, HcL⟩ := Hp
  ihave #Hai := HaiW $$ Hfr
  obtain ⟨fpb, Hfb, Hfeq⟩ := entsFrom_full S fp0 b HfullS HwfS Hb1 Hbt
  have HwF : PlogWf base0 (fp0 ++ S.ents) := full_wf _ _ _ HfullS HwfS
  ihave #HrF := logRecs_full γ S.base fp0 S.ents HfullS $$ Hfp0 HrS
  have HlS : plogLastIndexZ S.base S.ents = plogLastIndexZ base0 (fp0 ++ S.ents) :=
    (full_last_index _ _ _ HfullS).symm
  have HlB : plogLastIndexZ b (S.entsFrom b) = plogLastIndexZ base0 (fp0 ++ S.ents) := by
    rw [← full_last_index _ _ _ Hfb, Hfeq]
  have HtS : ∀ j, uint.Z S.base.index' ≤ uint.Z j →
      plogTermAt S.base S.ents j = plogTermAt base0 (fp0 ++ S.ents) j :=
    fun j hj => (full_term_at _ _ _ _ HfullS hj).symm
  have HtB : ∀ j, uint.Z b.index' ≤ uint.Z j →
      plogTermAt b (S.entsFrom b) j = plogTermAt base0 (fp0 ++ S.ents) j := by
    intro j hj; rw [← full_term_at _ _ _ _ Hfb hj, Hfeq]
  -- the vote table, for Leader Completeness
  ihave #Hli := raftCommitInv_log γ $$ Hinv
  unfold raftLogInv
  iinv Hli with H Hclose
  iunfold raftLogInvBody at H
  icases H with ⟨%l, >Hauth, >Hjust, >Htbl, >Hwt, >Hrest⟩
  icases bigSepM_keep (iprop(votesTbl (GF := GF) γ ∗ logRecs γ base0 (fp0 ++ S.ents) ∗
      commitIn γ (fp0 ++ S.ents) S.commit S.term))
      (fun k _ => iprop((∀ (_ : k.1 = S.term ∧ uint.Z S.commit < uint.Z k.2),
        ackAgree (GF := GF) γ S.base S.ents k.1 k.2) ∗ ackInF γ k.1 k.2))
      (fun k _ => iprop(∀ (_ : k.1 = S.term ∧ uint.Z c < uint.Z k.2),
        ackAgree (GF := GF) γ b (S.entsFrom b) k.1 k.2))
      Ed.acks (fun k _ => restart_ack_one γ S (fp0 ++ S.ents) b (S.entsFrom b) c k HwF
        (by rw [← HlS]; exact HcL) HsC HtS HlS HtB HlB Hb2)
      $$ [Htbl] with ⟨⟨Htbl, -, -⟩, #Hres⟩
  · iframe Htbl HrF Hci
    iapply BigSepM.bigSepM_forall.2
    iintro %k %u %hk
    isplitr
    · iapply (BigSepM.bigSepM_lookup (Φ := fun (k : w64 × w64) (_ : Unit) =>
        iprop(∀ (_ : k.1 = S.term ∧ uint.Z S.commit < uint.Z k.2),
          ackAgree (GF := GF) γ S.base S.ents k.1 k.2)) hk) $$ Hag
    · iapply (BigSepM.bigSepM_lookup (Φ := fun (k : w64 × w64) (_ : Unit) =>
        ackInF (GF := GF) γ k.1 k.2) hk) $$ Hai
  imod Hclose $$ [Hauth Hjust Htbl Hwt Hrest] with -
  · inext; unfold raftLogInvBody; iexists l; iframe Hauth Hjust Htbl Hwt Hrest
  imodintro
  iexact Hres

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
theorem raft_restart (E : CoPset) (γ : RaftNames) (id : w64) {md : Bool}
    (b : entryID) (c : w64) (Φ : RaftState → Prop) (R : RaftState → IProp GF) :
    ↑(raftN γ) ⊆ E →
    γ.reDyn.isSome = md →
    (∀ S, Φ S → uint.Z S.base.index' ≤ uint.Z b.index' ∧ uint.Z b.index' ≤ uint.Z c ∧
      uint.Z c ≤ uint.Z S.commit ∧ plogTermAt S.base S.ents b.index' = some b.term' ∧
      -- (2026-11-02, stage II (p)) at or above the commit of the last batch that wrote the log
      uint.nat S.wcommit ≤ uint.nat c) →
    (γ.reBoot.length : Int) ≤ uint.Z c →
    ⊢ raftIdSlot (GF := GF) γ id -∗
      (|={E \ ↑(slotN γ id), ∅}=> ∃ S, ownDurGhost γ id S ∗ ⌜Φ S⌝ ∗
        (ownDurGhost γ id S ={∅, E \ ↑(slotN γ id)}=∗ R S)) ={E}=∗
      ∃ S, ⌜Φ S⌝ ∗ R S ∗ ownRaftGhost γ id (restartP S b c) md ∗
        ∃ g, slotLive γ id 1 g ∗ slotFree γ id g ∗
        -- (2026-11-02, stage II (p)) I1 of the restarted log at the commit (`durI1_rebase`)
        □ (∀ fp, ⌜FullOk b fp⌝ -∗ logRecs γ base0 fp -∗
          ⌜md = true → ConfI1 (fp ++ S.entsFrom b) (uint.nat c)⌝) := by
  intro HE Hmd HΦ Hboot
  iintro Hslot Hacc
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
  icases H with ⟨%γs', %E0, %g0, %Mq, >%Hγs', >Hsh0, #>Hfr0, #>Hai0, >Hv0, >Hg0, >Hq, >%Hdom, >%Hcur, >%Hb⟩
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
  -- the durable half, through the accessor (the client's update: `RestartNode`'s), while the slot
  -- is open
  imod Hacc with ⟨%S, Hdur, %HS, Hcl⟩
  obtain ⟨Hb1, Hb2, Hb3, Hbt, Hwc⟩ := HΦ S HS
  unfold ownDurGhost
  icases Hdur with ⟨%E1, Hsh1, #Hdp, #Hsinv1, #HI1⟩
  icases durShares_agree γ id _ _ V E1 $$ Hsh0 Hsh1 with ⟨Hsh0, Hsh1, %HE1⟩
  subst HE1
  -- the leader-side keys: entered campaigns' terms
  icases keys_camps γ id _ V (fun t (x : TermRec) => iprop(t ↪[γm]□ x)) terms $$ [$Hsh1 $Htf]
    with ⟨Hsh1, %Ktm⟩
  icases keys_camps γ id _ V (fun t (x : GSet w64) => iprop(t ↪[γw]□ x)) wins $$ [$Hsh1 $Hwf]
    with ⟨Hsh1, %Kwn⟩
  icases keys_camps γ id _ V (fun t (x : GName) => iprop(t ↪[γl]□ x)) lcm $$ [$Hsh1 $Hlf]
    with ⟨Hsh1, %Kln⟩
  icases keys_camps γ id _ V (fun t (x : GName) => iprop(t ↪[γq]□ x)) rqm $$ [$Hsh1 $Hqf]
    with ⟨Hsh1, %Kqn⟩
  ihave #HI1r := durI1_rebase γ id S V b c Hb1 Hbt Hwc $$ Hdp HI1
  imod Hcl $$ [Hsh1] with HR
  · iexists V; iframe Hsh1 Hdp Hsinv1 HI1
  imod Hclose $$ [Hsh0 Hv0 Hg0 Hq] with -
  · inext
    unfold slotBody
    iexists γs, V, g, Mq
    iframe Hsh0 Hfr0 Hai0 Hv0 Hg0 Hq
    ipureintro; exact ⟨Hγs, Hdom, Hcur, Hb⟩
  -- the durable invariants, re-based at `b` and `c`
  icases durPers_rebase γ id S V b c Hb1 Hb2 Hb3 Hbt $$ Hdp with
    ⟨%kd, %fp, %Hp, #Hrb, #Hbb, #Hfp, #Hvl, #Hhs, #Hkl, #Hci, #Hcm, -⟩
  obtain ⟨Hvh, Hak, Hcp, Hev, HfB, Hwfb, Hterms_le, HcL⟩ := Hp
  imod durPers_restart_acks E γ id S V b c HE Hb1 Hb2 Hb3 Hbt $$ Hdp Hfr0 with #Hacks
  imod rdCred_zero (GF := GF) γ with Hcr0
  have Hterm : (restartP S b c).term = S.term := rfl
  have Hrole : (restartP S b c).role = .follower := rfl
  have Hbase : (restartP S b c).base = b := rfl
  have Hlog : (restartP S b c).log = S.entsFrom b := rfl
  have Hcommit : (restartP S b c).commit = c := rfl
  have Hvote : (restartP S b c).vote = S.vote := rfl
  imodintro
  iexists S
  isplitr; · ipureintro; exact HS
  iframe HR
  isplitr [Hl Hfr]

  rotate_left
  · iexists g
    isplitl [Hl]
    · unfold slotLive; iexists γs; iframe Hl; ipureintro; exact Hγs
    isplitl [Hfr]
    · unfold slotFree; iexists γs; iframe Hfr; ipureintro; exact Hγs
    rw [← Hmd]; iexact HI1r
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

/-- (stage II helper) Every entry of the bootstrap log is of term `1`: the commit invariant's boot
arm records it, and a commit fact's log starts with the boot log, whose records say so. -/
private theorem boot_terms (E : CoPset) (γ : RaftNames) :
    ↑(raftN γ) ⊆ E → ⊢ raftCommitInv (GF := GF) γ ={E}=∗ ⌜∀ e ∈ γ.reBoot, e.Term' = W64 1⌝ := by
  intro HE
  iintro #Hci
  ihave #Hli := raftCommitInv_log γ $$ Hci
  have HlE : (↑(raftLogN γ) : CoPset) ⊆ E := raftLogN_of HE
  unfold raftLogInv
  iinv Hli with H Hclose
  unfold raftLogInvBody
  icases H with ⟨%l, >Hauth, >Hj, >Htbl, >Hwt, >Hrest⟩
  icases Hj with #Hj
  ihave #Hj' := Hj
  iunfold committedJust at Hj'
  imod Hclose $$ [Hauth Hj Htbl Hwt Hrest] with -
  · inext; iexists l; iframe Hauth Hj Htbl Hwt Hrest
  imodintro
  icases Hj' with (%Ha | ⟨%t, %n, %G, %ldr, #Hq, -, -, -⟩)
  · ipureintro; exact Ha.2.2
  · icases cq_boot γ t n G $$ Hq with %Hb
    icases cq_full γ t n G $$ Hq with ⟨%HwG, #HrG⟩
    icases logRecs_boot_wf γ G HwG $$ HrG with %Hw
    ipureintro; exact (Hw Hb.1).2

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
  · obtain ⟨Hl, Hwf, -⟩ := Ha
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
theorem raft_start_boot (E : CoPset) (γ : RaftNames) (id : w64) {md : Bool} (R : IProp GF) :
    ↑(raftN γ) ⊆ E →
    γ.reDyn.isSome = md →
    ⊢ raftIdSlot (GF := GF) γ id -∗
      (|={E \ ↑(slotN γ id), ∅}=> ownDurGhost γ id RaftState.init ∗
        (ownDurGhost γ id RaftState.init ={∅, E \ ↑(slotN γ id)}=∗ R)) ={E}=∗
      R ∗ ownRaftGhost γ id (bootPState γ.reBoot) md ∗
      ∃ g, slotLive γ id 1 g ∗ slotFree γ id g := by
  intro HE Hmd
  iintro Hslot Hacc
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
  icases H with ⟨%γs', %E0, %g0, %Mq, >%Hγs', >Hsh0, #>Hfr0, #>Hai0, >Hv0, >Hg0, >Hq, >%Hdom, >%Hcur, >%Hb⟩
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
  -- the durable half, through the accessor (the client's update: `StartNode`'s), while the slot
  -- is open
  imod Hacc with ⟨Hdur, Hcl⟩
  unfold ownDurGhost
  icases Hdur with ⟨%E1, Hsh1, #Hdp, #Hsinv1, #HI1⟩
  icases durShares_agree γ id _ _ V E1 $$ Hsh0 Hsh1 with ⟨Hsh0, Hsh1, %HE1⟩
  subst HE1
  -- the leader-side keys: entered campaigns' terms
  icases keys_camps γ id _ V (fun t (x : TermRec) => iprop(t ↪[γm]□ x)) terms $$ [$Hsh1 $Htf]
    with ⟨Hsh1, %Ktm⟩
  icases keys_camps γ id _ V (fun t (x : GSet w64) => iprop(t ↪[γw]□ x)) wins $$ [$Hsh1 $Hwf]
    with ⟨Hsh1, %Kwn⟩
  icases keys_camps γ id _ V (fun t (x : GName) => iprop(t ↪[γl]□ x)) lcm $$ [$Hsh1 $Hlf]
    with ⟨Hsh1, %Kln⟩
  icases keys_camps γ id _ V (fun t (x : GName) => iprop(t ↪[γq]□ x)) rqm $$ [$Hsh1 $Hqf]
    with ⟨Hsh1, %Kqn⟩
  imod Hcl $$ [Hsh1] with HR
  · iexists V; iframe Hsh1 Hdp Hsinv1 HI1
  imod Hclose $$ [Hsh0 Hv0 Hg0 Hq] with -
  · inext
    unfold slotBody
    iexists γs, V, g, Mq
    iframe Hsh0 Hfr0 Hai0 Hv0 Hg0 Hq
    ipureintro; exact ⟨Hγs, Hdom, Hcur, Hb⟩
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
  iframe HR
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
  icases H with ⟨%γs', %E0, %g0, %Mq, >%Hγs', >Hsh, #Hfr, #Hai, >Hv', >Hg', >Hq, >%Hdom, >%Hcur, -⟩
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
    iframe Hsh Hfr Hai Hg' Hq
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
    ipureintro; intro b hb; cases hb
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
