/-
`handleAcceptReply` keeps the invariant (`inv_deliver_acceptReply'`): the no-op branches
(`PrepReplyProof.inv_deliver_same`), the counting branch (`LbCountProof.inv_deliver_lbc`), and the
commit (`RecCommitNewProof.inv_commit_new`). The commit's value is the instance's, equal to the
bookkeeping's (`lbValEq`), and it is decided already or slow-chosen at the Accept's ballot:
each counted reply is its acceptor's vote for it, or the value is decided, or (G3, `InvPM.arOk`)
a majority without that acceptor promised above the ballot and sent no reply at it — impossible
next to the leader and the other counted acceptor (`ar_chosen`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.RecCommitNew
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.LbCount

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace AcceptReplyProof

open HStepProof HLocal SafeProof AuxProof PrepReplyProof RecCommitProof RecAcceptProof
  RecCommitNewProof LbCountProof

/-! ## The handler's branches -/

/-- The bookkeeping after counting the reply. -/
abbrev arLb (lb : LbRec) : LbRec := { lb with acceptOKs := lb.acceptOKs + 1 }

theorem ar_cases (σ : RState) (m : AcceptReply) :
    hAcceptReply σ m = (σ, []) ∨ hAcceptReply σ m = (bumpRecvBallot σ m.ballot, []) ∨
    ∃ w lb, σ.inst (arX m) = some w ∧ w.lb = some lb ∧ lb.status = stACCEPTED ∧
      stGe w.status stCOMMITTED = false ∧ lb.lastTriedBallot.slt w.bal = false ∧
      lb.lastTriedBallot = m.ballot ∧
      ((¬ (W64 (nR / 2)).slt ((arLb lb).acceptOKs + 1) ∧
        hAcceptReply σ m = ((bumpRecvBallot σ m.ballot).setInst (arX m)
          { w with lb := some (arLb lb) }, [])) ∨
       ((W64 (nR / 2)).slt ((arLb lb).acceptOKs + 1) ∧
        hAcceptReply σ m =
          (updateCommitted ((bumpRecvBallot σ m.ballot).setInst (arX m)
            { w with status := stCOMMITTED, lb := some { arLb lb with status := stCOMMITTED } })
            (arX m).q,
           [Out.ev (.commit (arX m) w.bal (⟨w.cmds.getD [], w.seq, w.deps⟩ : Val)),
            Out.bcast (bcastCommitOf (updateCommitted ((bumpRecvBallot σ m.ballot).setInst (arX m)
              { w with status := stCOMMITTED, lb := some { arLb lb with status := stCOMMITTED } })
              (arX m).q) (arX m)
              (commitOf (updateCommitted ((bumpRecvBallot σ m.ballot).setInst (arX m)
                { w with status := stCOMMITTED, lb := some { arLb lb with status := stCOMMITTED } })
                (arX m).q) m.replica m.inst { arLb lb with status := stCOMMITTED }))]))) := by
  unfold hAcceptReply
  dsimp only
  cases hw : σ.inst ⟨toN m.replica, toN m.inst⟩ with
  | none => exact Or.inl rfl
  | some w =>
    dsimp only
    cases hlb : w.lb with
    | none => exact Or.inl rfl
    | some lb =>
      dsimp only
      by_cases c1 : lb.status ≠ stACCEPTED ∨ stGe w.status stCOMMITTED = true
      · rw [if_pos c1]; exact Or.inr (Or.inl rfl)
      rw [if_neg c1]
      have c1' : lb.status = stACCEPTED ∧ stGe w.status stCOMMITTED = false := by
        simp only [not_or, ne_eq, Decidable.not_not, Bool.not_eq_true] at c1; exact c1
      by_cases c2 : lb.lastTriedBallot.slt w.bal = true
      · rw [if_pos c2]; exact Or.inr (Or.inl rfl)
      rw [if_neg c2]
      by_cases c3 : lb.lastTriedBallot ≠ m.ballot
      · rw [if_pos c3]; exact Or.inr (Or.inl rfl)
      rw [if_neg c3]
      have c3' : lb.lastTriedBallot = m.ballot := by simpa using c3
      have c4 : lb.lastTriedBallot.slt m.ballot = false := by
        rw [slt_false, c3']; exact Int.le_refl _
      rw [if_neg (by rw [c4]; simp)]
      refine Or.inr (Or.inr ⟨w, lb, rfl, hlb, c1'.1, c1'.2, by simpa using c2, c3', ?_⟩)
      by_cases c5 : (W64 (nR / 2)).slt (lb.acceptOKs + 1 + 1) = true
      · rw [if_pos c5]; exact Or.inr ⟨c5, rfl⟩
      · rw [if_neg c5]; exact Or.inl ⟨c5, rfl⟩

/-! ## Counters -/

theorem w64_succ (o : w64) (h : o.toNat ≤ 5) : (o + 1).toNat = o.toNat + 1 := by
  rw [BitVec.toNat_add]; simp; omega

theorem w64_quorum (o : w64) (h : o.toNat ≤ 5) :
    (W64 (nR / 2)).slt (o + 1 + 1) = true ↔ 1 ≤ o.toNat := by
  have h1 : (o + 1 + 1).toNat = o.toNat + 2 := by
    rw [BitVec.toNat_add, BitVec.toNat_add]; simp; omega
  rw [BitVec.slt, BitVec.toInt_eq_toNat_of_lt, BitVec.toInt_eq_toNat_of_lt, h1]
  · simp [nR, W64]; omega
  · rw [h1]; omega
  · simp [nR, W64]

theorem nodup_len_le {Q : List Nat} (hQ : Q.Nodup) (h : ∀ a ∈ Q, a < nR) : Q.length ≤ nR := by
  have := (List.subperm_of_subset hQ (fun a ha => List.mem_range.mpr (h a ha)) :
    Q.Subperm (List.range nR)).length_le
  simpa using this

/-! ## The commit's value is decided or slow-chosen -/

theorem inv_lbI {S : Sys} (hS : Inv S) : Inv.lbInv S :=
  let ⟨_, _, _, _, _, _, _, _, _, _, h, _⟩ := hS.1; h

theorem inv_vfp {S : Sys} (hS : Inv S) : Inv.votesFollowProposals S :=
  let ⟨_, _, _, _, _, _, _, h, _⟩ := hS.1; h

theorem inv_op {S : Sys} (hS : Inv S) : Inv.oneProposal S :=
  let ⟨_, _, _, _, _, _, h, _⟩ := hS.1; h

theorem inv_wf' {S : Sys} (hS : Inv S) : Inv.wf S := hS.1.1

theorem inv_bal {S : Sys} (hS : Inv S) : Inv.ballots S :=
  let ⟨_, _, _, _, h, _⟩ := hS.1; h

/-- Two ACCEPTED votes at one ballot are for the same value. -/
theorem acc_votes_eq {S : Sys} (hS : Inv S) {r r' : Nat} {x : InstId} {b : w32} {v v' : Val}
    (h : S.ev r (.vote x b stACCEPTED v)) (h' : S.ev r' (.vote x b stACCEPTED v')) : v = v' := by
  obtain ⟨l, hl⟩ := (inv_vfp hS).2 _ _ _ _ h
  obtain ⟨l', hl'⟩ := (inv_vfp hS).2 _ _ _ _ h'
  exact (inv_op hS).2.1 _ _ _ _ _ _ hl hl'

/-- A nodup list of replicas avoiding three distinct replicas has at most two members. -/
theorem three_out {M : List Nat} (hM : M.Nodup) (hlt : ∀ q ∈ M, q < nR) {a b c : Nat}
    (ha : a < nR) (hb : b < nR) (hc : c < nR) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hna : a ∉ M) (hnb : b ∉ M) (hnc : c ∉ M) (hl : nR / 2 + 1 ≤ M.length) : False := by
  obtain ⟨q, hq, hq'⟩ := meet (U := List.range nR) hM (Q' := [a, b, c])
    (List.nodup_cons.mpr ⟨by simp [hab, hac], List.nodup_cons.mpr ⟨by simp [hbc],
      List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩⟩⟩)
    (fun q h => List.mem_range.mpr (hlt q h))
    (fun q h => by
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> exact List.mem_range.mpr ‹_›)
    (by simp [nR] at hl ⊢; omega)
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hq'
  rcases hq' with rfl | rfl | rfl
  · exact hna hq
  · exact hnb hq
  · exact hnc hq

/-- **The commit of `handleAcceptReply`**: the record is ACCEPTED with the bookkeeping's value,
the bookkeeping is out of the prepare phase, and the value is decided or slow-chosen at the
bookkeeping's ballot (two counted acceptors and the leader). -/
theorem ar_chosen (S : Sys) (hS : Inv S) (i : Nat) (hi : i < nR) (x : InstId) (w : InstRec)
    (lb : LbRec) (hw : (S.rep i).inst x = some w) (hlb : w.lb = some lb)
    (hst : lb.status = stACCEPTED) (hnc : stGe w.status stCOMMITTED = false)
    (hbal : w.bal = lb.lastTriedBallot) (hacc : ∃ v, S.ev i (.accept x lb.lastTriedBallot v))
    (a1 a2 : Nat) (m1 m2 : AcceptReply) (h12 : a1 ≠ a2) (ha1 : a1 ≠ i) (ha2 : a2 ≠ i)
    (ha1n : a1 < nR) (ha2n : a2 < nR)
    (hm1 : Msg.acceptReply m1 ∈ S.msgs a1 i) (hx1 : arX m1 = x) (hb1 : m1.ballot = lb.lastTriedBallot)
    (hm2 : Msg.acceptReply m2 ∈ S.msgs a2 i) (hx2 : arX m2 = x) (hb2 : m2.ballot = lb.lastTriedBallot) :
    w.status = stACCEPTED ∧ lb.preparing = false ∧ lbVal lb = instVal w ∧
      (S.committedVal x (instVal w) ∨ S.slowChosen x lb.lastTriedBallot (instVal w)) := by
  have hA := hS.2
  obtain ⟨u, hu⟩ := hacc
  -- out of the prepare phase
  have hprep : lb.preparing = false := by
    cases h : lb.preparing
    · rfl
    · exact absurd hu ((hA.prepNoProp i hi x w lb hw hlb h).2.2.1 u)
  -- the record is ACCEPTED (the leader's own vote at its ballot, `accKeep`)
  have hvu := hA.pm.accVote i x _ u hu
  have hvb : zz w.vbal ≤ zz w.bal := (inv_bal hS).1 i hi x w hw
  have hwst : w.status = stACCEPTED := by
    rcases hA.accKeep i hi x w hw _ u hvu (by rw [← hbal]; exact hvb) with h | h
    · exact h
    · exact absurd h (not_comm_of hnc)
  obtain ⟨-, hvl0⟩ := (inv_lbI hS) i hi x w lb hw hlb |>.2.2.2.2.2.2.2.1 hst hwst hbal hprep
  have hvl : S.ev i (.vote x lb.lastTriedBallot stACCEPTED (lbVal lb)) := hvl0
  -- `lbValEq`
  have hle := hA.votesLe i hi x w hw _ _ _ hvu
  have hvbeq : w.vbal = lb.lastTriedBallot := zz_inj (by rw [← hbal] at hle ⊢; omega)
  have hrec := hA.recVote i hi x w hw (Or.inr hwst)
  rw [hwst, hvbeq] at hrec
  have heq : lbVal lb = instVal w := acc_votes_eq hS hvl hrec
  refine ⟨hwst, hprep, heq, ?_⟩
  rw [← heq]
  have hvacc : S.ev i (.accept x lb.lastTriedBallot (lbVal lb)) := by
    obtain ⟨l, hl⟩ := (inv_vfp hS).2 _ _ _ _ hvl
    have := (inv_op hS).2.1 _ _ _ _ _ _ hu hl
    rw [← this] at hl ⊢; exact hu
  -- each counted reply: a vote, the value decided, or a majority that excludes both
  have hcase : ∀ a m, Msg.acceptReply m ∈ S.msgs a i → arX m = x →
      m.ballot = lb.lastTriedBallot →
      S.ev a (.vote x lb.lastTriedBallot stACCEPTED (lbVal lb)) ∨ S.committedVal x (lbVal lb) ∨
      ∃ M : List Nat, M.Nodup ∧ nR / 2 + 1 ≤ M.length ∧ a ∉ M ∧ ∀ q ∈ M, q < nR ∧
        (∃ wq, (S.rep q).inst x = some wq ∧ zz lb.lastTriedBallot < zz wq.bal) ∧
        ∀ m' : AcceptReply, Msg.acceptReply m' ∈ S.msgs q i → arX m' = x →
          m'.ballot ≠ lb.lastTriedBallot := by
    intro a m hm hx hb
    have hacc' : S.ev i (.accept (arX m) m.ballot (lbVal lb)) := by rw [hx, hb]; exact hvacc
    rcases hA.pm.arOk a i m hm (lbVal lb) hacc' with h | h | ⟨w', hw', hlt⟩ | ⟨M, hM, hl, ha, hMm⟩
    · rw [hx, hb] at h; exact Or.inl h
    · rw [hx] at h; exact Or.inr (Or.inl h)
    · rw [hx] at hw'; rw [hw] at hw'; cases hw'; rw [hb, ← hbal] at hlt; exact absurd hlt (Int.lt_irrefl _)
    · refine Or.inr (Or.inr ⟨M, hM, hl, ha, fun q hq => ?_⟩)
      obtain ⟨h1, -, ⟨wq, hwq, hlt⟩, h4⟩ := hMm q hq
      rw [hx] at hwq; rw [hb] at hlt
      exact ⟨h1, ⟨wq, hwq, hlt⟩, fun m' hm' hx' => by rw [← hb]; exact h4 m' hm' (by rw [hx', hx])⟩
  have hexcl : ∀ (a : Nat) (M : List Nat), a < nR → a ≠ i → Msg.acceptReply m1 ∈ S.msgs a1 i →
      M.Nodup → nR / 2 + 1 ≤ M.length → a ∉ M → (∀ q ∈ M, q < nR ∧
        (∃ wq, (S.rep q).inst x = some wq ∧ zz lb.lastTriedBallot < zz wq.bal) ∧
        ∀ m' : AcceptReply, Msg.acceptReply m' ∈ S.msgs q i → arX m' = x →
          m'.ballot ≠ lb.lastTriedBallot) → ∀ b' m', b' ≠ a → b' ≠ i → b' < nR →
      Msg.acceptReply m' ∈ S.msgs b' i → arX m' = x → m'.ballot = lb.lastTriedBallot → False := by
    intro a M han hai _ hM hl ha hMm b' m' hba hbi hbn hm' hx' hb'
    have hiM : i ∉ M := by
      intro h; obtain ⟨-, ⟨wq, hwq, hlt⟩, -⟩ := hMm i h
      rw [hw] at hwq; cases hwq; rw [hbal] at hlt; exact Int.lt_irrefl _ hlt
    have hbM : b' ∉ M := fun h => (hMm b' h).2.2 m' hm' hx' hb'
    exact three_out hM (fun q h => (hMm q h).1) han hi hbn hai (Ne.symm hba) (Ne.symm hbi) ha hiM
      hbM hl
  rcases hcase a1 m1 hm1 hx1 hb1 with h1 | h1 | ⟨M, hM, hl, ha, hMm⟩
  · rcases hcase a2 m2 hm2 hx2 hb2 with h2 | h2 | ⟨M, hM, hl, ha, hMm⟩
    · refine Or.inr ⟨[i, a1, a2], ?_, by simp [nR], fun r hr => ?_⟩
      · simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false, List.nodup_nil, and_true, not_or]
        exact ⟨⟨Ne.symm ha1, Ne.symm ha2⟩, h12, fun h => h⟩
      · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨hi, hvl⟩
        · exact ⟨ha1n, h1⟩
        · exact ⟨ha2n, h2⟩
    · exact Or.inl h2
    · exact (hexcl a2 M ha2n ha2 hm1 hM hl ha hMm a1 m1 h12 ha1 ha1n hm1 hx1 hb1).elim
  · exact Or.inl h1
  · exact (hexcl a1 M ha1n ha1 hm1 hM hl ha hMm a2 m2 (Ne.symm h12) ha2 ha2n hm2 hx2 hb2).elim

theorem inv_own' {S : Sys} (hS : Inv S) : Inv.ballotOwner S :=
  let ⟨_, _, _, _, _, h, _⟩ := hS.1; h

theorem inv_agr {S : Sys} (hS : Inv S) : Inv.agreement S :=
  let ⟨_, _, _, _, _, _, _, _, _, _, _, h, _⟩ := hS.1; h

theorem inv_dc {S : Sys} (hS : Inv S) : Inv.decidedChosen S :=
  let ⟨_, _, _, _, _, _, _, _, _, _, _, _, h, _⟩ := hS.1; h

theorem inv_cs {S : Sys} (hS : Inv S) : Inv.chosenSafe S :=
  let ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩ := hS.1; h

theorem inv_rep' {S : Sys} (hS : Inv S) : Inv.reports S :=
  let ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := hS.1; h

/-- A proposal's ballot is not negative. -/
theorem propAt_nonneg {S : Sys} (hS : Inv S) {x : InstId} {c : w32} {cs : List WCmd}
    (h : S.propAt x c cs) : 0 ≤ zz c := by
  have hown := inv_own' hS
  have hph : ∀ q u, S.ev q (.phase1 x c u) → 0 ≤ zz c := by
    intro q u hq
    obtain ⟨p1, p2, -, hp1, -⟩ := hown.2.1 _ _ _ _ hq
    exact zz_nonneg_of_make S hown (List.mem_of_getElem? hp1)
  rcases h with ⟨q, st, u, hst, hv, -⟩ | ⟨q, u, hq, -⟩
  · rcases hst with hst | rfl
    · obtain ⟨l, v0, hl, -⟩ := (inv_vfp hS).1 _ _ _ _ _ hv hst
      exact hph _ _ hl
    · obtain ⟨l, hl⟩ := (inv_vfp hS).2 _ _ _ _ hv
      exact zz_nonneg_of_make S hown (hown.2.2.1 _ _ _ _ hl)
  · exact hph _ _ hq

/-- A slow-chosen value at a ballot of an Accept agrees with every decided value. -/
theorem agree_slow (S : Sys) (hS : Inv S) (x : InstId) (n : w32) (v : Val)
    (hc : S.slowChosen x n v) : ∀ u, S.committedVal x u → u = v := by
  have hcs := inv_cs hS
  obtain ⟨Q, hQn, hl, hQ⟩ := hc
  obtain ⟨r0, hr0⟩ : ∃ r, r ∈ Q := by
    cases Q with
    | nil => simp [nR] at hl
    | cons r _ => exact ⟨r, List.mem_cons_self⟩
  obtain ⟨l0, hacc⟩ := (inv_vfp hS).2 _ _ _ _ (hQ r0 hr0).2
  have hreal : realBal x n ∧ x.q < nR :=
    slowChosen_real S (inv_bal hS) (inv_wf' hS) (inv_own' hS) (inv_vfp hS) x n v ⟨Q, hQn, hl, hQ⟩
  intro u hu
  rcases inv_dc hS x u hu with ⟨b0, hsc⟩ | ⟨hfr, hfc⟩
  · obtain ⟨Q0, hQ0n, hl0, hQ0⟩ := hsc
    obtain ⟨r1, hr1⟩ : ∃ r, r ∈ Q0 := by
      cases Q0 with
      | nil => simp [nR] at hl0
      | cons r _ => exact ⟨r, List.mem_cons_self⟩
    obtain ⟨l1, hacc1⟩ := (inv_vfp hS).2 _ _ _ _ (hQ0 r1 hr1).2
    rcases Int.lt_trichotomy (zz b0) (zz n) with hlt | heq | hgt
    · exact ((hcs x b0 u (Or.inl ⟨Q0, hQ0n, hl0, hQ0⟩) n hlt).1 _ _ hacc).symm
    · have : b0 = n := zz_inj heq
      subst this
      exact acc_votes_eq hS (hQ0 r1 hr1).2 (hQ r0 hr0).2
    · exact (hcs x n v (Or.inl ⟨Q, hQn, hl, hQ⟩) b0 hgt).1 _ _ hacc1
  · have hfl : S.fastLive x u := ⟨hfr, Or.inr hfc⟩
    have hxq := hreal.2
    rcases hreal.1 with rfl | hge
    · exact absurd hfl (fun h => not_fastLive_of_fastBlocked S x u hxq h
        ((inv_rep' hS).2.2.2.2.2.2.2.1 _ _ _ hacc u))
    · have hlt : zz (initBal x) < zz n := by
        rw [zz_initBal x hxq]; simp [nR] at hxq hge; omega
      exact ((hcs x (initBal x) u (Or.inr ⟨rfl, hfl⟩) n hlt).1 _ _ hacc).symm

/-! ## The law -/

/-- The delivered reply's sender has no other counted reply at the ballot. -/
theorem fr_fresh (S : Sys) (hS : Inv S) (fr i n : Nat) (hn : (fr, i, n) ∉ S.delivered)
    (p : AcceptReply) (hm : (S.sent fr i)[n]? = some (.acceptReply p)) (x : InstId)
    (hx : arX p = x) (b : w32) (hb : p.ballot = b) (hna : ¬ S.lastAbove i x b)
    (m' : AcceptReply) (hd : S.deliveredMsg fr i (.acceptReply m'))
    (hx' : (Msg.acceptReply m').instOf = some x) (hb' : m'.ballot = b) : False := by
  obtain ⟨n', hn', hdl⟩ := hd
  have hp1 : Msg.isARat x b (.acceptReply p) = true := by
    simp only [Msg.isARat, decide_eq_true_eq]; exact ⟨hx, hb⟩
  have hp2 : Msg.isARat x b (.acceptReply m') = true := by
    simp only [Msg.isARat, Msg.instOf, Option.some.injEq] at hx' ⊢
    simp only [decide_eq_true_eq]; exact ⟨hx', hb'⟩
  have hc1 : 1 ≤ S.cnt fr i (Msg.isARat x b) := by
    unfold Sys.cnt
    exact List.length_pos_of_mem (List.mem_filter.mpr ⟨mem_msgs_of_sent S hm, hp1⟩)
  rcases hS.2.arOnce fr i x b hc1 with h | ⟨h1, -⟩
  · exact hna h
  · have := pos_unique (S.msgs fr i) (Msg.isARat x b) (by unfold Sys.cnt at h1; omega)
      (msgs_of_sent S hm) hp1 (msgs_of_sent S hn') hp2
    subst this; exact hn hdl

theorem deliveredMsg_new (S : Sys) (fr i n : Nat) (m : Msg) (hm : (S.sent fr i)[n]? = some m) :
    (S.deliver fr i n m).deliveredMsg fr i m :=
  ⟨n, by
    have hd : S.deliver fr i n m =
        ({ S with delivered := S.delivered ++ [(fr, i, n)] } : Sys).applyStep i
          ((hMsg (S.rep i) m).1, (hMsg (S.rep i) m).2) := rfl
    rw [hd, Sys.applyStep_sent]; exact hm, deliver_delivered S fr i n m⟩

theorem inv_msgWf {S : Sys} (hS : Inv S) : Inv.msgWf S :=
  let ⟨_, h, _⟩ := hS.1; h

/-- The facts shared by the counting and the committing branches. -/
theorem ar_common (S : Sys) (fr i n : Nat) (hS : Inv S) (hi : i < nR) (hfr : fr < nR)
    (hn : (fr, i, n) ∉ S.delivered) (p : AcceptReply)
    (hm : (S.sent fr i)[n]? = some (.acceptReply p)) (w : InstRec) (lb : LbRec)
    (hw : (S.rep i).inst (arX p) = some w) (hlb : w.lb = some lb)
    (hlt : lb.lastTriedBallot.slt w.bal = false) (hb : lb.lastTriedBallot = p.ballot) :
    fr ≠ i ∧ (∃ v, S.ev i (.accept (arX p) lb.lastTriedBallot v)) ∧ lb.preparing = false ∧
      w.bal = lb.lastTriedBallot ∧
      (∃ Q : List Nat, Q.Nodup ∧ Q.length = lb.acceptOKs.toNat ∧ fr ∉ Q ∧
        ∀ a ∈ Q, a < nR ∧ a ≠ i ∧ ∃ m : AcceptReply, S.deliveredMsg a i (.acceptReply m) ∧
          (Msg.acceptReply m).instOf = some (arX p) ∧ m.ballot = lb.lastTriedBallot) ∧
      lb.acceptOKs.toNat ≤ 5 := by
  have hpm := mem_msgs_of_sent S hm
  have hA := hS.2
  have hfi : fr ≠ i := ((inv_wf' hS).2.2.2.2.2.1 fr i (List.ne_nil_of_mem hpm)).2.2
  have hlbI := inv_lbI hS i hi _ w lb hw hlb
  obtain ⟨-, -, -, a4, -, -, ⟨Q', q1', q2', q3'⟩, -, -⟩ := hlbI
  obtain ⟨b', u, hle, hu⟩ := hA.arFrom fr i p hpm
  have hle' := a4 b' u (Or.inr hu)
  have hb' : b' = lb.lastTriedBallot := zz_inj (by rw [hb] at hle' ⊢; omega)
  rw [hb'] at hu
  have hprep : lb.preparing = false := by
    cases h : lb.preparing
    · rfl
    · exact absurd hu ((hA.prepNoProp i hi _ w lb hw hlb h).2.2.1 u)
  have hbal : w.bal = lb.lastTriedBallot := by
    have h1 := (slt_false _ _).mp hlt
    have h2 := hA.lastLeBal i hi _ w lb hw hlb
    exact zz_inj (by omega)
  have hna : ¬ S.lastAbove i (arX p) lb.lastTriedBallot := by
    rintro ⟨w2, lb2, h2, hl2, hlt2⟩
    rw [hw] at h2; cases h2; rw [hlb] at hl2; cases hl2; exact Int.lt_irrefl _ hlt2
  have hfrQ : fr ∉ Q' := by
    intro h
    obtain ⟨-, -, m', hd, hx', hb''⟩ := q3' fr h
    exact fr_fresh S hS fr i n hn p hm _ rfl _ hb.symm hna m' hd hx' hb''
  have hlen : Q'.length ≤ 5 := nodup_len_le q1' (fun a h => (q3' a h).1)
  exact ⟨hfi, ⟨u, hu⟩, hprep, hbal, ⟨Q', q1', q2', hfrQ, q3'⟩, by rw [← q2']; exact hlen⟩

theorem bump_inst (σ : RState) (b : w32) : (bumpRecvBallot σ b).inst = σ.inst := by
  unfold bumpRecvBallot; split <;> rfl

theorem bump_fields (σ : RState) (b : w32) :
    (bumpRecvBallot σ b).id = σ.id ∧ (bumpRecvBallot σ b).peerOrder = σ.peerOrder ∧
    (bumpRecvBallot σ b).crtInstance = σ.crtInstance ∧
    (bumpRecvBallot σ b).conflicts = σ.conflicts ∧
    (bumpRecvBallot σ b).execedUpTo = σ.execedUpTo ∧ (bumpRecvBallot σ b).store = σ.store := by
  unfold bumpRecvBallot; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The counting branch** (below the quorum). -/
theorem ar_count (S : Sys) (fr i n : Nat) (hS : Inv S) (hi : i < nR) (hfr : fr < nR)
    (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered) (p : AcceptReply)
    (hm : (S.sent fr i)[n]? = some (.acceptReply p)) (w : InstRec) (lb : LbRec)
    (hw : (S.rep i).inst (arX p) = some w) (hlb : w.lb = some lb) (hst : lb.status = stACCEPTED)
    (hlt : lb.lastTriedBallot.slt w.bal = false) (hb : lb.lastTriedBallot = p.ballot)
    (h : hAcceptReply (S.rep i) p = ((bumpRecvBallot (S.rep i) p.ballot).setInst (arX p)
          { w with lb := some (arLb lb) }, [])) :
    Inv (S.deliver fr i n (.acceptReply p)) := by
  obtain ⟨hfi, -, hprep, -, ⟨Q', q1', q2', hfrQ, q3'⟩, hle5⟩ :=
    ar_common S fr i n hS hi hfr hn p hm w lb hw hlb hlt hb
  obtain ⟨-, a2, -, -, -, ⟨Q, q1, q2, q3⟩, -, -, -⟩ := inv_lbI hS i hi _ w lb hw hlb
  have hnpa : ¬ isPA (arLb lb).status := by simp only [arLb, hst]; exact acc_not_pa
  refine inv_deliver_lbc S fr i n (.acceptReply p) _ (arX p) w lb (arLb lb) hS hi hidle hm h
    (by simp [RState.setInst, bump_inst])
    (by obtain ⟨e1, e2, e3, e4, e5, e6⟩ := bump_fields (S.rep i) p.ballot
        exact ⟨by simp [RState.setInst, e1], by simp [RState.setInst, e2],
          by simp [RState.setInst, e3], by simp [RState.setInst, e4],
          by simp [RState.setInst, e5], by simp [RState.setInst, e6]⟩)
    (AuxProof.bumpRB_cls _ _)
    hw hlb ⟨rfl, rfl, rfl, rfl, hprep, hprep, rfl, rfl, rfl, a2,
      Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    (fun h' => ((inv_wf' hS).2.1 i hi _ w hw).2.2.2.2.1 lb hlb h')
    (fun h' => absurd h' hnpa)
    ⟨Q, q1, q2, fun a m' hq => by
      obtain ⟨c1, c2, c3, c4, c5, -⟩ := q3 a m' hq
      exact ⟨c1, c2, Or.inl c3, c4, c5, fun h' => absurd h' hnpa⟩⟩
    ⟨Q' ++ [fr], ?_, ?_, fun a ha => ?_⟩
    (fun _ h' => absurd h' (by rw [hst]; exact acc_not_pa))
    (fun h' => absurd h' hnpa)
  · exact List.nodup_append.mpr ⟨q1', List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩,
      fun a ha b hb' hab => by simp only [List.mem_singleton] at hb'; subst hb'; subst hab; exact hfrQ ha⟩
  · simp only [List.length_append, List.length_singleton, arLb]
    rw [w64_succ _ hle5, q2']
  · rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨c1, c2, m', c3, c4, c5⟩ := q3' a ha
      exact ⟨c1, c2, m', Or.inl c3, c4, c5⟩
    · simp only [List.mem_singleton] at ha; subst ha
      exact ⟨hfr, hfi, p, Or.inr ⟨rfl, rfl⟩, rfl, hb.symm⟩

/-- **The committing branch.** -/
theorem ar_commit (S : Sys) (fr i n : Nat) (hS : Inv S) (hi : i < nR) (hfr : fr < nR)
    (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered) (p : AcceptReply)
    (hm : (S.sent fr i)[n]? = some (.acceptReply p)) (w : InstRec) (lb : LbRec)
    (hw : (S.rep i).inst (arX p) = some w) (hlb : w.lb = some lb) (hst : lb.status = stACCEPTED)
    (hnc : stGe w.status stCOMMITTED = false)
    (hlt : lb.lastTriedBallot.slt w.bal = false) (hb : lb.lastTriedBallot = p.ballot)
    (hq : (W64 (nR / 2)).slt ((arLb lb).acceptOKs + 1) = true)
    (h : hAcceptReply (S.rep i) p =
          (updateCommitted ((bumpRecvBallot (S.rep i) p.ballot).setInst (arX p)
            { w with status := stCOMMITTED, lb := some { arLb lb with status := stCOMMITTED } })
            (arX p).q,
           [Out.ev (.commit (arX p) w.bal (⟨w.cmds.getD [], w.seq, w.deps⟩ : Val)),
            Out.bcast (bcastCommitOf (updateCommitted ((bumpRecvBallot (S.rep i) p.ballot).setInst
              (arX p) { w with status := stCOMMITTED, lb := some { arLb lb with status := stCOMMITTED } }) (arX p).q) (arX p)
              (commitOf (updateCommitted ((bumpRecvBallot (S.rep i) p.ballot).setInst (arX p)
                { w with status := stCOMMITTED, lb := some { arLb lb with status := stCOMMITTED } })
                (arX p).q) p.replica p.inst { arLb lb with status := stCOMMITTED }))])) :
    Inv (S.deliver fr i n (.acceptReply p)) := by
  have hpm := mem_msgs_of_sent S hm
  have hA := hS.2
  obtain ⟨hfi, hacc, hprep, hbal, ⟨Q', q1', q2', hfrQ, q3'⟩, hle5⟩ :=
    ar_common S fr i n hS hi hfr hn p hm w lb hw hlb hlt hb
  obtain ⟨-, a2, a3, -, -, ⟨Q, q1, q2, q3⟩, -, -, -⟩ := inv_lbI hS i hi _ w lb hw hlb
  -- a second counted acceptor
  have hq' : 1 ≤ lb.acceptOKs.toNat := (w64_quorum _ hle5).mp hq
  obtain ⟨a1, ha1⟩ : ∃ a, a ∈ Q' := by
    cases Q' with
    | nil => simp at q2'; omega
    | cons a _ => exact ⟨a, List.mem_cons_self⟩
  obtain ⟨a1n, a1i, m1, ⟨n1, hn1, -⟩, hx1, hb1⟩ := q3' a1 ha1
  have ha1fr : a1 ≠ fr := fun h' => hfrQ (h' ▸ ha1)
  simp only [Msg.instOf, Option.some.injEq] at hx1
  obtain ⟨hwst, -, heq, hcho⟩ := ar_chosen S hS i hi (arX p) w lb hw hlb hst hnc hbal hacc a1 fr
    m1 p ha1fr a1i hfi a1n hfr (mem_msgs_of_sent S hn1) hx1 hb1 hpm rfl hb.symm
  -- the record's commands and the value
  obtain ⟨c, hcw⟩ : ∃ c, w.cmds = some c := by
    cases h' : w.cmds with
    | none => exact absurd h' (hA.cmdsSome i hi _ w hw (by rw [hwst]; exact acc_ne_none))
    | some c => exact ⟨c, rfl⟩
  have hcne : c ≠ [] := hA.cmdsNe.2.1 i hi _ w c hw hcw
  generalize hv : (⟨w.cmds.getD [], w.seq, w.deps⟩ : Val) = v at h
  have hvI : instVal w = v := by rw [← hv]; rfl
  have hvc : v.cmds = c := by rw [← hv, hcw]; rfl
  rw [hvI] at heq hcho
  have hlbc : lb.cmds = some c := by
    have h1 : lb.cmds.getD [] = c := by
      have := congrArg Val.cmds heq; simp only [lbVal] at this; rw [this, hvc]
    cases h2 : lb.cmds with
    | none => rw [h2] at h1; exact absurd h1.symm hcne
    | some c' => rw [h2] at h1; simp only [Option.getD_some] at h1; rw [h1]
  -- agreement and choice
  have hagr : ∀ u, S.committedVal (arX p) u → u = v := by
    rcases hcho with hc | hc
    · exact fun u hu => (inv_agr hS).1 _ _ _ hu hc
    · exact agree_slow S hS _ _ v hc
  have haccv : ∃ l, S.ev l (.accept (arX p) lb.lastTriedBallot v) := by
    obtain ⟨-, hvl⟩ := (inv_lbI hS) i hi _ w lb hw hlb |>.2.2.2.2.2.2.2.1 hst hwst hbal hprep
    have hvl' : S.ev i (.vote (arX p) lb.lastTriedBallot stACCEPTED (lbVal lb)) := hvl
    rw [heq] at hvl'
    exact (inv_vfp hS).2 _ _ _ _ hvl'
  obtain ⟨l0, hacc0⟩ := haccv
  have hownv : S.ev i (.vote (arX p) lb.lastTriedBallot stACCEPTED v) := by
    obtain ⟨-, hvl⟩ := (inv_lbI hS) i hi _ w lb hw hlb |>.2.2.2.2.2.2.2.1 hst hwst hbal hprep
    have hvl' : S.ev i (.vote (arX p) lb.lastTriedBallot stACCEPTED (lbVal lb)) := hvl
    rw [heq] at hvl'; exact hvl'
  -- the step
  generalize hL : ({ arLb lb with status := stCOMMITTED } : LbRec) = lb' at h
  generalize hσ1 : updateCommitted ((bumpRecvBallot (S.rep i) p.ballot).setInst (arX p)
    { w with status := stCOMMITTED, lb := some lb' }) (arX p).q = σ1 at h
  generalize hmc : commitOf σ1 p.replica p.inst lb' = mc at h
  generalize hB : bcastCommitOf σ1 (arX p) mc = B at h
  have hH := hs_deliver S fr i n (.acceptReply p) hidle hm
  have hout : hMsg (S.rep i) (.acceptReply p) = (σ1, [Out.ev (.commit (arX p) w.bal v),
      Out.bcast B]) := by simp only [hMsg]; exact h
  rw [hout] at hH
  have hH' : HS S (S.deliver fr i n (.acceptReply p)) i σ1
      (.commit (arX p) w.bal v :: (if false then [.fastCommit (arX p) v] else []))
      (fun _ => []) B.norm := by
    have e1 : evsOf [Out.ev (.commit (arX p) w.bal v), Out.bcast B] =
        .commit (arX p) w.bal v :: (if false then [.fastCommit (arX p) v] else []) := rfl
    have e2 : sendsOf [Out.ev (.commit (arX p) w.bal v), Out.bcast B] = fun _ => [] := by
      funext to; rfl
    have e3 : pendFold [Out.ev (.commit (arX p) w.bal v), Out.bcast B] none = B.norm := rfl
    rw [e1, e2, e3] at hH; exact hH
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := bump_fields (S.rep i) p.ballot
  have hσf : σ1.id = (S.rep i).id ∧ σ1.peerOrder = (S.rep i).peerOrder ∧
      σ1.crtInstance = (S.rep i).crtInstance ∧ σ1.conflicts = (S.rep i).conflicts ∧
      σ1.execedUpTo = (S.rep i).execedUpTo ∧ σ1.store = (S.rep i).store := by
    rw [← hσ1]
    exact ⟨by simp [updateCommitted, RState.setInst, e1], by simp [updateCommitted, RState.setInst, e2],
      by simp [updateCommitted, RState.setInst, e3], by simp [updateCommitted, RState.setInst, e4],
      by simp [updateCommitted, RState.setInst, e5], by simp [updateCommitted, RState.setInst, e6]⟩
  obtain ⟨r1, r2, r3, r4⟩ := (inv_msgWf hS fr i _ hpm).1 p.replica p.inst rfl
  have hwb := (inv_bal hS).1 i hi _ w hw
  have hvb0 := hA.vbalNonneg i hi _ w hw (by rw [hwst]; exact acc_ne_none)
  have hlbP := hA.pm.lbProp i hi _ w lb hw hlb hst hacc
  rw [hlbc] at hlbP; simp only [Option.getD_some] at hlbP; rw [← hvc] at hlbP
  have hdepsW : depsOk w.deps := ((inv_wf' hS).2.1 i hi _ w hw).2.2.2.1 (by rw [hwst]; exact acc_ne_none)
  have hdepsL : depsOk lb.deps :=
    ((inv_wf' hS).2.1 i hi _ w hw).2.2.2.2.1 lb hlb (by rw [hst]; exact acc_ne_none)
  have hvd : v.deps = w.deps := by rw [← hv]
  refine inv_commit_new S _ i σ1 (arX p) w lb lb' w.bal v false B mc hS hi hidle hH'
    (ExecOrd.deliver_chan_nil S fr i n _ (fun c h => by cases h))
    ⟨by rw [← hB]; rfl, by rw [← hB]; rfl,
      by rw [← hB]; simp only [bcastCommitOf]; rw [hσf.2.1], by rw [← hB]; rfl,
      by rw [← hB]; rfl, by rw [← hB]; rfl⟩
    ⟨by rw [← hmc]; rfl, by rw [← hmc]; exact r1, by rw [← hmc]; exact r2, by rw [← hmc]; exact r3,
      by rw [← hmc]; exact r4,
      by rw [← hmc, ← hL]; simp only [commitOf, arLb]; exact heq,
      by rw [← hmc, ← hL]; simp only [commitOf, arLb]; exact propAt_nonneg hS hlbP⟩
    ?_ hσf (by rw [← hσ1]; exact AuxProof.bumpRB_cls _ _) hw hlb (not_comm_of hnc) (Int.le_refl _) (by rw [hbal]; exact Int.le_refl _)
    hwb hvb0 hagr ?_ ?_ ?_ (by rw [hvd]; exact hdepsW) (by rw [hvc]; exact hcne)
    (fun _ => Or.inl ⟨i, stACCEPTED, v, Or.inr rfl, by rw [hbal]; exact hownv, rfl⟩)
    (by rw [← hmc, ← hL]; simp only [commitOf, arLb]; exact hlbP)
    (fun h' => by cases h')
    ⟨by rw [← hL], by rw [← hL]; exact a2, by rw [← hL], by rw [← hL]; exact hprep,
      by rw [← hL]; exact a3, by rw [← hL], by rw [← hL], by rw [← hL]; exact hdepsL,
      by rw [← hL]; simp only [arLb]; rw [hlbc, hvc]⟩ ?_
  · -- the record
    rw [← hσ1]
    simp only [updateCommitted, RState.setInst, bump_inst]
    congr 1; congr 1
    simp only [comNew]
    rw [← hv]; simp only [hcw, Option.getD_some]
  · -- choice
    rcases hcho with hc | hc
    · exact Or.inl hc
    · exact Or.inr (Or.inl ⟨_, hc⟩)
  · -- witnesses
    rcases hcho with hc | hc
    · exact Or.inl hc
    by_cases hno : v.cmds = noop
    · exact Or.inr (Or.inl hno)
    rcases hA.pm.accWit _ _ _ _ hacc0 hno with hw' | ⟨u, hu⟩
    · exact Or.inr (Or.inr hw')
    · exact Or.inl (hagr u hu ▸ hu)
  · -- slots
    exact hA.valOk _ _ _ _ (Or.inr hacc0)
  · -- the counted replies
    have hdn := deliveredMsg_new S fr i n (.acceptReply p) hm
    refine ⟨⟨Q, q1, by rw [← hL]; exact q2, fun a m' hq' => ?_⟩, ⟨Q' ++ [fr], ?_, ?_, fun a ha => ?_⟩⟩
    · obtain ⟨c1, c2, c3, c4, c5, -⟩ := q3 a m' hq'
      exact ⟨c1, c2, hH'.deliveredMsg_old c3, c4, by rw [← hL]; exact c5⟩
    · exact List.nodup_append.mpr ⟨q1', List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩,
        fun a ha b hb' hab => by simp only [List.mem_singleton] at hb'; subst hb'; subst hab; exact hfrQ ha⟩
    · rw [← hL]; simp only [List.length_append, List.length_singleton, arLb]
      rw [w64_succ _ hle5, q2']
    · rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨c1, c2, m', c3, c4, c5⟩ := q3' a ha
        exact ⟨c1, c2, m', hH'.deliveredMsg_old c3, c4, by rw [← hL]; exact c5⟩
      · simp only [List.mem_singleton] at ha; subst ha
        exact ⟨hfr, hfi, p, hdn, rfl, by rw [← hL]; exact hb.symm⟩

/-- **`handleAcceptReply` keeps the invariant.** -/
theorem inv_deliver_acceptReply' (S : Sys) (fr i n : Nat) (hS : Inv S) (hi : i < nR)
    (hfr : fr < nR) (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered) (p : AcceptReply)
    (hm : (S.sent fr i)[n]? = some (.acceptReply p)) :
    Inv (S.deliver fr i n (.acceptReply p)) := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := bump_fields (S.rep i) p.ballot
  rcases ar_cases (S.rep i) p with h | h | ⟨w, lb, hw, hlb, hst, hnc, hlt, hb, ⟨hq, h⟩ | ⟨hq, h⟩⟩
  · exact inv_deliver_same S fr i n _ _ hS hm h ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl ⟨rfl, rfl⟩
  · exact inv_deliver_same S fr i n _ _ hS hm h ⟨e1, bump_inst _ _, e3, e4, e5, e6⟩ e2
      (AuxProof.bumpRB_cls _ _)
  · exact ar_count S fr i n hS hi hfr hidle hn p hm w lb hw hlb hst hlt hb h
  · exact ar_commit S fr i n hS hi hfr hidle hn p hm w lb hw hlb hst hnc hlt hb (by simpa using hq) h

end AcceptReplyProof


end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
