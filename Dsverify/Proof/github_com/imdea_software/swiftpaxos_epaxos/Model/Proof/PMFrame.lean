/-
`InvPM` (the reply handlers' conjuncts, sixth agent) under steps that create nothing it reads:
one frame lemma per field (`*_frame`, with the field's own hypotheses, for the steps that create
some of what `InvPM` reads and prove the other fields by frame), and `pm_frame` for the steps
that create nothing it reads (events only grow, new events are sends of non-`PrepareReply`
messages, messages only shrink, `sent` only grows, `bal`s only grow, the bookkeepings keep what
`InvPM` reads; `paSent` given by the caller, `ps_frame` for its common case).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.CmdSafe

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace PMProof

/-- The bookkeeping fields `InvPM` reads (except `preAcceptsSent`, `paSent`'s alone). -/
def LbPM (lb lb' : LbRec) : Prop :=
  lb'.lastTriedBallot = lb.lastTriedBallot ∧ lb'.status = lb.status ∧ lb'.ballot = lb.ballot ∧
    lb'.cmds = lb.cmds ∧ lb'.preAcceptOKs = lb.preAcceptOKs ∧ lb'.allEqual = lb.allEqual

theorem LbPM.refl (lb : LbRec) : LbPM lb lb := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem filter_sub {l : List Nat} {p q : Nat → Bool} (h : ∀ a, p a = true → q a = true) :
    (l.filter p).Sublist (l.filter q) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases hp : p a = true
    · simp only [List.filter_cons, hp, h a hp, if_true]; exact ih.cons_cons a
    · by_cases hq : q a = true
      · simp only [List.filter_cons, hp, hq, if_true, Bool.false_eq_true, if_false]; exact ih.cons a
      · simp only [List.filter_cons, hp, hq, Bool.false_eq_true, if_false]; exact ih

section
variable {S S' : Sys}

theorem propAt_mono (hmono : ∀ r e, S.ev r e → S'.ev r e) {x : InstId} {c : w32}
    {cs : List WCmd} (h : S.propAt x c cs) : S'.propAt x c cs := by
  rcases h with ⟨q, st, u, h0, h1, h2⟩ | ⟨q, u, h1, h2⟩
  · exact Or.inl ⟨q, st, u, h0, hmono _ _ h1, h2⟩
  · exact Or.inr ⟨q, u, hmono _ _ h1, h2⟩

theorem witnessed_mono (hmono : ∀ r e, S.ev r e → S'.ev r e) {x : InstId} {v : Val}
    (h : S.witnessed x v) : S'.witnessed x v := by
  obtain ⟨W, h1, h2, h3⟩ := h
  exact ⟨W, h1, h2, fun r hr => ⟨(h3 r hr).1, by
    obtain ⟨d, d1, d2⟩ := (h3 r hr).2; exact ⟨d, hmono _ _ d1, d2⟩⟩⟩

theorem arOk_frame (hP : InvPM S)
    (hmsg : ∀ a r m, Msg.acceptReply m ∈ S'.msgs a r → Msg.acceptReply m ∈ S.msgs a r)
    (hacc : ∀ r y b v, S'.ev r (.accept y b v) → S.ev r (.accept y b v))
    (hvote : ∀ q y b v, S'.ev q (.vote y b stACCEPTED v) → S.ev q (.vote y b stACCEPTED v) ∨
      ∀ w, (S.rep q).inst y = some w → zz w.bal ≤ zz b)
    (hmono : ∀ r e, S.ev r e → S'.ev r e)
    (hcv : ∀ y u, S.committedVal y u → S'.committedVal y u)
    (hbal : ∀ r y w, (S.rep r).inst y = some w →
      ∃ w', (S'.rep r).inst y = some w' ∧ zz w.bal ≤ zz w'.bal) :
    ∀ a r (m : AcceptReply), Msg.acceptReply m ∈ S'.msgs a r → ∀ v,
      S'.ev r (.accept (arX m) m.ballot v) →
      S'.ev a (.vote (arX m) m.ballot stACCEPTED v) ∨ S'.committedVal (arX m) v ∨
      (∃ w, (S'.rep r).inst (arX m) = some w ∧ zz m.ballot < zz w.bal) ∨
      ∃ M : List Nat, M.Nodup ∧ nR / 2 + 1 ≤ M.length ∧ a ∉ M ∧ ∀ q ∈ M, q < nR ∧
        ¬ S'.ev q (.vote (arX m) m.ballot stACCEPTED v) ∧
        (∃ wq, (S'.rep q).inst (arX m) = some wq ∧ zz m.ballot < zz wq.bal) ∧
        ∀ m' : AcceptReply, Msg.acceptReply m' ∈ S'.msgs q r → arX m' = arX m →
          m'.ballot ≠ m.ballot := by
  intro a r m hm v hv
  rcases hP.arOk a r m (hmsg _ _ _ hm) v (hacc _ _ _ _ hv) with h | h | ⟨w, hw, hlt⟩ |
    ⟨M, hM, hl, ha, hMm⟩
  · exact Or.inl (hmono _ _ h)
  · exact Or.inr (Or.inl (hcv _ _ h))
  · obtain ⟨w', hw', hle⟩ := hbal r _ w hw
    exact Or.inr (Or.inr (Or.inl ⟨w', hw', Int.lt_of_lt_of_le hlt hle⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨M, hM, hl, ha, fun q hq => ?_⟩))
    obtain ⟨h1, h2, ⟨wq, hwq, hlt⟩, h4⟩ := hMm q hq
    obtain ⟨wq', hwq', hle⟩ := hbal q _ wq hwq
    refine ⟨h1, fun hv' => ?_, ⟨wq', hwq', Int.lt_of_lt_of_le hlt hle⟩,
      fun m' hm' hx => h4 m' (hmsg _ _ _ hm') hx⟩
    rcases hvote _ _ _ _ hv' with h | h
    · exact h2 h
    · have := h wq hwq; omega

/-- `arOk_frame` when only the Accepts an old `AcceptReply` answers are known to be old. -/
theorem arOk_frame2 (hP : InvPM S)
    (hmsg : ∀ a r m, Msg.acceptReply m ∈ S'.msgs a r → Msg.acceptReply m ∈ S.msgs a r)
    (hacc : ∀ a r m, Msg.acceptReply m ∈ S.msgs a r → ∀ v,
      S'.ev r (.accept (arX m) m.ballot v) → S.ev r (.accept (arX m) m.ballot v))
    (hvote : ∀ q y b v, S'.ev q (.vote y b stACCEPTED v) → S.ev q (.vote y b stACCEPTED v) ∨
      ∀ w, (S.rep q).inst y = some w → zz w.bal ≤ zz b)
    (hmono : ∀ r e, S.ev r e → S'.ev r e)
    (hcv : ∀ y u, S.committedVal y u → S'.committedVal y u)
    (hbal : ∀ r y w, (S.rep r).inst y = some w →
      ∃ w', (S'.rep r).inst y = some w' ∧ zz w.bal ≤ zz w'.bal) :
    ∀ a r (m : AcceptReply), Msg.acceptReply m ∈ S'.msgs a r → ∀ v,
      S'.ev r (.accept (arX m) m.ballot v) →
      S'.ev a (.vote (arX m) m.ballot stACCEPTED v) ∨ S'.committedVal (arX m) v ∨
      (∃ w, (S'.rep r).inst (arX m) = some w ∧ zz m.ballot < zz w.bal) ∨
      ∃ M : List Nat, M.Nodup ∧ nR / 2 + 1 ≤ M.length ∧ a ∉ M ∧ ∀ q ∈ M, q < nR ∧
        ¬ S'.ev q (.vote (arX m) m.ballot stACCEPTED v) ∧
        (∃ wq, (S'.rep q).inst (arX m) = some wq ∧ zz m.ballot < zz wq.bal) ∧
        ∀ m' : AcceptReply, Msg.acceptReply m' ∈ S'.msgs q r → arX m' = arX m →
          m'.ballot ≠ m.ballot := by
  intro a r m hm v hv
  have hm0 := hmsg _ _ _ hm
  rcases hP.arOk a r m hm0 v (hacc _ _ _ hm0 _ hv) with h | h | ⟨w, hw, hlt⟩ |
    ⟨M, hM, hl, ha, hMm⟩
  · exact Or.inl (hmono _ _ h)
  · exact Or.inr (Or.inl (hcv _ _ h))
  · obtain ⟨w', hw', hle⟩ := hbal r _ w hw
    exact Or.inr (Or.inr (Or.inl ⟨w', hw', Int.lt_of_lt_of_le hlt hle⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨M, hM, hl, ha, fun q hq => ?_⟩))
    obtain ⟨h1, h2, ⟨wq, hwq, hlt⟩, h4⟩ := hMm q hq
    obtain ⟨wq', hwq', hle⟩ := hbal q _ wq hwq
    refine ⟨h1, fun hv' => ?_, ⟨wq', hwq', Int.lt_of_lt_of_le hlt hle⟩,
      fun m' hm' hx => h4 m' (hmsg _ _ _ hm') hx⟩
    rcases hvote _ _ _ _ hv' with h | h
    · exact h2 h
    · have := h wq hwq; omega

theorem commitProp_frame (hP : InvPM S)
    (hcm : ∀ r y c u, S'.ev r (.commit y c u) → S.ev r (.commit y c u))
    (hmono : ∀ r e, S.ev r e → S'.ev r e) :
    ∀ r x c u, S'.ev r (.commit x c u) → zz c ≤ zz (initBal x) → S'.propAt x c u.cmds :=
  fun r x c u h hle => propAt_mono hmono (hP.commitProp r x c u (hcm _ _ _ _ h) hle)

theorem commitMsgProp_frame (hP : InvPM S)
    (hmsg : ∀ fr to m, Msg.commit m ∈ S'.msgs fr to → Msg.commit m ∈ S.msgs fr to)
    (hmono : ∀ r e, S.ev r e → S'.ev r e) :
    ∀ fr to (m : Commit), Msg.commit m ∈ S'.msgs fr to →
      S'.propAt ⟨toN m.replica, toN m.inst⟩ m.ballot m.command :=
  fun fr to m h => propAt_mono hmono (hP.commitMsgProp fr to m (hmsg _ _ _ h))

theorem lbProp_frame (hP : InvPM S)
    (hlb : ∀ r x w' lb', (S'.rep r).inst x = some w' → w'.lb = some lb' →
      ∃ w lb, (S.rep r).inst x = some w ∧ w.lb = some lb ∧ LbPM lb lb')
    (hacc : ∀ r y b v, S'.ev r (.accept y b v) → S.ev r (.accept y b v))
    (hmono : ∀ r e, S.ev r e → S'.ev r e) :
    ∀ r < nR, ∀ x w lb, (S'.rep r).inst x = some w → w.lb = some lb →
      lb.status = stACCEPTED → (∃ v, S'.ev r (.accept x lb.lastTriedBallot v)) →
      S'.propAt x lb.ballot (lb.cmds.getD []) := by
  intro r hr x w' lb' hw' hlb' hs ⟨v, hv⟩
  obtain ⟨w, lb, hw, hlb, e1, e2, e3, e4, -, -⟩ := hlb r x w' lb' hw' hlb'
  rw [e3, e4]
  exact propAt_mono hmono (hP.lbProp r hr x w lb hw hlb (by rw [← e2]; exact hs)
    ⟨v, by rw [← e1]; exact hacc _ _ _ _ hv⟩)

theorem parCom_frame (hP : InvPM S)
    (hmsg : ∀ a r m, Msg.preAcceptReply m ∈ S'.msgs a r → Msg.preAcceptReply m ∈ S.msgs a r)
    (hmono : ∀ r e, S.ev r e → S'.ev r e) :
    ∀ a r (m : PreAcceptReply), Msg.preAcceptReply m ∈ S'.msgs a r →
      isCommitted m.status → ∃ c u, S'.ev a (.commit (parX m) c u) ∧ zz c ≤ zz m.ballot ∧
        u.seq = m.seq ∧ u.deps = m.deps := by
  intro a r m hm hc
  obtain ⟨c, u, h1, h2, h3, h4⟩ := hP.parCom a r m (hmsg _ _ _ hm) hc
  exact ⟨c, u, hmono _ _ h1, h2, h3, h4⟩

theorem parSt_frame (hP : InvPM S)
    (hmsg : ∀ a r m, Msg.preAcceptReply m ∈ S'.msgs a r → Msg.preAcceptReply m ∈ S.msgs a r)
    (hsent : ∀ fr to m, m ∈ S.sent fr to → m ∈ S'.sent fr to) :
    ∀ a r (m : PreAcceptReply), Msg.preAcceptReply m ∈ S'.msgs a r →
      (isPA m.status ∨ m.status = stACCEPTED ∨ isCommitted m.status) ∧ 0 ≤ zz m.vballot ∧
      zz m.vballot ≤ zz m.ballot ∧ ∃ p : PreAccept, Msg.preAccept p ∈ S'.sent r a ∧
        (⟨toN p.replica, toN p.inst⟩ : InstId) = parX m ∧ p.ballot = m.ballot := by
  intro a r m hm
  obtain ⟨h1, h2, h3, p, h4, h5, h6⟩ := hP.parSt a r m (hmsg _ _ _ hm)
  exact ⟨h1, h2, h3, p, hsent _ _ _ h4, h5, h6⟩

theorem paFresh_frame (hP : InvPM S)
    (hlb : ∀ r x w' lb', (S'.rep r).inst x = some w' → w'.lb = some lb' →
      ∃ w lb, (S.rep r).inst x = some w ∧ w.lb = some lb ∧ LbPM lb lb')
    (hph : ∀ r y b v, S'.ev r (.phase1 y b v) → S.ev r (.phase1 y b v)) :
    ∀ r < nR, ∀ x w lb, (S'.rep r).inst x = some w → w.lb = some lb → isPA lb.status →
      lb.preAcceptOKs = W64 0 → (∃ v, S'.ev r (.phase1 x lb.lastTriedBallot v)) →
      zz lb.ballot = -1 := by
  intro r hr x w' lb' hw' hlb' hs h0 ⟨v, hv⟩
  obtain ⟨w, lb, hw, hlb, e1, e2, e3, -, e5, -⟩ := hlb r x w' lb' hw' hlb'
  rw [e3]
  exact hP.paFresh r hr x w lb hw hlb (by rw [← e2]; exact hs) (by rw [← e5]; exact h0)
    ⟨v, by rw [← e1]; exact hph _ _ _ _ hv⟩

theorem paCmds_frame (hP : InvPM S)
    (hlb : ∀ r x w' lb', (S'.rep r).inst x = some w' → w'.lb = some lb' →
      ∃ w lb, (S.rep r).inst x = some w ∧ w.lb = some lb ∧ LbPM lb lb')
    (hph : ∀ r y b v, S'.ev r (.phase1 y b v) → S.ev r (.phase1 y b v)) :
    ∀ r < nR, ∀ x w lb, (S'.rep r).inst x = some w → w.lb = some lb → isPA lb.status →
      ∀ v, S'.ev r (.phase1 x lb.lastTriedBallot v) → lb.cmds = some v.cmds := by
  intro r hr x w' lb' hw' hlb' hs v hv
  obtain ⟨w, lb, hw, hlb, e1, e2, -, e4, -, -⟩ := hlb r x w' lb' hw' hlb'
  rw [e4]
  exact hP.paCmds r hr x w lb hw hlb (by rw [← e2]; exact hs) v (by rw [← e1]; exact hph _ _ _ _ hv)

theorem paVoteMsg_frame (hP : InvPM S)
    (hvote : ∀ r y b st v, S'.ev r (.vote y b st v) → S.ev r (.vote y b st v))
    (hsent : ∀ fr to m, m ∈ S.sent fr to → m ∈ S'.sent fr to) :
    ∀ r x st v, isPA st → r ≠ x.q → S'.ev r (.vote x (initBal x) st v) →
      ∃ p : PreAccept, Msg.preAccept p ∈ S'.sent x.q r ∧
        (⟨toN p.replica, toN p.inst⟩ : InstId) = x ∧ p.ballot = initBal x := by
  intro r x st v hst hne hv
  obtain ⟨p, h1, h2, h3⟩ := hP.paVoteMsg r x st v hst hne (hvote _ _ _ _ _ hv)
  exact ⟨p, hsent _ _ _ h1, h2, h3⟩

theorem parNoPA_frame (hP : InvPM S)
    (hmsg : ∀ a r m, Msg.preAcceptReply m ∈ S'.msgs a r → Msg.preAcceptReply m ∈ S.msgs a r)
    (hvote : ∀ r y b st v, S'.ev r (.vote y b st v) → S.ev r (.vote y b st v)) :
    ∀ a r (m : PreAcceptReply), Msg.preAcceptReply m ∈ S'.msgs a r → ¬ isPA m.status →
      ∀ st u, isPA st → ¬ S'.ev a (.vote (parX m) m.ballot st u) :=
  fun a r m hm hn st u hst hv =>
    hP.parNoPA a r m (hmsg _ _ _ hm) hn st u hst (hvote _ _ _ _ _ hv)

theorem aeF_frame (hP : InvPM S)
    (hlb : ∀ r x w' lb', (S'.rep r).inst x = some w' → w'.lb = some lb' →
      ∃ w lb, (S.rep r).inst x = some w ∧ w.lb = some lb ∧ LbPM lb lb')
    (hsent : ∀ fr to m, m ∈ S.sent fr to → m ∈ S'.sent fr to) :
    ∀ r < nR, ∀ x w lb, (S'.rep r).inst x = some w → w.lb = some lb → isPA lb.status →
      lb.allEqual = false → ∃ (a a' : Nat) (m m' : PreAcceptReply),
        Msg.preAcceptReply m ∈ S'.sent a r ∧ Msg.preAcceptReply m' ∈ S'.sent a' r ∧
        parX m = x ∧ parX m' = x ∧ m.ballot = lb.lastTriedBallot ∧
        m'.ballot = lb.lastTriedBallot ∧ (m.seq ≠ m'.seq ∨ m.deps ≠ m'.deps) := by
  intro r hr x w' lb' hw' hlb' hs hae
  obtain ⟨w, lb, hw, hlb, e1, e2, -, -, -, e6⟩ := hlb r x w' lb' hw' hlb'
  obtain ⟨a, a', m, m', h1, h2, h3, h4, h5, h6, h7⟩ :=
    hP.aeF r hr x w lb hw hlb (by rw [← e2]; exact hs) (by rw [← e6]; exact hae)
  exact ⟨a, a', m, m', hsent _ _ _ h1, hsent _ _ _ h2, h3, h4, by rw [e1]; exact h5,
    by rw [e1]; exact h6, h7⟩

theorem repLead_frame (hP : InvPM S)
    (hprep : ∀ r m e, S'.prepReport r m e → S.prepReport r m e)
    (hbal : ∀ r y w, (S.rep r).inst y = some w →
      ∃ w', (S'.rep r).inst y = some w' ∧ zz w.bal ≤ zz w'.bal) :
    ∀ r m e, S'.prepReport r m e → r = toN m.replica →
      ∃ w, (S'.rep r).inst ⟨toN m.replica, toN m.inst⟩ = some w ∧
        zz (initBal ⟨toN m.replica, toN m.inst⟩) < zz w.bal := by
  intro r m e hp hr
  obtain ⟨w, hw, hlt⟩ := hP.repLead r m e (hprep _ _ _ hp) hr
  obtain ⟨w', hw', hle⟩ := hbal r _ w hw
  exact ⟨w', hw', Int.lt_of_lt_of_le hlt hle⟩

theorem paGe_frame (hP : InvPM S)
    (hvote : ∀ r y b st v, S'.ev r (.vote y b st v) → S.ev r (.vote y b st v))
    (hph : ∀ r y b v, S'.ev r (.phase1 y b v) → S.ev r (.phase1 y b v)) :
    ∀ r x b st v ℓ v0, isPA st → S'.ev r (.vote x b st v) → S'.ev ℓ (.phase1 x b v0) →
      depsLe v0.deps v.deps :=
  fun r x b st v ℓ v0 hst h1 h2 => hP.paGe r x b st v ℓ v0 hst (hvote _ _ _ _ _ h1) (hph _ _ _ _ h2)

theorem phAttrs_frame (hP : InvPM S)
    (hph : ∀ r y b v, S'.ev r (.phase1 y b v) → S.ev r (.phase1 y b v))
    (hmono : ∀ r e, S.ev r e → S'.ev r e) :
    ∀ ℓ x b v0, S'.ev ℓ (.phase1 x b v0) → S'.ev ℓ (.attrsRec x v0.cmds v0.deps) :=
  fun ℓ x b v0 h => hmono _ _ (hP.phAttrs ℓ x b v0 (hph _ _ _ _ h))

theorem accWit_frame (hP : InvPM S)
    (hacc : ∀ r y b v, S'.ev r (.accept y b v) → S.ev r (.accept y b v))
    (hmono : ∀ r e, S.ev r e → S'.ev r e)
    (hcv : ∀ y u, S.committedVal y u → S'.committedVal y u) :
    ∀ r x b v, S'.ev r (.accept x b v) → v.cmds ≠ noop →
      S'.witnessed x v ∨ ∃ u, S'.committedVal x u := by
  intro r x b v h hn
  rcases hP.accWit r x b v (hacc _ _ _ _ h) hn with h' | ⟨u, hu⟩
  · exact Or.inl (witnessed_mono hmono h')
  · exact Or.inr ⟨u, hcv _ _ hu⟩

theorem accVote_frame (hP : InvPM S)
    (hacc : ∀ r y b v, S'.ev r (.accept y b v) → S.ev r (.accept y b v))
    (hmono : ∀ r e, S.ev r e → S'.ev r e) :
    ∀ r x b v, S'.ev r (.accept x b v) → S'.ev r (.vote x b stACCEPTED v) :=
  fun r x b v h => hmono _ _ (hP.accVote r x b v (hacc _ _ _ _ h))

/-- `paSent` when the leaders' bookkeepings keep `lastTriedBallot` and `preAcceptsSent`, no
tracking broadcast becomes pending and the recipients handed to the wire do not grow. -/
theorem ps_frame (hP : InvPM S)
    (hlb : ∀ x w' lb', (S'.rep x.q).inst x = some w' → w'.lb = some lb' →
      ∃ w lb, (S.rep x.q).inst x = some w ∧ w.lb = some lb ∧
        lb'.lastTriedBallot = lb.lastTriedBallot ∧ lb'.preAcceptsSent = lb.preAcceptsSent)
    (hpend : ∀ r b, S'.pending r = some b → b.trackPA = true → S.pending r = some b)
    (hrc : ∀ x a, (S'.sent x.q a ++ S'.outbox x.q a).any (Msg.isPAat x (initBal x)) = true →
      (S.sent x.q a ++ S.outbox x.q a).any (Msg.isPAat x (initBal x)) = true) :
    ∀ x w lb, x.q < nR → (S'.rep x.q).inst x = some w → w.lb = some lb →
      lb.lastTriedBallot = initBal x →
      lb.preAcceptsSent.toNat ≤ 2 * fR - 1 ∧
      (∀ b, S'.pending x.q = some b → b.x = x → b.trackPA = true →
        b.m.isPAat x (initBal x) = true ∧ b.sent = lb.preAcceptsSent.toNat ∧ b.need ≤ 2 * fR - 1) ∧
      (S'.paRcpt x).length ≤ lb.preAcceptsSent.toNat := by
  intro x w' lb' hq hw' hlb' hlt
  obtain ⟨w, lb, hw, hlb, e1, e2⟩ := hlb x w' lb' hw' hlb'
  obtain ⟨h1, h2, h3⟩ := hP.paSent x w lb hq hw hlb (by rw [← e1]; exact hlt)
  refine ⟨by rw [e2]; exact h1, fun b hb hbx ht => ?_, ?_⟩
  · rw [e2]; exact h2 b (hpend _ _ hb ht) hbx ht
  · rw [e2]
    refine Nat.le_trans (List.Sublist.length_le ?_) h3
    unfold Sys.paRcpt
    exact filter_sub (fun a ha => hrc x a ha)

/-- **Frame for `InvPM`.** -/
theorem pm_frame (hP : InvPM S)
    (hmono : ∀ r e, S.ev r e → S'.ev r e)
    (hev : ∀ r e, S'.ev r e → S.ev r e ∨ ∃ to m, e = .sent to m ∧ ∀ p, m ≠ .prepareReply p)
    (hmsg : ∀ fr to m, m ∈ S'.msgs fr to → m ∈ S.msgs fr to)
    (hsent : ∀ fr to m, m ∈ S.sent fr to → m ∈ S'.sent fr to)
    (hcv : ∀ y u, S.committedVal y u → S'.committedVal y u)
    (hbal : ∀ r y w, (S.rep r).inst y = some w →
      ∃ w', (S'.rep r).inst y = some w' ∧ zz w.bal ≤ zz w'.bal)
    (hlb : ∀ r x w' lb', (S'.rep r).inst x = some w' → w'.lb = some lb' →
      ∃ w lb, (S.rep r).inst x = some w ∧ w.lb = some lb ∧ LbPM lb lb')
    (hps : ∀ x w lb, x.q < nR → (S'.rep x.q).inst x = some w → w.lb = some lb →
      lb.lastTriedBallot = initBal x →
      lb.preAcceptsSent.toNat ≤ 2 * fR - 1 ∧
      (∀ b, S'.pending x.q = some b → b.x = x → b.trackPA = true →
        b.m.isPAat x (initBal x) = true ∧ b.sent = lb.preAcceptsSent.toNat ∧ b.need ≤ 2 * fR - 1) ∧
      (S'.paRcpt x).length ≤ lb.preAcceptsSent.toNat)
    (hpd : ∀ r b, S'.pending r = some b → S.pending r = some b ∨
      (b.trackPA = false ∧ ∀ x c, b.m.isPAat x c = false)) :
    InvPM S' := by
  have hold : ∀ r e, S'.ev r e → (∀ to m, e ≠ .sent to m) → S.ev r e := by
    intro r e h hn
    rcases hev r e h with h | ⟨to, m, rfl, -⟩
    · exact h
    · exact absurd rfl (hn to m)
  have hacc : ∀ r y b v, S'.ev r (.accept y b v) → S.ev r (.accept y b v) :=
    fun r y b v h => hold _ _ h (fun _ _ h => by cases h)
  have hvote : ∀ r y b st v, S'.ev r (.vote y b st v) → S.ev r (.vote y b st v) :=
    fun r y b st v h => hold _ _ h (fun _ _ h => by cases h)
  have hph : ∀ r y b v, S'.ev r (.phase1 y b v) → S.ev r (.phase1 y b v) :=
    fun r y b v h => hold _ _ h (fun _ _ h => by cases h)
  have hcm : ∀ r y c u, S'.ev r (.commit y c u) → S.ev r (.commit y c u) :=
    fun r y c u h => hold _ _ h (fun _ _ h => by cases h)
  have hprep : ∀ r m e, S'.prepReport r m e → S.prepReport r m e := by
    rintro r m e ⟨he, ⟨to, hm, rfl⟩ | rfl⟩
    · rcases hev r _ he with h | ⟨to', m', h1, h2⟩
      · exact ⟨h, Or.inl ⟨to, hmsg _ _ _ hm, rfl⟩⟩
      · simp only [Event.sent.injEq] at h1; obtain ⟨-, rfl⟩ := h1; exact absurd rfl (h2 m)
    · exact ⟨hold _ _ he (fun _ _ h => by cases h), Or.inr rfl⟩
  exact {
    arOk := arOk_frame hP (fun a r m h => hmsg _ _ _ h) hacc
      (fun q y b v h => Or.inl (hvote _ _ _ _ _ h)) hmono hcv hbal
    commitProp := commitProp_frame hP hcm hmono
    commitMsgProp := commitMsgProp_frame hP (fun fr to m h => hmsg _ _ _ h) hmono
    lbProp := lbProp_frame hP hlb hacc hmono
    parCom := parCom_frame hP (fun a r m h => hmsg _ _ _ h) hmono
    parSt := parSt_frame hP (fun a r m h => hmsg _ _ _ h) hsent
    paFresh := paFresh_frame hP hlb hph
    paCmds := paCmds_frame hP hlb hph
    paSent := hps
    pendPA := fun r b hb x c hc => by
      rcases hpd r b hb with h | ⟨-, h⟩
      · exact hP.pendPA r b h x c hc
      · rw [h x c] at hc; cases hc
    paVoteMsg := paVoteMsg_frame hP hvote hsent
    parNoPA := parNoPA_frame hP (fun a r m h => hmsg _ _ _ h) hvote
    aeF := aeF_frame hP hlb hsent
    repLead := repLead_frame hP hprep hbal
    paGe := paGe_frame hP hvote hph
    phAttrs := phAttrs_frame hP hph hmono
    accWit := accWit_frame hP hacc hmono hcv
    accVote := accVote_frame hP hacc hmono
    cmdSafe := CmdSafeProof.cmdSafe_frame' hP hph hmono hbal
      (fun q y c st u h => Or.inl (hvote _ _ _ _ _ h))
    accSup := CmdSafeProof.accSup_frame hP hmono hacc }


/-- `pm_frame` with `pendPA` of the post-state given. -/
theorem pm_frame' (hP : InvPM S)
    (hmono : ∀ r e, S.ev r e → S'.ev r e)
    (hev : ∀ r e, S'.ev r e → S.ev r e ∨ ∃ to m, e = .sent to m ∧ ∀ p, m ≠ .prepareReply p)
    (hmsg : ∀ fr to m, m ∈ S'.msgs fr to → m ∈ S.msgs fr to)
    (hsent : ∀ fr to m, m ∈ S.sent fr to → m ∈ S'.sent fr to)
    (hcv : ∀ y u, S.committedVal y u → S'.committedVal y u)
    (hbal : ∀ r y w, (S.rep r).inst y = some w →
      ∃ w', (S'.rep r).inst y = some w' ∧ zz w.bal ≤ zz w'.bal)
    (hlb : ∀ r x w' lb', (S'.rep r).inst x = some w' → w'.lb = some lb' →
      ∃ w lb, (S.rep r).inst x = some w ∧ w.lb = some lb ∧ LbPM lb lb')
    (hps : ∀ x w lb, x.q < nR → (S'.rep x.q).inst x = some w → w.lb = some lb →
      lb.lastTriedBallot = initBal x →
      lb.preAcceptsSent.toNat ≤ 2 * fR - 1 ∧
      (∀ b, S'.pending x.q = some b → b.x = x → b.trackPA = true →
        b.m.isPAat x (initBal x) = true ∧ b.sent = lb.preAcceptsSent.toNat ∧ b.need ≤ 2 * fR - 1) ∧
      (S'.paRcpt x).length ≤ lb.preAcceptsSent.toNat)
    (hpa : ∀ r b, S'.pending r = some b → ∀ x c, b.m.isPAat x c = true →
      b.trackPA = true ∧ b.x = x) :
    InvPM S' := by
  have hold : ∀ r e, S'.ev r e → (∀ to m, e ≠ .sent to m) → S.ev r e := by
    intro r e h hn
    rcases hev r e h with h | ⟨to, m, rfl, -⟩
    · exact h
    · exact absurd rfl (hn to m)
  have hacc : ∀ r y b v, S'.ev r (.accept y b v) → S.ev r (.accept y b v) :=
    fun r y b v h => hold _ _ h (fun _ _ h => by cases h)
  have hvote : ∀ r y b st v, S'.ev r (.vote y b st v) → S.ev r (.vote y b st v) :=
    fun r y b st v h => hold _ _ h (fun _ _ h => by cases h)
  have hph : ∀ r y b v, S'.ev r (.phase1 y b v) → S.ev r (.phase1 y b v) :=
    fun r y b v h => hold _ _ h (fun _ _ h => by cases h)
  have hcm : ∀ r y c u, S'.ev r (.commit y c u) → S.ev r (.commit y c u) :=
    fun r y c u h => hold _ _ h (fun _ _ h => by cases h)
  have hprep : ∀ r m e, S'.prepReport r m e → S.prepReport r m e := by
    rintro r m e ⟨he, ⟨to, hm, rfl⟩ | rfl⟩
    · rcases hev r _ he with h | ⟨to', m', h1, h2⟩
      · exact ⟨h, Or.inl ⟨to, hmsg _ _ _ hm, rfl⟩⟩
      · simp only [Event.sent.injEq] at h1; obtain ⟨-, rfl⟩ := h1; exact absurd rfl (h2 m)
    · exact ⟨hold _ _ he (fun _ _ h => by cases h), Or.inr rfl⟩
  exact {
    arOk := arOk_frame hP (fun a r m h => hmsg _ _ _ h) hacc
      (fun q y b v h => Or.inl (hvote _ _ _ _ _ h)) hmono hcv hbal
    commitProp := commitProp_frame hP hcm hmono
    commitMsgProp := commitMsgProp_frame hP (fun fr to m h => hmsg _ _ _ h) hmono
    lbProp := lbProp_frame hP hlb hacc hmono
    parCom := parCom_frame hP (fun a r m h => hmsg _ _ _ h) hmono
    parSt := parSt_frame hP (fun a r m h => hmsg _ _ _ h) hsent
    paFresh := paFresh_frame hP hlb hph
    paCmds := paCmds_frame hP hlb hph
    paSent := hps
    pendPA := hpa
    paVoteMsg := paVoteMsg_frame hP hvote hsent
    parNoPA := parNoPA_frame hP (fun a r m h => hmsg _ _ _ h) hvote
    aeF := aeF_frame hP hlb hsent
    repLead := repLead_frame hP hprep hbal
    paGe := paGe_frame hP hvote hph
    phAttrs := phAttrs_frame hP hph hmono
    accWit := accWit_frame hP hacc hmono hcv
    accVote := accVote_frame hP hacc hmono
    cmdSafe := CmdSafeProof.cmdSafe_frame' hP hph hmono hbal
      (fun q y c st u h => Or.inl (hvote _ _ _ _ _ h))
    accSup := CmdSafeProof.accSup_frame hP hmono hacc }

end

end PMProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace PMProof

/-- `InvPM` under a step that keeps the records, the history, the messages and the pending
broadcasts, and only moves messages from `outbox` to `sent` (the frame steps, the no-op
deliveries). -/
theorem pm_same {S S' : Sys} (hP : InvPM S) (hinst : ∀ r, (S'.rep r).inst = (S.rep r).inst)
    (hhist : S'.hist = S.hist) (hmsgs : S'.msgs = S.msgs)
    (hsent : ∀ fr to m, m ∈ S.sent fr to → m ∈ S'.sent fr to)
    (hpend : S'.pending = S.pending)
    (hrc : ∀ fr to m, m ∈ S'.sent fr to ++ S'.outbox fr to → m ∈ S.sent fr to ++ S.outbox fr to) :
    InvPM S' := by
  have hev : ∀ r e, S'.ev r e ↔ S.ev r e := by intro r e; simp only [Sys.ev, hhist]
  have hcv : ∀ y u, S.committedVal y u → S'.committedVal y u := by
    intro y u h; simpa only [Sys.committedVal, Sys.ev, hhist, hmsgs] using h
  refine pm_frame hP (fun r e h => (hev r e).mpr h) (fun r e h => Or.inl ((hev r e).mp h))
    (fun fr to m h => by rw [hmsgs] at h; exact h) hsent hcv
    (fun r y w h => ⟨w, by rw [hinst]; exact h, Int.le_refl _⟩)
    (fun r x w' lb' h hl => ⟨w', lb', by rw [← hinst]; exact h, hl, LbPM.refl _⟩) ?_
    (fun r b h => Or.inl (by rw [hpend] at h; exact h))
  refine ps_frame hP (fun x w' lb' h hl => ⟨w', lb', by rw [← hinst]; exact h, hl, rfl, rfl⟩)
    (fun r b h _ => by rw [hpend] at h; exact h) (fun x a h => ?_)
  obtain ⟨m, hm, hp⟩ := List.any_eq_true.mp h
  exact List.any_eq_true.mpr ⟨m, hrc _ _ _ hm, hp⟩

end PMProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

namespace PMProof

/-- `InvPM` under a step that keeps the records, the history and the pending broadcasts, and
only drops messages (`lose`) or moves them from `outbox` to `sent`. -/
theorem pm_sub {S S' : Sys} (hP : InvPM S) (hinst : ∀ r, (S'.rep r).inst = (S.rep r).inst)
    (hhist : S'.hist = S.hist) (hmsg : ∀ fr to m, m ∈ S'.msgs fr to → m ∈ S.msgs fr to)
    (hcv : ∀ y u, S.committedVal y u → S'.committedVal y u)
    (hsent : ∀ fr to m, m ∈ S.sent fr to → m ∈ S'.sent fr to)
    (hpend : S'.pending = S.pending)
    (hrc : ∀ fr to m, m ∈ S'.sent fr to ++ S'.outbox fr to → m ∈ S.sent fr to ++ S.outbox fr to) :
    InvPM S' := by
  have hev : ∀ r e, S'.ev r e ↔ S.ev r e := by intro r e; simp only [Sys.ev, hhist]
  refine pm_frame hP (fun r e h => (hev r e).mpr h) (fun r e h => Or.inl ((hev r e).mp h))
    hmsg hsent hcv
    (fun r y w h => ⟨w, by rw [hinst]; exact h, Int.le_refl _⟩)
    (fun r x w' lb' h hl => ⟨w', lb', by rw [← hinst]; exact h, hl, LbPM.refl _⟩) ?_
    (fun r b h => Or.inl (by rw [hpend] at h; exact h))
  refine ps_frame hP (fun x w' lb' h hl => ⟨w', lb', by rw [← hinst]; exact h, hl, rfl, rfl⟩)
    (fun r b h _ => by rw [hpend] at h; exact h) (fun x a h => ?_)
  obtain ⟨m, hm, hp⟩ := List.any_eq_true.mp h
  exact List.any_eq_true.mpr ⟨m, hrc _ _ _ hm, hp⟩

end PMProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
