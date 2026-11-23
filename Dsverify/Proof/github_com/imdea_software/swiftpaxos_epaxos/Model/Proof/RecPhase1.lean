/-
A handler step of replica `i` that starts a Phase 1 of its instance `x` at its ballot `b`
(`startPhase1`): fresh attributes (`updateAttributes` from deps all `-1`), the record becomes
PRE-ACCEPTED at `b` with a fresh bookkeeping, the events `phase1`, the own pre-accept `vote` and
`attrsRec` are logged, the conflicts map records `x`, and the PreAccept broadcast is left pending
(`inv_phase1_start`). Used by `handlePrepareReply`'s sub-cases 5 and 6 (an instance the replica
holds, a recovery ballot); `handlePropose` (a fresh instance at its initial ballot, with
`makeBallot`, the owner and the `crtInstance` bump) needs the generalization described in
notes/prove-model.md.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.RecAccept
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HCommit
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Conf

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace RecPhase1Proof

open HStepProof HLocal SafeProof AuxProof RecCommitProof RecAcceptProof ConfProof CommitProof

/-- The record `startPhase1` writes. -/
def p1Rec (x : InstId) (cmds : List WCmd) (b seq : w32) (deps : List w32) (lbN : LbRec) : InstRec :=
  { cmds := some cmds, bal := b, vbal := b, status := stPREACCEPTED, seq := seq, deps := deps,
    lb := some lbN, id := x }

/-- The fresh bookkeeping `startPhase1` writes (as far as `Inv` reads it). -/
def LbFresh (lb lbN : LbRec) (b : w32) (cmds : List WCmd) (deps : List w32) : Prop :=
  lbN.lastTriedBallot = b ∧ lbN.ballot = W32 (-1) ∧ lbN.status = stPREACCEPTED ∧
  lbN.preparing = false ∧ lbN.tryingToPreAccept = false ∧
  lbN.clientProposals = lb.clientProposals ∧ lbN.preAcceptOKs = W64 0 ∧ lbN.acceptOKs = W64 0 ∧
  lbN.cmds = some cmds ∧ lbN.deps = deps

/-- `updateAttributes` from deps all `-1` on a state with `S.rep i`'s conflicts map gives
followable deps. -/
theorem ua_depsOk (S : Sys) (i : Nat) (hS : Inv S) (hi : i < nR) (σu : RState)
    (hσu : σu.conflicts = (S.rep i).conflicts)
    (hσus : σu.lastScan = (S.rep i).lastScan ∧ σu.lastPut = (S.rep i).lastPut) (cmds : List WCmd) :
    depsOk (updateAttributes σu cmds (W32 0) (List.replicate nR (W32 (-1)))).2.1 := by
  obtain ⟨u1, u2, -, u4⟩ := ua_spec σu cmds (W32 0) (List.replicate nR (W32 (-1)))
  have hl : (List.replicate nR (W32 (-1))).length = nR := by simp
  refine ⟨by rw [u1, hl], fun d hd => ?_⟩
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hd
  have hq' : q < nR := by rw [u1, hl] at hq; exact hq
  have hget : (updateAttributes σu cmds (W32 0) (List.replicate nR (W32 (-1)))).2.1[q] =
      (updateAttributes σu cmds (W32 0) (List.replicate nR (W32 (-1)))).2.1.getD q (W32 0) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]; rfl
  have hget0 : (List.replicate nR (W32 (-1))).getD q (W32 0) = W32 (-1) := by
    simp [List.getD_eq_getElem?_getD, hq']
  rw [hget]
  rcases u4 q with h | ⟨hsrc, hlt⟩
  · rw [h, hget0]; exact Or.inl (by decide)
  · rw [hget0] at hlt
    have hm1 : zz (W32 (-1)) = -1 := by decide
    rw [hm1] at hlt
    have h0 : 0 ≤ zz ((updateAttributes σu cmds (W32 0) (List.replicate nR (W32 (-1)))).2.1.getD q (W32 0)) := by
      omega
    refine Or.inr ⟨h0, ?_⟩
    have hne : (S.rep i).inst ⟨q, toN ((updateAttributes σu cmds (W32 0) (List.replicate nR (W32 (-1)))).2.1.getD q (W32 0))⟩ ≠ none := by
      generalize (updateAttributes σu cmds (W32 0) (List.replicate nR (W32 (-1)))).2.1.getD q (W32 0) = d at h0 hsrc ⊢
      rcases hsrc with ⟨k, pp, hk, hpk⟩ | h | h | h
      · rw [hσu] at hk
        obtain ⟨k1, k2, k3⟩ := hS.1.1.2.2.2.1 i hi q k pp hk
        rcases hpk with h | h <;> subst h
        · exact k2 h0
        · exact k3 h0
      · subst h; rw [hσus.1] at h0 ⊢; exact (hS.2.classWf i hi q hq').1 h0
      · subst h; rw [hσus.2] at h0 ⊢; exact (hS.2.classWf i hi q hq').2.1 h0
      · subst h; exact absurd h0 (by decide)
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hne
    exact (hS.1.1.2.1 i hi _ w hw).2.2.1

theorem recorded_instOf {e : Event} {y : InstId} {c : List WCmd} (h : e.recorded = some (y, c)) :
    e.instOf = some y := by
  cases e <;> simp only [Event.recorded, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    simp only [Event.instOf, h.1]

/-- (`InvPM`) A handler step of an idle replica appends its direct sends to its outbox. -/
theorem pm_outbox_eq {S S' : Sys} {i : Nat} {σ' : RState} {E : List Event}
    {snd : Nat → List Msg} {pend : Option Bcast} (hH : HS S S' i σ' E snd pend)
    (hidle : S.pending i = none) (fr to : Nat) :
    S'.outbox fr to = S.outbox fr to ++ (if fr = i then snd to else []) := by
  have h1 := hH.msgs fr to
  have hi : S'.intended fr to = if fr = i then intendedOf pend to else S.intended fr to := by
    unfold Sys.intended
    rw [hH.pending]
    by_cases hf : fr = i
    · subst hf; simp only [upd_same, if_true]; rfl
    · simp only [upd_other _ _ _ _ hf, hf, if_false]
  unfold Sys.msgs at h1
  rw [hH.sent, hi] at h1
  by_cases hf : fr = i
  · subst hf
    have h0 : S.intended fr to = [] := by unfold Sys.intended; rw [hidle]
    simp only [if_true, h0, List.append_nil] at h1 ⊢
    have h2 : S.sent fr to ++ (S'.outbox fr to ++ intendedOf pend to) =
        S.sent fr to ++ ((S.outbox fr to ++ snd to) ++ intendedOf pend to) := by
      simpa only [List.append_assoc] using h1
    exact List.append_cancel_right (List.append_cancel_left h2)
  · simp only [hf, if_false, List.append_nil] at h1 ⊢
    have h2 : S.sent fr to ++ (S'.outbox fr to ++ S.intended fr to) =
        S.sent fr to ++ (S.outbox fr to ++ S.intended fr to) := by
      simpa only [List.append_assoc] using h1
    exact List.append_cancel_right (List.append_cancel_left h2)

/-- (`InvPM`) A handler step of an idle replica whose direct sends carry no PreAccept at an
initial ballot does not grow the thrifty broadcasts' recipients. -/
theorem pm_paRcpt_le {S S' : Sys} {i : Nat} {σ' : RState} {E : List Event}
    {snd : Nat → List Msg} {pend : Option Bcast} (hH : HS S S' i σ' E snd pend)
    (hidle : S.pending i = none)
    (hsnd : ∀ to m, m ∈ snd to → ∀ x, m.isPAat x (initBal x) = false) (y : InstId) :
    (S'.paRcpt y).length ≤ (S.paRcpt y).length := by
  refine List.Sublist.length_le ?_
  unfold Sys.paRcpt
  refine PMProof.filter_sub (fun a ha => ?_)
  obtain ⟨m, hm, hpa⟩ := List.any_eq_true.mp ha
  rw [hH.sent, pm_outbox_eq hH hidle] at hm
  refine List.any_eq_true.mpr ⟨m, ?_, hpa⟩
  simp only [List.mem_append] at hm ⊢
  rcases hm with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · split at h
    · rw [hsnd a m h y] at hpa; cases hpa
    · cases h

/-- **Starting a Phase 1 at an own recovery ballot keeps the invariant.** -/
theorem inv_phase1_start (S S' : Sys) (i : Nat) (σ' σu σb : RState) (x : InstId) (w : InstRec)
    (lb lbN : LbRec) (b n : w32) (cmds : List WCmd) (seq : w32) (deps : List w32) (B : Bcast)
    (m : PreAccept) (hS : Inv S) (hi : i < nR) (hidle : S.idle i)
    (hd : deps = (updateAttributes σu cmds (W32 0) (List.replicate nR (W32 (-1)))).2.1)
    (hσu : σu.conflicts = (S.rep i).conflicts)
    (hσus : σu.lastScan = (S.rep i).lastScan ∧ σu.lastPut = (S.rep i).lastPut)
    (hH : HS S S' i σ' [.phase1 x b ⟨cmds, W32 (-1), deps⟩, .vote x b stPREACCEPTED ⟨cmds, seq, deps⟩,
      .attrsRec x cmds deps] (fun _ => []) B.norm)
    (hchan : S'.proposeChan = S.proposeChan)
    (hB : B.x = x ∧ B.m = .preAccept m ∧ B.peers = (S.rep i).peerOrder.take (nR - 1) ∧
      B.need = 2 * fR - 1 ∧ B.sent = 0)
    (hmm : m.leaderId = W32 i ∧ (⟨toN m.replica, toN m.inst⟩ : InstId) = x ∧ 0 ≤ zz m.replica ∧
      zz m.replica < nR ∧ 0 ≤ zz m.inst ∧ toN m.inst + 1 < MAX_INSTANCE ∧ m.ballot = b ∧
      m.command = cmds ∧ m.seq = W32 (-1) ∧ m.deps = deps)
    (hσ : σ'.inst = upd (S.rep i).inst x (some (p1Rec x cmds b seq deps lbN)))
    (hc : σ'.id = (S.rep i).id ∧ σ'.peerOrder = (S.rep i).peerOrder ∧
      σ'.crtInstance = (S.rep i).crtInstance ∧
      σ'.execedUpTo = (S.rep i).execedUpTo ∧ σ'.store = (S.rep i).store)
    (hconf : σb.conflicts = (S.rep i).conflicts ∧
      σ'.conflicts = (updateConflicts σb cmds x.q n seq).conflicts)
    (hcls : σb.lastScan = (S.rep i).lastScan ∧ σb.lastPut = (S.rep i).lastPut ∧
      σb.inst = σ'.inst ∧ σ'.lastScan = (updateConflicts σb cmds x.q n seq).lastScan ∧
      σ'.lastPut = (updateConflicts σb cmds x.q n seq).lastPut)
    (hn : 0 ≤ zz n ∧ toN n = x.i)
    (hw : (S.rep i).inst x = some w) (hlb : w.lb = some lb) (hnc : ¬ isCommitted w.status)
    (hb : zz w.bal ≤ zz b) (hlt : lb.lastTriedBallot = b) (hbN : (nR : Int) ≤ zz b)
    (hnoph : ∀ r u, ¬ S.ev r (.phase1 x b u))
    (hnoacc : ∀ r u, ¬ S.ev r (.accept x b u))
    (hnovPA : ∀ r st u, isPA st → ¬ S.ev r (.vote x b st u))
    (hsafeP : S.safePh x b)
    (hcmdS : ∀ c, realBal x c → zz c < zz b → ∀ Z, Z ≠ cmds → S.cmdBlocked x c Z)
    (hcne : cmds ≠ [])
    (hval : cmds = noop ∨ ∃ ps, S.owner x = some ps ∧ cmds = ps.map (·.cmd))
    (hk : LbFresh lb lbN b cmds deps) (hae : lbN.allEqual = true := by rfl)
    (htr : B.trackPA = true := by rfl) :
    Inv S' := by
  obtain ⟨c1, c2, c3, c5, c6⟩ := hc
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k10, k12⟩ := hk
  obtain ⟨hBx, hBm, hBp, hBn, hBs⟩ := hB
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8a, m8b, m8c⟩ := hmm
  have hdeps : depsOk deps := by rw [hd]; exact ua_depsOk S i hS hi σu hσu hσus cmds
  generalize hw'd : p1Rec x cmds b seq deps lbN = w' at hσ
  have hA := hS.2
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19,
    s20, s21, s22, s23, s24, s25, s26, s27⟩ := hS.1
  have hxq : x.q < nR := (s1.2.1 i hi x w hw).2.1
  have hb0 : 0 ≤ zz b := by omega
  have hbI : b ≠ initBal x := by
    intro h; rw [h, zz_initBal x hxq] at hbN; simp [nR] at hbN hxq; omega
  have hPA : isPA stPREACCEPTED := Or.inl rfl
  have hnotACC : ¬ isPA stACCEPTED := by rintro (h | h) <;> cases h
  -- events
  have hE : ∀ r e, S'.ev r e ↔ S.ev r e ∨
      (r = i ∧ (e = .phase1 x b ⟨cmds, W32 (-1), deps⟩ ∨
        e = .vote x b stPREACCEPTED ⟨cmds, seq, deps⟩ ∨ e = .attrsRec x cmds deps)) := by
    intro r e; rw [hH.ev_iff]; simp
  have hold : ∀ r e, S'.ev r e → (∀ y c u, e ≠ .phase1 y c u) → (∀ y c st u, e ≠ .vote y c st u) →
      (∀ y c d, e ≠ .attrsRec y c d) → S.ev r e := by
    intro r e he h1 h2 h3
    rcases (hE r e).mp he with h | ⟨-, rfl | rfl | rfl⟩
    · exact h
    · exact absurd rfl (h1 _ _ _)
    · exact absurd rfl (h2 _ _ _ _)
    · exact absurd rfl (h3 _ _ _)
  have hnotE : ∀ e, (∀ y c u, e ≠ .phase1 y c u) → (∀ y c st u, e ≠ .vote y c st u) →
      (∀ y c d, e ≠ .attrsRec y c d) → i = i →
      e ∉ [Event.phase1 x b ⟨cmds, W32 (-1), deps⟩, .vote x b stPREACCEPTED ⟨cmds, seq, deps⟩,
        .attrsRec x cmds deps] := by
    intro e h1 h2 h3 _ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h
    · exact h1 _ _ _ h
    · exact h2 _ _ _ _ h
    · exact h3 _ _ _ h
  -- messages
  have hmsgs : ∀ fr to m', m' ∈ S'.msgs fr to ↔ m' ∈ S.msgs fr to ∨
      (fr = i ∧ m' = .preAccept m ∧ to ∈ (S.rep i).peerOrder.take (nR - 1)) := by
    intro fr to m'
    rw [hH.mem_msgs]
    constructor
    · rintro (h | ⟨hf, h | h⟩)
      · exact Or.inl h
      · cases h
      · obtain ⟨h1, h2⟩ := mem_intended_norm h
        rw [hBm] at h1; rw [hBp] at h2; exact Or.inr ⟨hf, h1, h2⟩
    · rintro (h | ⟨hf, rfl, hto⟩)
      · exact Or.inl h
      · refine Or.inr ⟨hf, Or.inr ?_⟩
        have hne : B.norm = some B := by
          unfold Bcast.norm; rw [if_neg]; rintro (h | h)
          · rw [hBp] at h; rw [h] at hto; cases hto
          · rw [hBn, hBs] at h; simp [fR] at h
        rw [hne]; simp only [intendedOf]; rw [hBp, if_pos hto, hBm]; simp
  have hvoteO : ∀ r y c st u, S'.ev r (.vote y c st u) → S.ev r (.vote y c st u) ∨
      (r = i ∧ y = x ∧ c = b ∧ st = stPREACCEPTED ∧ u = ⟨cmds, seq, deps⟩) := by
    intro r y c st u h
    rcases (hE r _).mp h with h | ⟨hr, h | h | h⟩
    · exact Or.inl h
    · cases h
    · simp only [Event.vote.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact Or.inr ⟨hr, rfl, rfl, rfl, rfl⟩
    · cases h
  have hphO : ∀ r y c u, S'.ev r (.phase1 y c u) → S.ev r (.phase1 y c u) ∨
      (r = i ∧ y = x ∧ c = b ∧ u = ⟨cmds, W32 (-1), deps⟩) := by
    intro r y c u h
    rcases (hE r _).mp h with h | ⟨hr, h | h | h⟩
    · exact Or.inl h
    · simp only [Event.phase1.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr ⟨hr, rfl, rfl, rfl⟩
    · cases h
    · cases h
  have haO : ∀ r y c u, S'.ev r (.accept y c u) → S.ev r (.accept y c u) :=
    fun r y c u h => hold r _ h (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h)
  have hnoPAmsg : ∀ fr to (m' : PreAccept), Msg.preAccept m' ∈ S.msgs fr to →
      (⟨toN m'.replica, toN m'.inst⟩ : InstId) = x → m'.ballot ≠ b := by
    intro fr to m' hm' hx hb'
    have := (s6.2.2.2.2.1 fr to m' hm').2
    rw [hx, hb'] at this; exact hnoph _ _ this
  have hlbX := s11 i hi x w lb hw hlb
  have noPAR : ∀ a (m' : PreAcceptReply), Msg.preAcceptReply m' ∈ S.msgs a i →
      (⟨toN m'.replica, toN m'.inst⟩ : InstId) = x → m'.ballot ≠ b := by
    intro a m' hm' hx hb'
    obtain ⟨u, hu⟩ := (s9.2.1 a i m' hm').1
    rw [hx, hb'] at hu; exact hnoph _ _ hu
  have hnotEold : ∀ r e, S.ev r e → (∀ y c d, e ≠ .attrsRec y c d) → r = i →
      e ∉ [Event.phase1 x b ⟨cmds, W32 (-1), deps⟩, .vote x b stPREACCEPTED ⟨cmds, seq, deps⟩,
        .attrsRec x cmds deps] := by
    intro r e he h3 hr h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact hnoph r _ he
    · exact hnovPA r _ _ hPA he
    · exact h3 _ _ _ rfl
  have hevB : ∀ r e r' e', S'.evBefore r e r' e' → S.ev r' e' → (∀ y c d, e' ≠ .attrsRec y c d) →
      S.evBefore r e r' e' :=
    fun r e r' e' h h' h3 => hH.evBefore_back h h' (hnotEold r' e' h' h3)
  have hcnt0 : ∀ fr to (p : Msg → Bool), p (.preAccept m) = false →
      S'.cnt fr to p = S.cnt fr to p := by
    intro fr to p hp
    rw [hH.cnt_eq]
    split
    · simp only [List.nil_append, Nat.add_eq_left, List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro m' hm'
      obtain ⟨h1, -⟩ := mem_intended_norm hm'
      rw [h1, hBm, hp]; simp
    · rfl
  have hallP : ∀ fr to (p : Msg → Bool), p (.preAccept m) = false → S.allDeliv fr to p →
      S'.allDeliv fr to p := by
    intro fr to p hp h
    refine hH.allDeliv_old h (fun _ m' hm' => ?_)
    simp only [List.nil_append] at hm'
    obtain ⟨h1, -⟩ := mem_intended_norm hm'
    rw [h1, hBm, hp]
  -- records
  have hrep : ∀ r y, (S'.rep r).inst y =
      if r = i ∧ y = x then some w' else (S.rep r).inst y := by
    intro r y
    rw [hH.rep]
    by_cases hr : r = i
    · subst hr; simp only [upd_same, hσ, upd_apply, true_and]
    · simp [upd_other _ _ _ _ hr, hr]
  have R1 : ∀ r y w2, (S'.rep r).inst y = some w2 →
      (i = r ∧ x = y ∧ w' = w2) ∨ ((S.rep r).inst y = some w2 ∧ ¬ (r = i ∧ y = x)) := by
    intro r y w2 h; rw [hrep] at h; split at h
    · rename_i hc; obtain ⟨rfl, rfl⟩ := hc; simp only [Option.some.injEq] at h
      exact Or.inl ⟨rfl, rfl, h⟩
    · rename_i hc; exact Or.inr ⟨h, hc⟩
  have R2 : ∀ r y w1, (S.rep r).inst y = some w1 →
      (i = r ∧ x = y ∧ w = w1) ∨ (S'.rep r).inst y = some w1 := by
    intro r y w1 h
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc; rw [hw] at h; cases h; exact Or.inl ⟨rfl, rfl, rfl⟩
    · right; rw [hrep, if_neg hc]; exact h
  have R3 : (S'.rep i).inst x = some w' := by rw [hrep]; simp
  have hconfLe : ∀ r, confLe (S.rep r) (S'.rep r) := by
    intro r
    by_cases hr : r = i
    · subst hr; rw [hH.rep_self]
      intro q k p hp
      rw [← hconf.1] at hp
      obtain ⟨p', hp', a1, a2⟩ := uc_le σb cmds x.q n seq q k p hp
      exact ⟨p', by rw [hconf.2]; exact hp', a1, a2⟩
    · rw [hH.rep_other hr]; exact confLe_refl _
  have hfl : ∀ r, (S'.rep r).id = (S.rep r).id ∧ (S'.rep r).peerOrder = (S.rep r).peerOrder ∧
      (S'.rep r).crtInstance = (S.rep r).crtInstance ∧
      (S'.rep r).execedUpTo = (S.rep r).execedUpTo ∧ (S'.rep r).store = (S.rep r).store := by
    intro r
    by_cases hr : r = i
    · subst hr; rw [hH.rep_self]; exact ⟨c1, c2, c3, c5, c6⟩
    · rw [hH.rep_other hr]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have W : w'.cmds = some cmds ∧ w'.bal = b ∧ w'.vbal = b ∧ w'.status = stPREACCEPTED ∧
      w'.seq = seq ∧ w'.deps = deps ∧ w'.lb = some lbN ∧ w'.id = x ∧
      instVal w' = ⟨cmds, seq, deps⟩ := by
    rw [← hw'd]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [instVal, p1Rec]⟩
  obtain ⟨W1, W2, W3, W4, W5, W6, W7, W8, W9⟩ := W
  have hnc' : ¬ isCommitted w'.status := by rw [W4]; rintro (h | h) <;> cases h
  have hwnex : w.status ≠ stEXECUTED := fun h => hnc (Or.inr h)
  have hw'nex : w'.status ≠ stEXECUTED := by rw [W4]; decide
  have hex : ∀ r y, (S'.rep r).executed y ↔ (S.rep r).executed y := by
    intro r y
    constructor
    · rintro ⟨w2, h2, hs⟩
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · exact absurd hs hw'nex
      · exact ⟨w2, h, hs⟩
    · rintro ⟨w1, h1, hs⟩
      rcases R2 r y w1 h1 with ⟨-, -, rfl⟩ | h
      · exact absurd hs hwnex
      · exact ⟨w1, h, hs⟩
  have hxlog : x ∉ S.execLog i := by
    intro h
    obtain ⟨w1, h1, hs⟩ := ((s18 i hi).2.1 x).mp h
    rw [hw] at h1; cases h1; exact hwnex hs
  have hvO : ∀ r y c st u, S'.ev r (.vote y c st u) → ¬ (r = i ∧ y = x) →
      S.ev r (.vote y c st u) := by
    intro r y c st u h hne
    rcases hvoteO r y c st u h with h | ⟨h1, h2, -⟩
    · exact h
    · exact absurd ⟨h1, h2⟩ hne
  have hpO : ∀ r y c u, S'.ev r (.phase1 y c u) → ¬ (r = i ∧ y = x) → S.ev r (.phase1 y c u) := by
    intro r y c u h hne
    rcases hphO r y c u h with h | ⟨h1, h2, -⟩
    · exact h
    · exact absurd ⟨h1, h2⟩ hne
  have hvoteNew : NewVote S i x b stPREACCEPTED ⟨cmds, seq, deps⟩ := by
    refine ⟨fun w0 h0 => ?_, fun _ st' u hst' hv => absurd hv (hnovPA i st' u hst'),
      fun _ h => absurd h hbI⟩
    rw [hw] at h0; cases h0
    exact ⟨hb, fun _ h => absurd h hbI⟩
  have hsafeM : SafeMono S S' := by
    refine ⟨fun r y w1 h1 => ?_, fun r e h => hH.ev_old h,
      fun r y c st u h => ?_,
      fun y u h => Or.inl (hold _ _ h (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
        (fun _ _ _ h => by cases h)),
      fun a y m' h hy hb' => ?_⟩
    · rcases R2 r y w1 h1 with ⟨rfl, rfl, rfl⟩ | h
      · refine ⟨w', R3, by rw [W2]; exact hb, fun _ => Or.inr ?_⟩
        rw [W2, zz_initBal _ hxq]; simp [nR] at hbN hxq; omega
      · exact ⟨w1, h, Int.le_refl _, fun h => Or.inl h⟩
    · rcases hvoteO r y c st u h with h | ⟨rfl, rfl, rfl, rfl, rfl⟩
      · exact Or.inl h
      · exact Or.inr hvoteNew
    · rcases (hmsgs _ _ _).mp h with h | ⟨-, h, -⟩
      · exact Or.inl h
      · cases h
        exfalso; apply hbI
        simp only [Msg.instOf, Option.some.injEq] at hy
        rw [m2] at hy; subst hy; rw [← m7]; exact hb'
  have hsafe : Inv.safe S' := by
    refine safe_step hsafeM s26 (fun r y c u h => Or.inl (haO r y c u h)) (fun r y c u h => ?_)
    rcases hphO r y c u h with h | ⟨-, rfl, rfl, -⟩
    · exact Or.inl h
    · exact Or.inr (safePh_mono hsafeM hsafeP)
  have hpeer := hA.peerOk i hi
  have hwf : Inv.wf S' := by
    obtain ⟨w1', w2', w3', w4', w5', w6', w7', w8'⟩ := s1
    refine ⟨fun r hr => by rw [(hfl r).1]; exact w1' r hr, fun r hr y w2 h2 => ?_,
      fun r hr q hq => by rw [(hfl r).2.2.1]; exact w3' r hr q hq,
      fun r hr q k p hk => ?_, fun r hr q hq n' hn' => ?_, fun fr' to hne => ?_,
      fun fr' to n' hn' => ?_, fun r b' hb' => ?_⟩
    · rcases R1 r y w2 h2 with ⟨rfl, rfl, rfl⟩ | ⟨h, -⟩
      · obtain ⟨g1, g2, g3, -, -, g6, g7⟩ := w2' i hi x w hw
        refine ⟨W8, g2, g3, fun _ => by rw [W6]; exact hdeps,
          fun lb2 hl2 _ => ?_, fun hq => by rw [W7]; simp, fun lb2 ps hl2 hps => ?_⟩
        · rw [W7] at hl2; cases hl2; rw [k12]; exact hdeps
        · rw [W7] at hl2; cases hl2; rw [hH.owner]; rw [k6] at hps; exact g7 lb ps hlb hps
      · obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := w2' r hr y w2 h
        exact ⟨g1, g2, g3, g4, g5, g6, fun lb ps hlb hps => by rw [hH.owner]; exact g7 lb ps hlb hps⟩
    · have grow : ∀ y, (S.rep r).inst y ≠ none → (S'.rep r).inst y ≠ none := by
        intro y hy hy'
        obtain ⟨w1, h1⟩ := Option.ne_none_iff_exists'.mp hy
        rcases R2 r y w1 h1 with ⟨rfl, rfl, -⟩ | h
        · rw [R3] at hy'; cases hy'
        · rw [h] at hy'; cases hy'
      by_cases hr' : r = i
      · subst hr'
        rw [hH.rep_self, hconf.2] at hk
        have := uc_conf σb cmds x.q n seq
          (fun q v => q < nR ∧ (0 ≤ zz v → σ'.inst ⟨q, toN v⟩ ≠ none))
          (by
            intro q k p h; rw [hconf.1] at h
            obtain ⟨k1', k2', k3'⟩ := w4' r hr q k p h
            have g := grow; rw [hH.rep_self] at g
            exact ⟨⟨k1', fun h0 => g _ (k2' h0)⟩, ⟨k1', fun h0 => g _ (k3' h0)⟩⟩)
          ⟨hxq, fun _ => by rw [hσ]; simp [upd_apply, hn.2]⟩
          ⟨hxq, fun h => by simp [zz] at h⟩ q k p hk
        rw [hH.rep_self]
        exact ⟨this.1.1, this.1.2, this.2.2⟩
      · rw [hH.rep_other hr'] at hk ⊢
        exact w4' r hr q k p hk
    · rw [(hfl r).2.2.2.1] at hn'
      exact (hex r _).mpr (w5' r hr q hq n' hn')
    · by_cases h0 : S.msgs fr' to = []
      · obtain ⟨m', hm'⟩ := List.exists_mem_of_ne_nil _ hne
        rcases (hmsgs _ _ _).mp hm' with h | ⟨rfl, -, hto⟩
        · rw [h0] at h; cases h
        · exact ⟨hi, (hpeer.2 to hto).1, fun h => (hpeer.2 to hto).2 h.symm⟩
      · exact w6' fr' to h0
    · rcases hH.delOk fr' to n' hn' with h | h
      · rw [hH.sent]; exact w7' fr' to n' h
      · rw [hH.sent]; exact h
    · rw [hH.pending] at hb'
      by_cases hr : r = i
      · subst hr
        rw [upd_same] at hb'
        obtain ⟨rfl, hpn, hsn⟩ := norm_some hb'
        refine ⟨hi, by rw [hH.execCur]; exact hidle.2, hpn, hsn, by rw [hBp]; exact hpeer.1,
          fun q hq => by rw [hBp] at hq; exact hpeer.2 q hq, w', lbN, by rw [hBx]; exact R3, W7⟩
      · rw [upd_other _ _ _ _ hr] at hb'
        obtain ⟨d1, d2, d3, d4, d5, d6, w1, lb1, h1, hl1⟩ := w8' r b' hb'
        refine ⟨d1, by rw [hH.execCur]; exact d2, d3, d4, d5, d6, w1, lb1, ?_, hl1⟩
        rw [hrep, if_neg (fun h => hr h.1)]; exact h1
  have hbal : Inv.ballots S' := by
    refine ⟨fun r hr y w2 h2 => ?_, fun r hr y c st u he => ?_⟩
    · rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · rw [W2, W3]; exact Int.le_refl _
      · exact s5.1 r hr y w2 h
    · rcases hvoteO r y c st u he with he | ⟨rfl, rfl, rfl, -, -⟩
      · obtain ⟨w1, h1, hle⟩ := s5.2 r hr y c st u he
        rcases R2 r y w1 h1 with ⟨rfl, rfl, rfl⟩ | h
        · exact ⟨w', R3, by rw [W2]; omega⟩
        · exact ⟨w1, h, hle⟩
      · exact ⟨w', R3, by rw [W2]; exact Int.le_refl _⟩
  have hcountP : (S'.hist.filter (· = (i, .phase1 x b ⟨cmds, W32 (-1), deps⟩))).length = 1 := by
    rw [hH.hist, List.filter_append, List.length_append]
    have h0 : (S.hist.filter (· = (i, .phase1 x b ⟨cmds, W32 (-1), deps⟩))).length = 0 := by
      simp only [List.length_eq_zero_iff, List.filter_eq_nil_iff, decide_eq_true_eq]
      intro a ha hae; subst hae; exact hnoph i _ ha
    rw [h0]; simp
  have hown : Inv.ballotOwner S' := by
    obtain ⟨o1, o2, o3, o4, o5, o6⟩ := s6
    refine ⟨fun r y c he => ?_, fun r y c u he => ?_, fun r y c u he => ?_,
      fun r to m' hm' => ?_, fun r to m' hm' => ?_, fun r to m' hm' => ?_⟩
    · have h := hold r _ he (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
        (fun _ _ _ h => by cases h)
      refine ⟨(o1 r y c h).1, ?_⟩
      rw [hH.count_eq (fun _ => hnotE _ (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
        (fun _ _ _ h => by cases h) rfl)]
      exact (o1 r y c h).2
    · rcases hphO r y c u he with h | ⟨rfl, rfl, rfl, rfl⟩
      · exact hH.evBefore_old (o2 r y c u h)
      · exact (hH.evBefore_iff _ _ _ _).mpr
          (Or.inr (Or.inl ⟨by rw [← hlt]; exact hlbX.1, rfl, by simp⟩))
    · exact hH.ev_old (o3 r y c u (haO _ _ _ _ he))
    · rcases (hmsgs _ _ _).mp hm' with h | ⟨-, h, -⟩
      · obtain ⟨d1, d2⟩ := o4 r to m' h; exact ⟨d1, hH.ev_old d2⟩
      · cases h
    · rcases (hmsgs _ _ _).mp hm' with h | ⟨rfl, h, -⟩
      · obtain ⟨d1, d2⟩ := o5 r to m' h; exact ⟨d1, hH.ev_old d2⟩
      · cases h
        refine ⟨m1, hH.ev_new ?_⟩
        rw [m2, m7, m8a, m8b, m8c]; simp
    · rcases (hmsgs _ _ _).mp hm' with h | ⟨-, h, -⟩
      · obtain ⟨d1, d2⟩ := o6 r to m' h; exact ⟨d1, hH.ev_old d2⟩
      · cases h
  have hop : Inv.oneProposal S' := by
    obtain ⟨p1, p2, p3⟩ := s7
    refine ⟨fun r r' y c u u' he he' => ?_, fun r r' y c u u' he he' =>
      p2 r r' y c u u' (haO _ _ _ _ he) (haO _ _ _ _ he'), fun r r' y c u u' he he' => ?_⟩
    · rcases hphO r y c u he with h | ⟨rfl, rfl, rfl, rfl⟩ <;>
        rcases hphO r' y c u' he' with h' | ⟨h1, h2, h3, rfl⟩
      · obtain ⟨d1, d2, d3⟩ := p1 r r' y c u u' h h'
        refine ⟨d1, d2, ?_⟩
        rw [hH.count_eq (fun hr => by
          subst hr; intro hm'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hm'
          rcases hm' with hm' | hm' | hm' <;> cases hm'
          exact hnoph _ _ h)]
        exact d3
      · subst h2 h3; exact absurd h (hnoph r u)
      · exact absurd h' (hnoph r' u')
      · exact ⟨h1.symm, rfl, hcountP⟩
    · rcases hphO r y c u he with h | ⟨-, rfl, rfl, rfl⟩
      · exact p3 r r' y c u u' h (haO _ _ _ _ he')
      · exact absurd (haO _ _ _ _ he') (hnoacc r' u')
  have hvf : Inv.votesFollowProposals S' := by
    refine ⟨fun r y c st u he hst => ?_, fun r y c u he => ?_⟩
    · rcases hvoteO r y c st u he with h | ⟨-, rfl, rfl, -, rfl⟩
      · obtain ⟨l, u0, h1, h2⟩ := s8.1 r y c st u h hst
        exact ⟨l, u0, hH.ev_old h1, h2⟩
      · exact ⟨i, ⟨cmds, W32 (-1), deps⟩, hH.ev_new (by simp), rfl⟩
    · rcases hvoteO r y c _ u he with h | ⟨-, -, -, h, -⟩
      · obtain ⟨l, h1⟩ := s8.2 r y c u h; exact ⟨l, hH.ev_old h1⟩
      · cases h
  have hcv' : ∀ y u, S'.committedVal y u ↔ S.committedVal y u := by
    intro y u
    constructor
    · rintro (⟨r, b', h⟩ | ⟨fr, to, m', hm', hy, rfl⟩)
      · exact Or.inl ⟨r, b', hold r _ h (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
          (fun _ _ _ h => by cases h)⟩
      · rcases (hmsgs _ _ _).mp hm' with h | ⟨-, h, -⟩
        · exact Or.inr ⟨fr, to, m', h, hy, rfl⟩
        · cases h
    · rintro (⟨r, b', h⟩ | ⟨fr, to, m', hm', hy, rfl⟩)
      · exact Or.inl ⟨r, b', hH.ev_old h⟩
      · exact Or.inr ⟨fr, to, m', hH.msgs_old hm', hy, rfl⟩
  have hprepR : ∀ r m' e, S'.prepReport r m' e ↔ S.prepReport r m' e := by
    intro r m' e
    constructor
    · rintro ⟨he, ⟨to, hm', rfl⟩ | rfl⟩
      · refine ⟨hold r _ he (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
          (fun _ _ _ h => by cases h), Or.inl ⟨to, ?_, rfl⟩⟩
        rcases (hmsgs _ _ _).mp hm' with h | ⟨-, h, -⟩
        · exact h
        · cases h
      · exact ⟨hold r _ he (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
          (fun _ _ _ h => by cases h), Or.inr rfl⟩
    · rintro ⟨he, ⟨to, hm', rfl⟩ | rfl⟩
      · exact ⟨hH.ev_old he, Or.inl ⟨to, hH.msgs_old hm', rfl⟩⟩
      · exact ⟨hH.ev_old he, Or.inr rfl⟩
  have hnotAR : ∀ e : Event, (∃ to m', e = Event.sent to m') ∨ (∃ m', e = Event.selfReply m') →
      ∀ y c d, e ≠ Event.attrsRec y c d := by
    rintro e (⟨to, m', rfl⟩ | ⟨m', rfl⟩) y c d h <;> cases h
  have hrr : Inv.repliesReportVotes S' := by
    obtain ⟨q1, q2, q3⟩ := s9
    refine ⟨fun r m' e hp => ?_, fun a r m' hm' => ?_, fun a r m' hm' => ?_⟩
    · have hp0 := (hprepR r m' e).mp hp
      have hne := hnotAR e (by rcases hp0.2 with ⟨to, -, h⟩ | h
                               · exact Or.inl ⟨to, _, h⟩
                               · exact Or.inr ⟨_, h⟩)
      obtain ⟨d1, d2, d3, d4, d5⟩ := q1 r m' e hp0
      refine ⟨d1, fun hs => hH.evBefore_old (d2 hs), fun hs => (hcv' _ _).mpr (d3 hs),
        fun hs c st u hb' => d4 hs c st u (hevB _ _ _ _ hb' hp0.1 hne),
        fun c st u hb' => ?_⟩
      obtain ⟨pp, pp', hlt', h1, h2⟩ := hb'
      have hv' : S'.ev r (.vote _ c st u) := List.mem_of_getElem? h2
      rcases hvoteO r _ c st u hv' with h | ⟨rfl, hy, rfl, -, -⟩
      · exact d5 c st u (hevB _ _ _ _ ⟨pp, pp', hlt', h1, h2⟩ h (fun _ _ _ h => by cases h))
      · obtain ⟨w1, h1', hle⟩ := (s27.2.2.2.2.1) _ m' e hi hp0
        rw [hy, hw] at h1'; cases h1'; omega
    · rcases (hmsgs _ _ _).mp hm' with hm' | ⟨-, h, -⟩
      · obtain ⟨d1, d2, d3, d4⟩ := q2 a r m' hm'
        refine ⟨?_, fun hs => ?_, fun hs => ?_, fun hs => ?_⟩
        · obtain ⟨u, hu⟩ := d1; exact ⟨u, hH.ev_old hu⟩
        · obtain ⟨e1, u, e2, e3⟩ := d2 hs; exact ⟨e1, u, hH.ev_old e2, e3⟩
        · obtain ⟨u, e2, e3⟩ := d3 hs; exact ⟨u, hH.ev_old e2, e3⟩
        · obtain ⟨u, e2, e3⟩ := d4 hs; exact ⟨u, (hcv' _ _).mpr e2, e3⟩
      · cases h
    · rcases (hmsgs _ _ _).mp hm' with hm' | ⟨-, h, -⟩
      · rcases q3 a r m' hm' with ⟨u, hu⟩ | ⟨⟨c, u, hu⟩, c2⟩
        · exact Or.inl ⟨u, hH.evBefore_old hu⟩
        · refine Or.inr ⟨⟨c, u, hH.evBefore_old hu⟩, fun m2 e' hp hy hb' => ?_⟩
          have hp0 := (hprepR _ _ _).mp hp
          have hsent : S.ev a (.sent r (.acceptReply m')) := by
            obtain ⟨pp, pp', -, -, h1⟩ := hu; exact List.mem_of_getElem? h1
          exact c2 m2 e' hp0 hy (hevB _ _ _ _ hb' hsent (fun _ _ _ h => by cases h))
      · cases h
  have hhi : Inv.prepReplyHighest S' := by
    intro r m' e hp c st u hb'
    have hp0 := (hprepR r m' e).mp hp
    have hne := hnotAR e (by rcases hp0.2 with ⟨to, -, h⟩ | h
                             · exact Or.inl ⟨to, _, h⟩
                             · exact Or.inr ⟨_, h⟩)
    exact s10 r m' e hp0 c st u (hevB _ _ _ _ hb' hp0.1 hne)
  have hlbI : Inv.lbInv S' := by
    intro r hr y w2 lb2 h2 hl2
    rcases R1 r y w2 h2 with ⟨rfl, rfl, rfl⟩ | ⟨h, hne⟩
    · rw [W7] at hl2; cases hl2
      obtain ⟨a1, -, -, a4, -⟩ := hlbX
      refine ⟨by rw [k1, ← hlt]; exact hH.ev_old a1, by rw [k1, k2, show zz (W32 (-1)) = -1 by decide]; omega,
        k5, fun c u hv0 => ?_, fun _ c2 => (by rw [k7] at c2; exact absurd rfl c2),
        ⟨[], List.nodup_nil, by rw [k7]; rfl, fun a m' h => by cases h⟩,
        ⟨[], List.nodup_nil, by rw [k8]; rfl, fun a h => by cases h⟩,
        fun c1 => (by rw [k3] at c1; cases c1), fun c1 => (by rw [k4] at c1; cases c1)⟩
      rw [k1]
      rcases hv0 with hv0 | hv0
      · rcases hphO _ _ c u hv0 with h | ⟨-, -, rfl, -⟩
        · rw [← hlt]; exact a4 c u (Or.inl h)
        · exact Int.le_refl _
      · rw [← hlt]; exact a4 c u (Or.inr (haO _ _ _ _ hv0))
    · obtain ⟨a1, a2, a3, a4, a5, ⟨Q, q1, q2, q3⟩, ⟨Q', q1', q2', q3'⟩, a8, a9⟩ :=
        s11 r hr y w2 lb2 h hl2
      refine ⟨hH.ev_old a1, a2, a3,
        fun c u hv0 => a4 c u (hv0.imp (fun h => hpO _ _ _ _ h hne) (haO _ _ _ _)),
        fun c1 c2 => ?_, ⟨Q, q1, q2, fun a m' hq => ?_⟩, ⟨Q', q1', q2', fun a hq => ?_⟩,
        fun c1 c2 c3 c4 => ?_, fun hp => ?_⟩
      · obtain ⟨d1, d2, u, d3, d4⟩ := a5 c1 c2; exact ⟨d1, d2, u, hH.ev_old d3, d4⟩
      · obtain ⟨b1, b2, b3, b4⟩ := q3 a m' hq; exact ⟨b1, b2, hH.deliveredMsg_old b3, b4⟩
      · obtain ⟨b1, b2, m', b3, b4⟩ := q3' a hq; exact ⟨b1, b2, m', hH.deliveredMsg_old b3, b4⟩
      · obtain ⟨d1, d2⟩ := a8 c1 c2 c3 c4; exact ⟨hH.ev_old d1, hH.ev_old d2⟩
      · obtain ⟨c1, c2⟩ := a9 hp
        refine ⟨c1, fun e he' => ?_⟩
        obtain ⟨d1, d2, d3⟩ := c2 e he'
        refine ⟨d1, d2, ?_⟩
        rcases d3 with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact Or.inl ⟨e1, hH.deliveredMsg_old e2⟩
        · exact Or.inr ⟨e1, hH.ev_old e2⟩
  have hagr : Inv.agreement S' := by
    refine ⟨fun y u u' h1 h2 => s12.1 y u u' ((hcv' _ _).mp h1) ((hcv' _ _).mp h2),
      fun r hr y w2 h2 hc' => ?_⟩
    rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
    · exact absurd hc' hnc'
    · obtain ⟨d1, d2⟩ := s12.2 r hr y w2 h hc'
      exact ⟨d1, (hcv' _ _).mpr d2⟩
  have hdE : S'.dEdge = S.dEdge := by
    funext y z; simp only [Sys.dEdge, hcv']
  have hsO : S'.sccOrd = S.sccOrd := by
    funext y z; simp only [Sys.sccOrd, hcv']
  have hlx : ∀ r k, S'.lexec r k = S.lexec r k := by
    intro r k
    have hcur : S'.curSlots r k = S.curSlots r k := by
      by_cases hr : r = i
      · subst hr; simp only [Sys.curSlots, hH.execCur, hidle.2]
      · simp only [Sys.curSlots, hH.execCur, hH.execIdx, hH.rep_other hr]
    simp only [Sys.lexec, hcur, hH.execLog]
    congr 1
    by_cases hr : r = i
    · subst hr
      refine RecCommitProof.slotsOn_congr _ _ _ _ (fun y hy => ?_)
      rw [hrep, if_neg]; rintro ⟨-, rfl⟩; exact hxlog hy
    · rw [hH.rep_other hr]
  have hexec : Inv.execClosed S' ∧ Inv.execCursor S' ∧ Inv.execOrder S' ∧
      Inv.execPrefix S' := by
    refine ⟨fun r hr => ?_, fun r hr => ?_, ?_, ?_⟩
    · obtain ⟨e1, e2, e3⟩ := s18 r hr
      refine ⟨by rw [hH.execLog]; exact e1, fun y => by rw [hH.execLog, hex]; exact e2 y,
        fun y w2 h2 hs => ?_⟩
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, hne⟩
      · exact absurd hs hw'nex
      obtain ⟨d1, d2⟩ := e3 y w2 h hs
      refine ⟨(hcv' _ _).mpr d1, fun z hz => ?_⟩
      rw [hex, hH.execCur]
      apply d2 z
      obtain ⟨w3, h3, hq, hz'⟩ := hz
      rw [hrep, if_neg hne] at h3
      exact ⟨w3, h3, hq, hz'⟩
    · by_cases hri : r = i
      · subst r
        have hc0 : S.execCur i = [] := hidle.2
        rw [hH.execCur, hH.execIdx]
        exact ⟨fun _ => (s19 i hr).1 hc0, fun h => absurd hc0 h⟩
      · rw [hH.rep_other hri, hH.execCur, hH.execIdx]; exact s19 r hr
    · intro r hr a c y z hac h1 h2 ht
      rw [hH.execLog] at h1 h2; rw [hdE] at ht ⊢; rw [hsO]
      exact s20 r hr a c y z hac h1 h2 ht
    · obtain ⟨p1, p2, p3⟩ := s21
      refine ⟨fun r hr k => ?_, fun r hr k => ?_, fun r hr k pre e post h => ?_⟩
      · rw [hlx, hH.gexec]; exact p1 r hr k
      · rw [hlx, (hfl r).2.2.2.2]; exact p2 r hr k
      · rw [hlx] at h; rw [hH.gexec]; exact p3 r hr k pre e post h
  have hdc : Inv.decidedChosen S' := by
    intro y u hu
    rcases s13 y u ((hcv' _ _).mp hu) with ⟨c, Q, q1, q2, q3⟩ | ⟨⟨Q, q1, q2, q3⟩, hf⟩
    · exact Or.inl ⟨c, Q, q1, q2, fun r hr => ⟨(q3 r hr).1, hH.ev_old (q3 r hr).2⟩⟩
    · refine Or.inr ⟨⟨Q, q1, q2, fun r hr => ?_⟩, hH.ev_old hf⟩
      obtain ⟨d1, d2, st, d3, d4⟩ := q3 r hr
      exact ⟨d1, d2, st, d3, hH.ev_old d4⟩
  have hdcv : Inv.depsCover S' := fun y z u u' hne h1 h2 hi' =>
    s15 y z u u' hne ((hcv' _ _).mp h1) ((hcv' _ _).mp h2) hi'
  have hwit : Inv.witnesses S' := by
    intro y u hu hn'
    obtain ⟨W, w1, w2, w3⟩ := s16 y u ((hcv' _ _).mp hu) hn'
    exact ⟨W, w1, w2, fun r hr => ⟨(w3 r hr).1, by
      obtain ⟨d, d1, d2⟩ := (w3 r hr).2; exact ⟨d, hH.ev_old d1, d2⟩⟩⟩
  have hac : Inv.attrsCover S' := by
    intro r e y cy z cz d hrec hyz hb' hint
    rcases (hH.evBefore_iff _ _ _ _).mp hb' with h | ⟨he, hr, h⟩ | ⟨hr, -, p1, p2, hlt', h1, h2⟩
    · exact s17 r e y cy z cz d hrec hyz h hint
    · subst hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h
      · cases h
      · cases h
      · simp only [Event.attrsRec.injEq] at h; obtain ⟨hz, hcz, hdz⟩ := h
        subst z; subst cz; subst d
        have hyq : y.q < nR := (hA.crtEv _ e y he (recorded_instOf hrec)).1
        rw [hd]
        exact ua_covers hA hi he hrec hyq σu hσu hσus.1 hσus.2 cmds (W32 0) _ (by simp) hint
    · subst hr
      rcases p2 with _ | _ | _ | p2
      · omega
      · simp at h2
      · rcases p1 with _ | _ | p1
        · simp at h1; subst h1; simp [Event.recorded] at hrec
        · simp at h1; subst h1; simp [Event.recorded] at hrec
        · omega
      · simp at h2
  have hslots : Inv.slots S' := by
    refine ⟨fun y u hu => ?_, fun y ps h p hp => ?_⟩
    · rw [hH.owner]; exact s22.1 y u ((hcv' _ _).mp hu)
    · rw [hH.owner] at h; rw [hH.ops]; exact s22.2 y ps h p hp
  have hco : Inv.clientOps S' := by
    have hso : S'.slotOp = S.slotOp := by funext s; simp only [Sys.slotOp, hH.owner]
    exact ExecOrd.clientOps_frame s23 hH.ops hH.gexec hH.fired (fun _ _ _ => by rw [hso])
      (fun y v h => (hcv' _ _).mpr h)
  have hcm : Inv.commitMsgs S' := by
    intro fr to m' hm'
    rcases (hmsgs _ _ _).mp hm' with hm' | ⟨-, h, -⟩
    · obtain ⟨r, c, h⟩ := s24 fr to m' hm'
      exact ⟨r, c, hH.ev_old h⟩
    · cases h
  have hpk : Inv.pendingKind S' := by
    intro r b' hb'
    rw [hH.pending] at hb'
    by_cases hr : r = i
    · subst hr; rw [upd_same] at hb'
      obtain ⟨rfl, -⟩ := norm_some hb'
      rw [hBm]; rfl
    · rw [upd_other _ _ _ _ hr] at hb'; exact s25 r b' hb'
  have hrt : Inv.replyTargets S' := by
    intro fr to m' y hm' hy hk'
    rcases (hmsgs _ _ _).mp hm' with hm' | ⟨-, rfl, -⟩
    · obtain ⟨w1, lb1, h1, hl1⟩ := s3 fr to m' y hm' hy hk'
      rcases R2 to y w1 h1 with ⟨rfl, rfl, rfl⟩ | h
      · exact ⟨w', lbN, R3, W7⟩
      · exact ⟨w1, lb1, h, hl1⟩
    · rcases hk' with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
  have hmw : Inv.msgWf S' := by
    intro fr to m' hm'
    rcases (hmsgs _ _ _).mp hm' with hm' | ⟨-, rfl, -⟩
    · exact s2 fr to m' hm'
    · refine ⟨fun q n' hq => ?_, fun ds hds => ?_⟩
      · simp only [Msg.rawId, Option.some.injEq, Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        exact ⟨m3, m4, m5, m6⟩
      · simp only [Msg.depsFields, List.mem_singleton] at hds
        subst hds; rw [m8c]; exact hdeps
  have hntpa : Inv.noTPA S' := by
    intro fr to m' hm'
    rcases (hmsgs _ _ _).mp hm' with hm' | ⟨-, rfl, -⟩
    · exact s4 fr to m' hm'
    · exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
  have hrepo : Inv.reports S' := by
    obtain ⟨c1', c2', c3', c4', c5', c6', c7', c8', c9'⟩ := s27
    refine ⟨fun r m' e hp => c1' r m' e ((hprepR r m' e).mp hp),
      fun r m' e hp => c2' r m' e ((hprepR r m' e).mp hp),
      fun r m' e hp => c3' r m' e ((hprepR r m' e).mp hp),
      fun r m' e hp c u hb' => ?_, fun r m' e hr hp => ?_,
      fun r y c st st' u u' h1 h2 h3 h4 => ?_, fun y u m' e h1 h2 h3 => ?_,
      fun r y u h1 u' => ?_, fun r m' e hp => c9' r m' e ((hprepR r m' e).mp hp)⟩
    · have hp0 := (hprepR r m' e).mp hp
      have hne := hnotAR e (by rcases hp0.2 with ⟨to, -, h⟩ | h
                               · exact Or.inl ⟨to, _, h⟩
                               · exact Or.inr ⟨_, h⟩)
      exact c4' r m' e hp0 c u (hevB _ _ _ _ hb' hp0.1 hne)
    · obtain ⟨w1, h1, hle⟩ := c5' r m' e hr ((hprepR r m' e).mp hp)
      rcases R2 r _ w1 h1 with ⟨rfl, hy, rfl⟩ | h
      · exact ⟨w', by rw [← hy]; exact R3, by rw [W2]; omega⟩
      · exact ⟨w1, h, hle⟩
    · rcases hvoteO r y c st u h3 with h3 | ⟨rfl, rfl, rfl, -, rfl⟩ <;>
        rcases hvoteO r y c st' u' h4 with h4 | ⟨-, h5, h6, -, rfl⟩
      · exact c6' r y c st st' u u' h1 h2 h3 h4
      · subst h5 h6; exact absurd h3 (hnovPA r st u h1)
      · exact absurd h4 (hnovPA r st' u' h2)
      · rfl
    · exact c7' y u m' e (hold _ _ h1 (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
        (fun _ _ _ h => by cases h)) ((hprepR _ m' e).mp h2) h3
    · exact fastBlocked_mono hsafeM (c8' r y u (haO _ _ _ _ h1) u')
  refine ⟨⟨hwf, hmw, hrt, hntpa, hbal, hown, hop, hvf, hrr, hhi, hlbI,
    hagr, hdc, chosenSafe_of_safe _ hwf hbal hown hvf hsafe, hdcv, hwit, hac, hexec.1,
    hexec.2.1, hexec.2.2.1, hexec.2.2.2, hslots, hco, hcm, hpk, hsafe, hrepo⟩, ?_⟩
  have hlbv : ∀ r y w2 lb2, (S'.rep r).inst y = some w2 → w2.lb = some lb2 →
      (i = r ∧ x = y ∧ w' = w2 ∧ lbN = lb2) ∨
        ((S.rep r).inst y = some w2 ∧ ¬ (r = i ∧ y = x)) := by
    intro r y w2 lb2 h2 hl2
    rcases R1 r y w2 h2 with ⟨rfl, rfl, rfl⟩ | h
    · rw [W7] at hl2; cases hl2; exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
    · exact Or.inr h
  have hcntAcc : ∀ fr to y c, S'.cnt fr to (Msg.isAccAt y c) = S.cnt fr to (Msg.isAccAt y c) :=
    fun fr to y c => hcnt0 fr to _ rfl
  have hcntPAR : ∀ fr to y c, S'.cnt fr to (Msg.isPARat y c) = S.cnt fr to (Msg.isPARat y c) :=
    fun fr to y c => hcnt0 fr to _ rfl
  have hcntAR : ∀ fr to y c, S'.cnt fr to (Msg.isARat y c) = S.cnt fr to (Msg.isARat y c) :=
    fun fr to y c => hcnt0 fr to _ rfl
  have hint1 : ∀ to, (intendedOf B.norm to).length ≤ 1 := by
    intro to; unfold intendedOf; split
    · split <;> simp
    · simp
  have hPAat : ∀ y c, Msg.isPAat y c (.preAccept m) = true → x = y ∧ b = c := by
    intro y c hp
    simp only [Msg.isPAat, decide_eq_true_eq] at hp
    rw [m2, m7] at hp; exact ⟨hp.1, hp.2⟩
  have hnoV : ∀ r st u, isPA st → ¬ S.ev r (.vote x b st u) := hnovPA
  exact {
    stRange := fun r hr y w2 h2 => by
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · exact Or.inr (Or.inl (Or.inl W4))
      · exact hA.stRange r hr y w2 h
    cmdsSome := fun r hr y w2 h2 hs => by
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · rw [W1]; simp
      · exact hA.cmdsSome r hr y w2 h hs
    noneRec := fun r hr y w2 h2 hs => by
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, hne⟩
      · rw [W4] at hs; cases hs
      · obtain ⟨d1, d2⟩ := hA.noneRec r hr y w2 h hs
        exact ⟨d1, fun c st u hv0 => d2 c st u (hvO _ _ _ _ _ hv0 hne)⟩
    vbalNonneg := fun r hr y w2 h2 hs => by
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · rw [W3]; exact hb0
      · exact hA.vbalNonneg r hr y w2 h hs
    votesLe := fun r hr y w2 h2 c st u hv0 => by
      rcases R1 r y w2 h2 with ⟨rfl, rfl, rfl⟩ | ⟨h, hne⟩
      · rw [W3]
        rcases hvoteO _ _ c st u hv0 with h | ⟨-, -, rfl, -, -⟩
        · obtain ⟨w1, h1, hle⟩ := s5.2 _ hr _ c st u h
          rw [hw] at h1; cases h1; omega
        · exact Int.le_refl _
      · exact hA.votesLe r hr y w2 h c st u (hvO _ _ _ _ _ hv0 hne)
    recVote := fun r hr y w2 h2 hs => by
      rcases R1 r y w2 h2 with ⟨rfl, rfl, rfl⟩ | ⟨h, -⟩
      · rw [W3, W4, W9]; exact hH.ev_new (by simp)
      · exact hH.ev_old (hA.recVote r hr y w2 h hs)
    accKeep := fun r hr y w2 h2 c u hv0 hle => by
      rcases R1 r y w2 h2 with ⟨rfl, rfl, rfl⟩ | ⟨h, hne⟩
      · exfalso
        rcases hvoteO _ _ c _ u hv0 with h | ⟨-, -, -, h, -⟩
        · obtain ⟨w1, h1, hle'⟩ := s5.2 _ hr _ c _ u h
          rw [hw] at h1; cases h1; rw [W3] at hle
          have : c = b := zz_inj (by omega)
          subst this
          obtain ⟨l, hl⟩ := s8.2 _ _ _ u h
          exact hnoacc l u hl
        · cases h
      · exact hA.accKeep r hr y w2 h c u (hvO _ _ _ _ _ hv0 hne) hle
    recCommit := fun r hr y w2 h2 hs => by
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · exact absurd hs hnc'
      · obtain ⟨c, u, d1, d2⟩ := hA.recCommit r hr y w2 h hs
        exact ⟨c, u, hH.ev_old d1, d2⟩
    commitRec := fun r y c u hr he => by
      have h := hold _ _ he (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
        (fun _ _ _ h => by cases h)
      obtain ⟨w1, h1, hs⟩ := hA.commitRec r y c u hr h
      rcases R2 r y w1 h1 with ⟨-, -, rfl⟩ | h'
      · exact absurd hs hnc
      · exact ⟨w1, h', hs⟩
    fastCommitEv := fun r y u he => by
      obtain ⟨d1, c, d2⟩ := hA.fastCommitEv r y u
        (hold _ _ he (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
          (fun _ _ _ h => by cases h))
      exact ⟨d1, c, hH.ev_old d2⟩
    makerLb := fun r y c hr he => by
      obtain ⟨w1, lb1, h1, hl1, hle⟩ := hA.makerLb r y c hr
        (hold _ _ he (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
          (fun _ _ _ h => by cases h))
      rcases R2 r y w1 h1 with ⟨rfl, rfl, rfl⟩ | h
      · rw [hlb] at hl1; cases hl1; exact ⟨w', lbN, R3, W7, by rw [k1, ← hlt]; exact hle⟩
      · exact ⟨w1, lb1, h, hl1, hle⟩
    lastLeBal := fun r hr y w2 lb2 h2 hl2 => by
      rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, rfl, rfl⟩ | ⟨h, -⟩
      · rw [k1, W2]; exact Int.le_refl _
      · exact hA.lastLeBal r hr y w2 lb2 h hl2
    peerOk := fun r hr => by rw [(hfl r).2.1]; exact hA.peerOk r hr
    crtOwn := fun r hr q hq => by rw [(hfl r).2.2.1, (hfl q).2.2.1]; exact hA.crtOwn r hr q hq
    crtRec := fun r hr y w2 h2 => by
      rw [(hfl y.q).2.2.1]
      rcases R1 r y w2 h2 with ⟨rfl, rfl, -⟩ | ⟨h, -⟩
      · exact hA.crtRec _ hi _ w hw
      · exact hA.crtRec r hr y w2 h
    crtMsg := fun fr to m' y hm' hy => by
      rw [(hfl y.q).2.2.1]
      rcases (hmsgs _ _ _).mp hm' with hm' | ⟨hfi, rfl, -⟩
      · exact hA.crtMsg fr to m' y hm' hy
      · simp only [Msg.instOf, Option.some.injEq] at hy
        rw [m2] at hy; subst hy; exact hA.crtRec i hi x w hw
    crtEv := fun r e y he hy => by
      rw [(hfl y.q).2.2.1]
      rcases (hE r e).mp he with h | ⟨-, rfl | rfl | rfl⟩
      · exact hA.crtEv r e y h hy
      all_goals
        simp only [Event.instOf, Option.some.injEq] at hy; subst hy
        exact ⟨hxq, hA.crtRec i hi x w hw⟩
    ownRow := fun q hq j hj => by
      rw [(hfl q).2.2.1] at hj
      obtain ⟨w1, lb1, h1, hl1⟩ := hA.ownRow q hq j hj
      rcases R2 q _ w1 h1 with ⟨rfl, hx', rfl⟩ | h
      · exact ⟨w', lbN, by rw [← hx']; exact R3, W7⟩
      · exact ⟨w1, lb1, h, hl1⟩
    paNoAcc := fun r hr y w2 lb2 h2 hl2 hs u hv0 => by
      rcases hlbv r y w2 lb2 h2 hl2 with ⟨rfl, rfl, -, rfl⟩ | ⟨h, -⟩
      · rw [k1] at hv0; exact hnoacc _ u (haO _ _ _ _ hv0)
      · exact hA.paNoAcc r hr y w2 lb2 h hl2 hs u (haO _ _ _ _ hv0)
    paLeader := fun r hr y w2 lb2 h2 hl2 hs hp hc' hb' => by
      rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, rfl, rfl⟩ | ⟨h, hne⟩
      · rw [W3, k1, W4]; exact ⟨rfl, hPA⟩
      · obtain ⟨u, hu⟩ := hp
        exact hA.paLeader r hr y w2 lb2 h hl2 hs ⟨u, hpO _ _ _ _ hu hne⟩ hc' hb'
    prepNoProp := fun r hr y w2 lb2 h2 hl2 hp => by
      rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, -, rfl⟩ | ⟨h, hne⟩
      · rw [k4] at hp; cases hp
      · obtain ⟨d1, d2, d3, d4, d5⟩ := hA.prepNoProp r hr y w2 lb2 h hl2 hp
        exact ⟨d1, fun u h' => d2 u (hpO _ _ _ _ h' hne),
          fun u h' => d3 u (haO _ _ _ _ h'), d4, d5⟩
    paMsgOnce := fun fr to y c => by
      rw [hH.cnt_eq]
      split
      · rename_i hfr; subst fr
        by_cases hp : Msg.isPAat y c (.preAccept m) = true
        · obtain ⟨rfl, rfl⟩ := hPAat y c hp
          have h0 : S.cnt i to (Msg.isPAat x b) = 0 := by
            simp only [Sys.cnt, List.length_eq_zero_iff, List.filter_eq_nil_iff]
            intro m' hm' hp'
            cases m' with
            | preAccept a =>
              simp only [Msg.isPAat, decide_eq_true_eq] at hp'
              exact hnoPAmsg i to a hm' hp'.1 hp'.2
            | _ => simp [Msg.isPAat] at hp'
          rw [h0]; simp only [List.nil_append, Nat.zero_add]
          exact Nat.le_trans (List.length_filter_le _ _) (hint1 to)
        · simp only [List.nil_append]
          have : (intendedOf B.norm to).filter (Msg.isPAat y c) = [] := by
            simp only [List.filter_eq_nil_iff]
            intro m' hm'
            obtain ⟨h1, -⟩ := mem_intended_norm hm'
            rw [h1, hBm]; simpa using hp
          rw [this]; simpa using hA.paMsgOnce i to y c
      · simpa using hA.paMsgOnce fr to y c
    accMsgOnce := fun fr to y c => by rw [hcntAcc]; exact hA.accMsgOnce fr to y c
    paVoteDeliv := fun r y c st u hst hv0 => by
      rcases hvoteO r y c st u hv0 with h | ⟨rfl, rfl, rfl, -, -⟩
      · rcases hA.paVoteDeliv r y c st u hst h with ⟨u0, h0⟩ | h0
        · exact Or.inl ⟨u0, hH.ev_old h0⟩
        · refine Or.inr (fun fr' => ?_)
          by_cases hp : Msg.isPAat y c (.preAccept m) = true
          · obtain ⟨rfl, rfl⟩ := hPAat y c hp
            exact absurd h (hnoV r st u hst)
          · exact hallP _ _ _ (by simpa using hp) (h0 fr')
      · exact Or.inl ⟨⟨cmds, W32 (-1), deps⟩, hH.ev_new (by simp)⟩
    parOnce := fun a r y c h1 => by
      rw [hcntPAR] at h1 ⊢
      obtain ⟨d1, d2⟩ := hA.parOnce a r y c h1
      refine ⟨d1, ?_⟩
      by_cases hp : Msg.isPAat y c (.preAccept m) = true
      · obtain ⟨rfl, rfl⟩ := hPAat y c hp
        by_cases hri : r = i
        · exfalso; subst hri
          obtain ⟨n0, m0, hn0, hp0⟩ : ∃ n0 m0, (S.msgs a r)[n0]? = some m0 ∧
              Msg.isPARat x b m0 = true := by
            have : ((S.msgs a r).filter (Msg.isPARat x b)) ≠ [] := by
              intro h0; simp only [Sys.cnt, h0, List.length_nil] at h1; omega
            obtain ⟨m0, hm0⟩ := List.exists_mem_of_ne_nil _ this
            rw [List.mem_filter] at hm0
            obtain ⟨n0, hn0⟩ := List.mem_iff_getElem?.mp hm0.1
            exact ⟨n0, m0, hn0, hm0.2⟩
          cases m0 with
          | preAcceptReply ar =>
            simp only [Msg.isPARat, decide_eq_true_eq] at hp0
            exact noPAR a ar (List.mem_of_getElem? hn0) hp0.1 hp0.2
          | _ => simp [Msg.isPARat] at hp0
        · exact hH.allDeliv_old d2 (fun h => absurd h hri)
      · exact hallP _ _ _ (by simpa using hp) d2
    arFrom := fun a r m' hm' => by
      rcases (hmsgs _ _ _).mp hm' with hm' | ⟨-, h, -⟩
      · obtain ⟨c, u, d1, d2⟩ := hA.arFrom a r m' hm'
        exact ⟨c, u, d1, hH.ev_old d2⟩
      · cases h
    arOnce := fun a r y c h1 => by
      rw [hcntAR] at h1 ⊢
      rcases hA.arOnce a r y c h1 with ⟨w1, lb1, h1', hl1, hlt'⟩ | ⟨d1, d2⟩
      · refine Or.inl ?_
        rcases R2 r y w1 h1' with ⟨rfl, rfl, rfl⟩ | h
        · rw [hlb] at hl1; cases hl1; exact ⟨w', lbN, R3, W7, by rw [k1, ← hlt]; exact hlt'⟩
        · exact ⟨w1, lb1, h, hl1, hlt'⟩
      · exact Or.inr ⟨d1, hallP _ _ _ rfl d2⟩
    commitBal := fun fr to m' hm' => by
      rcases (hmsgs _ _ _).mp hm' with hm' | ⟨-, h, -⟩
      · exact hA.commitBal fr to m' hm'
      · cases h
    sentPR := fun r to m' he => by
      have he0 := hold _ _ he (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
        (fun _ _ _ h => by cases h)
      obtain ⟨d1, d2, d3⟩ := hA.sentPR r to m' he0
      refine ⟨fun hr => ?_, fun c st u hb' => ?_, fun to' m2 hb' hy => d3 to' m2 ?_ hy⟩
      · obtain ⟨w1, h1, hle⟩ := d1 hr
        rcases R2 r _ w1 h1 with ⟨rfl, hy, rfl⟩ | h
        · exact ⟨w', by rw [← hy]; exact R3, by rw [W2]; omega⟩
        · exact ⟨w1, h, hle⟩
      · obtain ⟨pp, pp', hlt', h1, h2⟩ := hb'
        rcases hvoteO r _ c st u (List.mem_of_getElem? h2) with h | ⟨rfl, hy, rfl, -, -⟩
        · exact d2 c st u (hevB _ _ _ _ ⟨pp, pp', hlt', h1, h2⟩ h (fun _ _ _ h => by cases h))
        · obtain ⟨w1, h1', hle⟩ := d1 hi
          rw [hy, hw] at h1'; cases h1'; omega
      · obtain ⟨pp, pp', hlt', h1, h2⟩ := hb'
        exact hevB _ _ _ _ ⟨pp, pp', hlt', h1, h2⟩
          (hold _ _ (List.mem_of_getElem? h2) (fun _ _ _ h => by cases h)
            (fun _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)) (fun _ _ _ h => by cases h)
    confCover := fun r hr e y cy he hrec c hc' => by
      rcases (hE r e).mp he with h | ⟨hri, rfl | rfl | rfl⟩
      · exact confLe_cover (hconfLe r) (hA.confCover r hr e y cy h hrec c hc')
      · cases hrec
      · cases hrec
      · simp only [Event.recorded, Option.some.injEq, Prod.mk.injEq] at hrec
        obtain ⟨rfl, rfl⟩ := hrec
        subst hri
        rw [hH.rep_self, hconf.2]
        obtain ⟨p, hp, h1, h2⟩ := uc_cov σb cmds x.q n seq c hc'
        have hz : (x.i : Int) = zz n := by rw [← hn.2]; exact toN_of_zz n hn.1
        exact ⟨p, hp, by rw [hz]; exact h1, fun h => by rw [hz]; exact h2 h⟩
    classWf := fun r hr => by
      have hgrow : ∀ y, (S.rep i).inst y ≠ none → σ'.inst y ≠ none := by
        intro y hy
        obtain ⟨w1, h1⟩ := Option.ne_none_iff_exists'.mp hy
        rcases R2 i y w1 h1 with ⟨-, rfl, -⟩ | h2
        · rw [← hH.rep_self, R3]; simp
        · rw [← hH.rep_self, h2]; simp
      by_cases hri : r = i
      · subst hri; rw [hH.rep_self]
        obtain ⟨h1, h2, h3, h4, h5⟩ := hcls
        have hb : AuxProof.ClsWf σb :=
          AuxProof.clsWf_keep (hA.classWf r hr) h1 h2 (fun y hy => by rw [h3]; exact hgrow y hy)
        have hu := ConfProof.clsWf_uc hb cmds x.q n seq (fun _ => by
          have : (⟨x.q, toN n⟩ : InstId) = x := by rw [hn.2]
          rw [this, h3, ← hH.rep_self, R3]; simp)
        exact AuxProof.clsWf_keep hu h4 h5 (fun y hy => by
          rw [ConfProof.uc_inst, h3] at hy; exact hy)
      · rw [hH.rep_other hri]; exact hA.classWf r hr
    classCover := fun r hr e y cy he hrec => by
      have hle : AuxProof.clsLe (S.rep r) (S'.rep r) := by
        by_cases h : r = i
        · subst h; rw [hH.rep_self]
          obtain ⟨h1, h2, -, h4, h5⟩ := hcls
          exact AuxProof.clsLe_trans (AuxProof.clsLe_of_eq h1 h2)
            (AuxProof.clsLe_trans (ConfProof.uc_clsLe σb cmds x.q n seq)
              (AuxProof.clsLe_of_eq h4 h5))
        · rw [hH.rep_other h]; exact AuxProof.clsLe_refl _
      rcases (hE r e).mp he with h | ⟨hri, rfl | rfl | rfl⟩
      · exact AuxProof.clsCov_mono hle (hA.classCover r hr e y cy h hrec)
      · cases hrec
      · cases hrec
      · simp only [Event.recorded, Option.some.injEq, Prod.mk.injEq] at hrec
        obtain ⟨rfl, rfl⟩ := hrec
        subst hri
        have hz : zz n = (x.i : Int) := by rw [← hn.2]; exact (toN_of_zz n hn.1).symm
        rw [hH.rep_self]; intro c hc'; rw [hcls.2.2.2.1, hcls.2.2.2.2]
        exact ConfProof.clsCov_uc σb cmds n seq x hz c hc'
    paAttrs := fun r y c st u hst hv0 => by
      rcases hvoteO r y c st u hv0 with h | ⟨rfl, rfl, rfl, -, rfl⟩
      · exact hH.ev_old (hA.paAttrs r y c st u hst h)
      · exact hH.ev_new (by simp)
    valOk := fun r y c u hv0 => by
      rw [hH.owner]
      rcases hv0 with hv0 | hv0
      · rcases hphO r y c u hv0 with h | ⟨-, rfl, rfl, rfl⟩
        · exact hA.valOk r y c u (Or.inl h)
        · exact hval
      · exact hA.valOk r y c u (Or.inr (haO _ _ _ _ hv0))
    cmdsNe := by
      obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hA.cmdsNe
      refine ⟨fun fr to m' hm' cs hcs => ?_,
        fun r hr y w2 cs h2 hc' => ?_, fun r hr y w2 lb2 cs h2 hl2 hc' => ?_,
        fun fr to m' hm' => ?_,
        fun r m' he => n5 r m' (hold _ _ he (fun _ _ _ h => by cases h)
          (fun _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)),
        fun r y c u hv0 => ?_⟩
      · rcases (hmsgs _ _ _).mp hm' with hm' | ⟨-, rfl, -⟩
        · exact n1 fr to m' hm' cs hcs
        · simp only [Msg.commandField, Option.some.injEq] at hcs
          subst hcs; rw [m8a]; exact hcne
      · rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
        · rw [W1] at hc'; cases hc'; exact hcne
        · exact n2 r hr y w2 cs h hc'
      · rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, -, rfl⟩ | ⟨h, -⟩
        · rw [k10] at hc'; cases hc'; exact hcne
        · exact n3 r hr y w2 lb2 cs h hl2 hc'
      · rcases (hmsgs _ _ _).mp hm' with hm' | ⟨-, h, -⟩
        · exact n4 fr to m' hm'
        · cases h
      · rcases hv0 with hv0 | hv0
        · rcases hphO r y c u hv0 with h | ⟨-, rfl, rfl, rfl⟩
          · exact n6 r y c u (Or.inl h)
          · exact hcne
        · exact n6 r y c u (Or.inr (haO _ _ _ _ hv0))
    prSent := fun fr to m' hm' => by
      rcases (hmsgs _ _ _).mp hm' with hm' | ⟨-, h, -⟩
      · exact hH.ev_old (hA.prSent fr to m' hm')
      · cases h
    selfOk := fun r m' he hs => hA.selfOk r m'
      (hold _ _ he (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
        (fun _ _ _ h => by cases h)) hs
    selfRaw := fun r m' he => hA.selfRaw r m'
      (hold _ _ he (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
        (fun _ _ _ h => by cases h))
    pm := by
      have hP := hA.pm
      have hmono : ∀ r e, S.ev r e → S'.ev r e := fun r e h => hH.ev_old h
      have hsent : ∀ fr to (m' : Msg), m' ∈ S.sent fr to → m' ∈ S'.sent fr to := by
        intro fr to m' h; rw [hH.sent]; exact h
      have hsm : ∀ fr to (m' : Msg), m' ∈ S.sent fr to → m' ∈ S.msgs fr to := by
        intro fr to m' h; unfold Sys.msgs
        exact List.mem_append_left _ (List.mem_append_left _ h)
      have hmsgO : ∀ fr to (m' : Msg), m' ∈ S'.msgs fr to → (∀ p, m' ≠ .preAccept p) →
          m' ∈ S.msgs fr to := by
        intro fr to m' h hn
        rcases (hmsgs _ _ _).mp h with h | ⟨-, rfl, -⟩
        · exact h
        · exact absurd rfl (hn m)
      have hPAR : ∀ a r (m' : PreAcceptReply), Msg.preAcceptReply m' ∈ S'.msgs a r →
          Msg.preAcceptReply m' ∈ S.msgs a r :=
        fun a r m' h => hmsgO _ _ _ h (fun _ h => by cases h)
      have hcv : ∀ y u, S.committedVal y u → S'.committedVal y u := fun y u h => (hcv' y u).mpr h
      have hbal : ∀ r y w1, (S.rep r).inst y = some w1 →
          ∃ w2, (S'.rep r).inst y = some w2 ∧ zz w1.bal ≤ zz w2.bal := by
        intro r y w1 h
        rcases R2 r y w1 h with ⟨rfl, rfl, rfl⟩ | h
        · exact ⟨w', R3, by rw [W2]; exact hb⟩
        · exact ⟨w1, h, Int.le_refl _⟩
      have hcm : ∀ r y c u, S'.ev r (.commit y c u) → S.ev r (.commit y c u) :=
        fun r y c u h => hold _ _ h (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
          (fun _ _ _ h => by cases h)
      have hsnd : ∀ (to : Nat) (m' : Msg), m' ∈ (fun _ => ([] : List Msg)) to → ∀ y, m'.isPAat y (initBal y) = false :=
        fun _ _ h => by cases h
      exact {
        arOk := PMProof.arOk_frame hP (fun a r m' h => hmsgO _ _ _ h (fun _ h => by cases h)) haO
          (fun q y c v h => by
            rcases hvoteO q y c _ v h with h | ⟨-, -, -, h, -⟩
            · exact Or.inl h
            · exact absurd (h ▸ hPA) hnotACC)
          hmono hcv hbal
        commitProp := PMProof.commitProp_frame hP hcm hmono
        commitMsgProp := PMProof.commitMsgProp_frame hP
          (fun fr to m' h => hmsgO _ _ _ h (fun _ h => by cases h)) hmono
        lbProp := fun r hr y w2 lb2 h2 hl2 hs hv => by
          rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, -, rfl⟩ | ⟨h, -⟩
          · rw [k3] at hs; exact absurd (hs ▸ hPA) hnotACC
          · obtain ⟨v, hv⟩ := hv
            exact PMProof.propAt_mono hmono
              (hP.lbProp r hr y w2 lb2 h hl2 hs ⟨v, haO _ _ _ _ hv⟩)
        parCom := PMProof.parCom_frame hP hPAR hmono
        parSt := PMProof.parSt_frame hP hPAR hsent
        paFresh := fun r hr y w2 lb2 h2 hl2 hs h0 hp => by
          rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, -, rfl⟩ | ⟨h, hne⟩
          · rw [k2]; decide
          · obtain ⟨v, hv⟩ := hp
            exact hP.paFresh r hr y w2 lb2 h hl2 hs h0 ⟨v, hpO _ _ _ _ hv hne⟩
        paCmds := fun r hr y w2 lb2 h2 hl2 hs v hv => by
          rcases hlbv r y w2 lb2 h2 hl2 with ⟨h1, h2', -, rfl⟩ | ⟨h, hne⟩
          · rw [k1] at hv
            rcases (hE r _).mp hv with h | ⟨-, h | h | h⟩
            · rw [← h2'] at h; exact absurd h (hnoph r v)
            · rw [← h2'] at h; simp only [Event.phase1.injEq] at h; obtain ⟨-, -, rfl⟩ := h
              rw [k10]
            · cases h
            · cases h
          · exact hP.paCmds r hr y w2 lb2 h hl2 hs v (hpO _ _ _ _ hv hne)
        paSent := fun y w2 lb2 hq h2 hl2 hlt' => by
          rcases hlbv _ y w2 lb2 h2 hl2 with ⟨-, rfl, -, rfl⟩ | ⟨h, hne⟩
          · rw [k1] at hlt'; exact absurd hlt' hbI
          · obtain ⟨g1, g2, g3⟩ := hP.paSent y w2 lb2 hq h hl2 hlt'
            refine ⟨g1, fun B' hB' hBx' ht => ?_,
              Nat.le_trans (pm_paRcpt_le hH hidle.1 hsnd y) g3⟩
            rw [hH.pending] at hB'
            by_cases hyq : y.q = i
            · rw [hyq, upd_same] at hB'
              obtain ⟨rfl, -, -⟩ := norm_some hB'
              exact absurd ⟨hyq, by rw [← hBx', hBx]⟩ hne
            · rw [upd_other _ _ _ _ hyq] at hB'; exact g2 B' hB' hBx' ht
        pendPA := fun r B' hB' y c hc => by
          rw [hH.pending] at hB'
          by_cases hr : r = i
          · subst hr; rw [upd_same] at hB'
            obtain ⟨rfl, -, -⟩ := norm_some hB'
            rw [hBm] at hc
            obtain ⟨rfl, -⟩ := hPAat y c hc
            exact ⟨htr, hBx⟩
          · rw [upd_other _ _ _ _ hr] at hB'; exact hP.pendPA r B' hB' y c hc
        paVoteMsg := fun r y st v hst hne hv => by
          rcases hvoteO r y _ st v hv with h | ⟨-, rfl, hc, -, -⟩
          · obtain ⟨p, h1, h2, h3⟩ := hP.paVoteMsg r y st v hst hne h
            exact ⟨p, hsent _ _ _ h1, h2, h3⟩
          · exact absurd hc.symm hbI
        parNoPA := fun a r m' hm' hn st u hst hv => by
          have hm0 := hPAR _ _ _ hm'
          rcases hvoteO a _ _ st u hv with h | ⟨rfl, hy, hc, -, -⟩
          · exact hP.parNoPA a r m' hm0 hn st u hst h
          · obtain ⟨-, -, -, p, hp, hpx, hpb⟩ := hP.parSt _ r m' hm0
            exact hnoPAmsg r _ p (hsm _ _ _ hp) (by rw [hpx, hy]) (by rw [hpb, hc])
        aeF := fun r hr y w2 lb2 h2 hl2 hs hae' => by
          rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, -, rfl⟩ | ⟨h, -⟩
          · rw [hae] at hae'; cases hae'
          · obtain ⟨a, a', m1, m1', g1, g2, g3, g4, g5, g6, g7⟩ :=
              hP.aeF r hr y w2 lb2 h hl2 hs hae'
            exact ⟨a, a', m1, m1', hsent _ _ _ g1, hsent _ _ _ g2, g3, g4, g5, g6, g7⟩
        repLead := PMProof.repLead_frame hP (fun r m' e h => (hprepR r m' e).mp h) hbal
        paGe := fun r y c st v ℓ v0 hst h1 h2 => by
          rcases hvoteO r y c st v h1 with h1 | ⟨-, rfl, rfl, -, rfl⟩
          · rcases hphO ℓ y c v0 h2 with h2 | ⟨-, rfl, rfl, -⟩
            · exact hP.paGe r y c st v ℓ v0 hst h1 h2
            · exact absurd h1 (hnovPA r st v hst)
          · rcases hphO ℓ _ _ v0 h2 with h2 | ⟨-, -, -, rfl⟩
            · exact absurd h2 (hnoph ℓ v0)
            · exact ⟨hdeps.1, hdeps.1, fun q _ => Int.le_refl _⟩
        phAttrs := fun ℓ y c v0 h => by
          rcases hphO ℓ y c v0 h with h | ⟨rfl, rfl, -, rfl⟩
          · exact hmono _ _ (hP.phAttrs ℓ y c v0 h)
          · exact hH.ev_new (by simp)
        accWit := PMProof.accWit_frame hP haO hmono hcv
        accVote := PMProof.accVote_frame hP haO hmono
        cmdSafe := CmdSafeProof.cmdSafe_step hP hsafeM (fun r y c u h => by
          rcases hphO r y c u h with h | ⟨rfl, rfl, rfl, rfl⟩
          · exact Or.inl h
          · exact Or.inr ⟨⟨stPREACCEPTED, ⟨cmds, seq, deps⟩, Or.inl rfl, hH.ev_new (by simp), rfl⟩, hcmdS⟩)
        accSup := CmdSafeProof.accSup_frame hP hmono haO },
    ownerCrt := fun y ps h => by
      rw [hH.owner] at h; rw [(hfl y.q).2.2.1]; exact hA.ownerCrt y ps h
    execLo := AuxProof.execLo_of_eq hA.execLo (fun r _ => (hfl r).2.2.2.1)
    exec := ExecOrd.invExec_hs hS.1 hA.exec hH hidle hagr hchan (fun r y h => by rw [hrep, if_neg]; rintro ⟨h1, h2⟩; rcases h with h | h; exact h h1; exact h h2) R3
      (fun w0 h0 hs => by rw [hw] at h0; cases h0; exact absurd hs hwnex)
      (fun lb2 hl hne => ⟨w, lb, hw, hlb, by rw [W7] at hl; cases hl; rw [k6] at hne; exact hne⟩) }

/-! ## `startPhase1`'s result -/

/-- The bookkeeping `startPhase1` writes. -/
def sp1Lb (cmds : List WCmd) (b : w32) (deps : List w32) (ps : Option (List Proposal)) : LbRec :=
  { clientProposals := ps, ballot := W32 (-1), allEqual := true,
    preAcceptOKs := W64 0, acceptOKs := W64 0, nacks := W64 0, prepareReplies := [],
    preparing := false, tryingToPreAccept := false, lastTriedBallot := b,
    cmds := some cmds, status := stPREACCEPTED, seq := W32 (-1), deps := deps,
    leaderResponded := false, preAcceptsSent := W64 0 }

theorem sp1_spec (σ : RState) (cmds : List WCmd) (x : InstId) (r n b : w32)
    (ps : Option (List Proposal)) :
    (startPhase1 σ cmds x r n b ps).1.inst = upd σ.inst x (some (p1Rec x cmds b
      (updateAttributes σ cmds (W32 0) (List.replicate nR (W32 (-1)))).1
      (updateAttributes σ cmds (W32 0) (List.replicate nR (W32 (-1)))).2.1
      (sp1Lb cmds b (updateAttributes σ cmds (W32 0) (List.replicate nR (W32 (-1)))).2.1 ps))) ∧
    (startPhase1 σ cmds x r n b ps).1.id = σ.id ∧
    (startPhase1 σ cmds x r n b ps).1.peerOrder = σ.peerOrder ∧
    (startPhase1 σ cmds x r n b ps).1.crtInstance = σ.crtInstance ∧
    (startPhase1 σ cmds x r n b ps).1.execedUpTo = σ.execedUpTo ∧
    (startPhase1 σ cmds x r n b ps).1.store = σ.store ∧
    (startPhase1 σ cmds x r n b ps).1.conflicts = (updateConflicts (σ.setInst x (p1Rec x cmds b
      (updateAttributes σ cmds (W32 0) (List.replicate nR (W32 (-1)))).1
      (updateAttributes σ cmds (W32 0) (List.replicate nR (W32 (-1)))).2.1
      (sp1Lb cmds b (updateAttributes σ cmds (W32 0) (List.replicate nR (W32 (-1)))).2.1 ps)))
      cmds x.q n (updateAttributes σ cmds (W32 0) (List.replicate nR (W32 (-1)))).1).conflicts ∧
    (startPhase1 σ cmds x r n b ps).2 =
      [Out.ev (.phase1 x b ⟨cmds, W32 (-1),
          (updateAttributes σ cmds (W32 0) (List.replicate nR (W32 (-1)))).2.1⟩),
       Out.ev (.vote x b stPREACCEPTED ⟨cmds,
          (updateAttributes σ cmds (W32 0) (List.replicate nR (W32 (-1)))).1,
          (updateAttributes σ cmds (W32 0) (List.replicate nR (W32 (-1)))).2.1⟩),
       Out.ev (.attrsRec x cmds (updateAttributes σ cmds (W32 0) (List.replicate nR (W32 (-1)))).2.1),
       Out.bcast (bcastPreAcceptOf (startPhase1 σ cmds x r n b ps).1 x
         (preAcceptOf (startPhase1 σ cmds x r n b ps).1 r n
           (sp1Lb cmds b (updateAttributes σ cmds (W32 0) (List.replicate nR (W32 (-1)))).2.1 ps)))] := by
  have hu := CommitProof.uc_fields
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;> unfold startPhase1 <;> dsimp only <;>
    split <;> simp [hu, RState.setInst, p1Rec, sp1Lb]

/-- (stage 2) `startPhase1`'s class arrays: `updateConflicts`' over the state with the record set. -/
theorem sp1_cls (σ : RState) (cmds : List WCmd) (x : InstId) (r n b : w32)
    (ps : Option (List Proposal)) :
    (startPhase1 σ cmds x r n b ps).1.lastScan = (updateConflicts (σ.setInst x (p1Rec x cmds b
      (updateAttributes σ cmds (W32 0) (List.replicate nR (W32 (-1)))).1
      (updateAttributes σ cmds (W32 0) (List.replicate nR (W32 (-1)))).2.1
      (sp1Lb cmds b (updateAttributes σ cmds (W32 0) (List.replicate nR (W32 (-1)))).2.1 ps)))
      cmds x.q n (updateAttributes σ cmds (W32 0) (List.replicate nR (W32 (-1)))).1).lastScan ∧
    (startPhase1 σ cmds x r n b ps).1.lastPut = (updateConflicts (σ.setInst x (p1Rec x cmds b
      (updateAttributes σ cmds (W32 0) (List.replicate nR (W32 (-1)))).1
      (updateAttributes σ cmds (W32 0) (List.replicate nR (W32 (-1)))).2.1
      (sp1Lb cmds b (updateAttributes σ cmds (W32 0) (List.replicate nR (W32 (-1)))).2.1 ps)))
      cmds x.q n (updateAttributes σ cmds (W32 0) (List.replicate nR (W32 (-1)))).1).lastPut := by
  refine ⟨?_, ?_⟩ <;> unfold startPhase1 <;> dsimp only <;>
    split <;> simp [RState.setInst, p1Rec, sp1Lb]

end RecPhase1Proof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
