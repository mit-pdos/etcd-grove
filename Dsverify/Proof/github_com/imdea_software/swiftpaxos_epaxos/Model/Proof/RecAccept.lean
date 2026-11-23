/-
A handler step of replica `i` that starts the accept phase of its instance `x` at its ballot `b`
with value `v`: the record becomes ACCEPTED with `v` at `b` (its own vote), the bookkeeping becomes
an ACCEPTED, non-preparing one at `b`, the events `vote x b ACCEPTED v` and `accept x b v` are
logged and the Accept broadcast is left pending (`inv_accept_start`). Used by
`handlePrepareReply`'s sub-cases 2 and 3 (and planned for `handlePreAcceptReply`'s slow path).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.RecCommit

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace RecAcceptProof

open HStepProof HLocal SafeProof AuxProof RecCommitProof

/-- The accepted record. -/
def accKnown (w : InstRec) (lb' : LbRec) (b : w32) (v : Val) : InstRec :=
  { w with cmds := some v.cmds, bal := b, vbal := b, seq := v.seq, deps := v.deps,
           status := stACCEPTED, lb := some lb' }

/-- The bookkeeping after the accept phase started (its counted replies are given in `S'`
terms by the caller). -/
def LbAccepted (lb lb' : LbRec) (v : Val) : Prop :=
  lb'.lastTriedBallot = lb.lastTriedBallot ∧ zz lb'.ballot ≤ zz lb.lastTriedBallot ∧
  lb'.status = stACCEPTED ∧ lb'.preparing = false ∧ lb'.tryingToPreAccept = false ∧
  lb'.clientProposals = lb.clientProposals ∧ depsOk lb'.deps ∧ lb'.cmds = some v.cmds ∧
  lb'.seq = v.seq ∧ lb'.deps = v.deps

theorem norm_some {B B' : Bcast} (h : B.norm = some B') :
    B' = B ∧ B.peers ≠ [] ∧ B.sent < B.need := by
  unfold Bcast.norm at h
  split at h
  · cases h
  · rename_i hc; cases h; refine ⟨rfl, fun h' => hc (Or.inl h'), ?_⟩
    have : ¬ B.need ≤ B.sent := fun h' => hc (Or.inr h'); omega

theorem mem_intended_norm {B : Bcast} {to : Nat} {m : Msg} (h : m ∈ intendedOf B.norm to) :
    m = B.m ∧ to ∈ B.peers := by
  unfold intendedOf at h
  split at h
  · rename_i B' hB
    obtain ⟨rfl, -⟩ := norm_some hB
    split at h
    · simp only [List.mem_singleton] at h; exact ⟨h, by assumption⟩
    · cases h
  · cases h

/-- **Starting the accept phase keeps the invariant.** -/
theorem inv_accept_start (S S' : Sys) (i : Nat) (σ' : RState) (x : InstId) (w : InstRec)
    (lb lb' : LbRec) (b : w32) (v : Val) (B : Bcast) (m : Accept) (hS : Inv S) (hi : i < nR)
    (hidle : S.idle i)
    (hH : HS S S' i σ' [.vote x b stACCEPTED v, .accept x b v] (fun _ => []) B.norm)
    (hchan : S'.proposeChan = S.proposeChan)
    (hB : B.x = x ∧ B.m = .accept m ∧ B.peers = (S.rep i).peerOrder.take (nR - 1) ∧
      B.need = nR / 2 ∧ B.sent = 0 ∧ B.trackPA = false)
    (hmm : m.leaderId = W32 i ∧ (⟨toN m.replica, toN m.inst⟩ : InstId) = x ∧ 0 ≤ zz m.replica ∧
      zz m.replica < nR ∧ 0 ≤ zz m.inst ∧ toN m.inst + 1 < MAX_INSTANCE ∧ m.ballot = b ∧
      (⟨m.command, m.seq, m.deps⟩ : Val) = v)
    (hσ : σ'.inst = upd (S.rep i).inst x (some (accKnown w lb' b v)))
    (hc : σ'.id = (S.rep i).id ∧ σ'.peerOrder = (S.rep i).peerOrder ∧
      σ'.crtInstance = (S.rep i).crtInstance ∧ σ'.conflicts = (S.rep i).conflicts ∧
      σ'.execedUpTo = (S.rep i).execedUpTo ∧ σ'.store = (S.rep i).store)
    (hcls : σ'.lastScan = (S.rep i).lastScan ∧ σ'.lastPut = (S.rep i).lastPut)
    (hw : (S.rep i).inst x = some w) (hlb : w.lb = some lb) (hnc : ¬ isCommitted w.status)
    (hb : zz w.bal ≤ zz b) (hlt : lb.lastTriedBallot = b) (hb0 : 0 ≤ zz b)
    (hnoacc : ∀ r u, ¬ S.ev r (.accept x b u))
    (hph : ∀ r u, S.ev r (.phase1 x b u) → v.cmds = u.cmds)
    (hsafeA : S.safeAcc x b v)
    (hinit : b = initBal x → ∀ u, S'.fastBlocked x u)
    (hdeps : depsOk v.deps) (hcne : v.cmds ≠ [])
    (hval : v.cmds = noop ∨ ∃ ps, S.owner x = some ps ∧ v.cmds = ps.map (·.cmd))
    (hk : LbAccepted lb lb' v)
    (hQ : (∃ Q : List (Nat × PreAcceptReply), (Q.map (·.1)).Nodup ∧
      Q.length = lb'.preAcceptOKs.toNat ∧
      ∀ a m, (a, m) ∈ Q → a < nR ∧ a ≠ i ∧ S'.deliveredMsg a i (.preAcceptReply m) ∧
        (Msg.preAcceptReply m).instOf = some x ∧ m.ballot = lb'.lastTriedBallot) ∧
      (∃ Q : List Nat, Q.Nodup ∧ Q.length = lb'.acceptOKs.toNat ∧
      ∀ a ∈ Q, a < nR ∧ a ≠ i ∧ ∃ m : AcceptReply, S'.deliveredMsg a i (.acceptReply m) ∧
        (Msg.acceptReply m).instOf = some x ∧ m.ballot = lb'.lastTriedBallot))
    (hlbP : lb'.ballot = b ∨ S.propAt x lb'.ballot v.cmds)
    (hpas : lb'.preAcceptsSent = lb.preAcceptsSent)
    (hwit : v.cmds ≠ noop → S.witnessed x v ∨ ∃ u, S.committedVal x u)
    (hsup : (∃ r' b' u, S.ev r' (.commit x b' u)) ∨
      ∃ c0, realBal x c0 ∧ zz c0 ≤ zz b ∧ S.cmdChosen x c0 v.cmds) :
    Inv S' := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hc
  obtain ⟨k1, k2, k3, k4, k5, k6, k9, k10, k11, k12⟩ := hk
  obtain ⟨hBx, hBm, hBp, hBn, hBs, hBt⟩ := hB
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8⟩ := hmm
  generalize hw'd : accKnown w lb' b v = w' at hσ
  have hA := hS.2
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19,
    s20, s21, s22, s23, s24, s25, s26, s27⟩ := hS.1
  have hxq : x.q < nR := (s1.2.1 i hi x w hw).2.1
  -- events
  have hE : ∀ r e, S'.ev r e ↔ S.ev r e ∨
      (r = i ∧ (e = .vote x b stACCEPTED v ∨ e = .accept x b v)) := by
    intro r e; rw [hH.ev_iff]; simp
  have hold : ∀ r e, S'.ev r e → (∀ y c st u, e ≠ .vote y c st u) → (∀ y c u, e ≠ .accept y c u) →
      S.ev r e := by
    intro r e he h1 h2
    rcases (hE r e).mp he with h | ⟨-, rfl | rfl⟩
    · exact h
    · exact absurd rfl (h1 _ _ _ _)
    · exact absurd rfl (h2 _ _ _)
  have hnotE : ∀ e, (∀ y c st u, e ≠ .vote y c st u) → (∀ y c u, e ≠ .accept y c u) →
      i = i → e ∉ [Event.vote x b stACCEPTED v, .accept x b v] := by
    intro e h1 h2 _ h
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
    rcases h with h | h
    · exact h1 _ _ _ _ h
    · exact h2 _ _ _ h
  -- messages
  have hmsgs : ∀ fr to m', m' ∈ S'.msgs fr to ↔ m' ∈ S.msgs fr to ∨
      (fr = i ∧ m' = .accept m ∧ to ∈ (S.rep i).peerOrder.take (nR - 1)) := by
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
          · rw [hBn, hBs] at h; simp [nR] at h
        rw [hne]; simp only [intendedOf]; rw [hBp, if_pos hto, hBm]; simp
  have hvoteO : ∀ r y c st u, S'.ev r (.vote y c st u) → S.ev r (.vote y c st u) ∨
      (r = i ∧ y = x ∧ c = b ∧ st = stACCEPTED ∧ u = v) := by
    intro r y c st u h
    rcases (hE r _).mp h with h | ⟨hr, h | h⟩
    · exact Or.inl h
    · simp only [Event.vote.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact Or.inr ⟨hr, rfl, rfl, rfl, rfl⟩
    · cases h
  have haccO : ∀ r y c u, S'.ev r (.accept y c u) → S.ev r (.accept y c u) ∨
      (r = i ∧ y = x ∧ c = b ∧ u = v) := by
    intro r y c u h
    rcases (hE r _).mp h with h | ⟨hr, h | h⟩
    · exact Or.inl h
    · cases h
    · simp only [Event.accept.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr ⟨hr, rfl, rfl, rfl⟩
  have hnoaccMsg : ∀ fr to (m' : Accept), Msg.accept m' ∈ S.msgs fr to →
      (⟨toN m'.replica, toN m'.inst⟩ : InstId) = x → m'.ballot ≠ b := by
    intro fr to m' hm' hx hb'
    have := (s6.2.2.2.2.2 fr to m' hm').2
    rw [hx, hb'] at this; exact hnoacc _ _ this
  have hlbX := s11 i hi x w lb hw hlb
  have noAR : ∀ a (m' : AcceptReply), Msg.acceptReply m' ∈ S.msgs a i →
      (⟨toN m'.replica, toN m'.inst⟩ : InstId) = x → m'.ballot ≠ b := by
    intro a m' hm' hx hb'
    obtain ⟨b', u, hle, hev⟩ := hA.arFrom a i m' hm'
    rw [hx] at hev
    have h2 := hlbX.2.2.2.1 b' u (Or.inr hev)
    rw [hlt, ← hb'] at h2
    have : b' = m'.ballot := zz_inj (by omega)
    rw [this, hb'] at hev; exact hnoacc _ _ hev
  have hprepR : ∀ r m' e, S'.prepReport r m' e ↔ S.prepReport r m' e := by
    intro r m' e
    constructor
    · rintro ⟨he, ⟨to, hm', rfl⟩ | rfl⟩
      · refine ⟨hold r _ he (fun _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h),
          Or.inl ⟨to, ?_, rfl⟩⟩
        rcases (hmsgs _ _ _).mp hm' with h | ⟨-, h, -⟩
        · exact h
        · cases h
      · exact ⟨hold r _ he (fun _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h), Or.inr rfl⟩
    · rintro ⟨he, ⟨to, hm', rfl⟩ | rfl⟩
      · exact ⟨hH.ev_old he, Or.inl ⟨to, hH.msgs_old hm', rfl⟩⟩
      · exact ⟨hH.ev_old he, Or.inr rfl⟩
  have hcv' : ∀ y u, S'.committedVal y u ↔ S.committedVal y u := by
    intro y u
    constructor
    · rintro (⟨r, b', h⟩ | ⟨fr, to, m', hm', hy, rfl⟩)
      · exact Or.inl ⟨r, b', hold r _ h (fun _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)⟩
      · rcases (hmsgs _ _ _).mp hm' with h | ⟨-, h, -⟩
        · exact Or.inr ⟨fr, to, m', h, hy, rfl⟩
        · cases h
    · rintro (⟨r, b', h⟩ | ⟨fr, to, m', hm', hy, rfl⟩)
      · exact Or.inl ⟨r, b', hH.ev_old h⟩
      · exact Or.inr ⟨fr, to, m', hH.msgs_old hm', hy, rfl⟩
  have hnoV : ∀ r, ¬ S.ev r (.vote x b stACCEPTED v) := by
    intro r h; obtain ⟨l, hl⟩ := s8.2 r x b v h; exact hnoacc l v hl
  have hnotEold : ∀ r e, S.ev r e → r = i → e ∉ [Event.vote x b stACCEPTED v, .accept x b v] := by
    intro r e he hr h
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact hnoV r he
    · exact hnoacc r v he
  have hevB : ∀ r e r' e', S'.evBefore r e r' e' → S.ev r' e' → S.evBefore r e r' e' :=
    fun r e r' e' h h' => hH.evBefore_back h h' (hnotEold r' e' h')
  have hcnt0 : ∀ fr to (p : Msg → Bool), p (.accept m) = false → S'.cnt fr to p = S.cnt fr to p := by
    intro fr to p hp
    rw [hH.cnt_eq]
    split
    · simp only [List.nil_append, Nat.add_eq_left, List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro m' hm'
      obtain ⟨h1, -⟩ := mem_intended_norm hm'
      rw [h1, hBm, hp]; simp
    · rfl
  have hallP : ∀ fr to (p : Msg → Bool), p (.accept m) = false → S.allDeliv fr to p →
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
  have hfl : ∀ r, (S'.rep r).id = (S.rep r).id ∧ (S'.rep r).peerOrder = (S.rep r).peerOrder ∧
      (S'.rep r).crtInstance = (S.rep r).crtInstance ∧
      (S'.rep r).conflicts = (S.rep r).conflicts ∧
      (S'.rep r).execedUpTo = (S.rep r).execedUpTo ∧ (S'.rep r).store = (S.rep r).store := by
    intro r
    by_cases hr : r = i
    · subst hr; rw [hH.rep_self]; exact ⟨c1, c2, c3, c4, c5, c6⟩
    · rw [hH.rep_other hr]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have W : w'.cmds = some v.cmds ∧ w'.bal = b ∧ w'.vbal = b ∧ w'.status = stACCEPTED ∧
      w'.seq = v.seq ∧ w'.deps = v.deps ∧ w'.lb = some lb' ∧ w'.id = w.id ∧
      instVal w' = v := by
    rw [← hw'd]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [instVal, accKnown]⟩
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
  -- votes and proposals at the instance of another record are old
  have hvO : ∀ r y c st u, S'.ev r (.vote y c st u) → ¬ (r = i ∧ y = x) →
      S.ev r (.vote y c st u) := by
    intro r y c st u h hne
    rcases hvoteO r y c st u h with h | ⟨h1, h2, -⟩
    · exact h
    · exact absurd ⟨h1, h2⟩ hne
  have haO : ∀ r y c u, S'.ev r (.accept y c u) → ¬ (r = i ∧ y = x) → S.ev r (.accept y c u) := by
    intro r y c u h hne
    rcases haccO r y c u h with h | ⟨h1, h2, -⟩
    · exact h
    · exact absurd ⟨h1, h2⟩ hne
  have hpO : ∀ r y c u, S'.ev r (.phase1 y c u) → S.ev r (.phase1 y c u) :=
    fun r y c u h => hold r _ h (fun _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
  have hvoteNew : NewVote S i x b stACCEPTED v := by
    refine ⟨fun w0 h0 => ?_, fun h => absurd h (by rintro (h | h) <;> cases h),
      fun h => absurd h (by rintro (h | h) <;> cases h)⟩
    rw [hw] at h0; cases h0
    exact ⟨hb, fun h => absurd h (by rintro (h | h) <;> cases h)⟩
  have hsafeM : SafeMono S S' := by
    refine ⟨fun r y w1 h1 => ?_, fun r e h => hH.ev_old h,
      fun r y c st u h => ?_,
      fun y u h => Or.inl (hold _ _ h (fun _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)),
      fun a y m' h hy hb' => ?_⟩
    · rcases R2 r y w1 h1 with ⟨rfl, rfl, rfl⟩ | h
      · exact ⟨w', R3, by rw [W2]; exact hb, fun _ => Or.inl (by rw [W4]; decide)⟩
      · exact ⟨w1, h, Int.le_refl _, fun h => Or.inl h⟩
    · rcases hvoteO r y c st u h with h | ⟨rfl, rfl, rfl, rfl, rfl⟩
      · exact Or.inl h
      · exact Or.inr hvoteNew
    · rcases (hmsgs _ _ _).mp h with h | ⟨-, h, -⟩
      · exact Or.inl h
      · cases h
  have hsafe : Inv.safe S' := by
    refine safe_step hsafeM s26 (fun r y c u h => ?_) (fun r y c u h => Or.inl (hpO r y c u h))
    rcases haccO r y c u h with h | ⟨-, rfl, rfl, rfl⟩
    · exact Or.inl h
    · exact Or.inr (safeAcc_mono hsafeM hsafeA)
  have hpeer := hA.peerOk i hi
  have hwf : Inv.wf S' := by
    obtain ⟨w1', w2', w3', w4', w5', w6', w7', w8'⟩ := s1
    refine ⟨fun r hr => by rw [(hfl r).1]; exact w1' r hr, fun r hr y w2 h2 => ?_,
      fun r hr q hq => by rw [(hfl r).2.2.1]; exact w3' r hr q hq,
      fun r hr q k p hk => ?_, fun r hr q hq n' hn' => ?_, fun fr' to hne => ?_,
      fun fr' to n' hn' => ?_, fun r b' hb' => ?_⟩
    · rcases R1 r y w2 h2 with ⟨rfl, rfl, rfl⟩ | ⟨h, -⟩
      · obtain ⟨g1, g2, g3, -, -, g6, g7⟩ := w2' i hi x w hw
        refine ⟨by rw [W8]; exact g1, g2, g3, fun _ => by rw [W6]; exact hdeps,
          fun lb2 hl2 _ => ?_, fun hq => by rw [W7]; simp, fun lb2 ps hl2 hps => ?_⟩
        · rw [W7] at hl2; cases hl2; exact k9
        · rw [W7] at hl2; cases hl2; rw [hH.owner]; rw [k6] at hps; exact g7 lb ps hlb hps
      · obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := w2' r hr y w2 h
        exact ⟨g1, g2, g3, g4, g5, g6, fun lb ps hlb hps => by rw [hH.owner]; exact g7 lb ps hlb hps⟩
    · rw [(hfl r).2.2.2.1] at hk
      obtain ⟨k1', k2', k3'⟩ := w4' r hr q k p hk
      have grow : ∀ y, (S.rep r).inst y ≠ none → (S'.rep r).inst y ≠ none := by
        intro y hy hy'
        obtain ⟨w1, h1⟩ := Option.ne_none_iff_exists'.mp hy
        rcases R2 r y w1 h1 with ⟨rfl, rfl, -⟩ | h
        · rw [R3] at hy'; cases hy'
        · rw [h] at hy'; cases hy'
      exact ⟨k1', fun h0 => grow _ (k2' h0), fun h0 => grow _ (k3' h0)⟩
    · rw [(hfl r).2.2.2.2.1] at hn'
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
          fun q hq => by rw [hBp] at hq; exact hpeer.2 q hq, w', lb', by rw [hBx]; exact R3, W7⟩
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
  have hown : Inv.ballotOwner S' := by
    obtain ⟨o1, o2, o3, o4, o5, o6⟩ := s6
    refine ⟨fun r y c he => ?_, fun r y c u he => ?_, fun r y c u he => ?_,
      fun r to m' hm' => ?_, fun r to m' hm' => ?_, fun r to m' hm' => ?_⟩
    · have h := hold r _ he (fun _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      refine ⟨(o1 r y c h).1, ?_⟩
      rw [hH.count_eq (fun _ => hnotE _ (fun _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h) rfl)]
      exact (o1 r y c h).2
    · exact hH.evBefore_old (o2 r y c u (hpO r y c u he))
    · rcases haccO r y c u he with h | ⟨rfl, rfl, rfl, rfl⟩
      · exact hH.ev_old (o3 r y c u h)
      · exact hH.ev_old (by rw [← hlt]; exact hlbX.1)
    · rcases (hmsgs _ _ _).mp hm' with h | ⟨-, h, -⟩
      · obtain ⟨d1, d2⟩ := o4 r to m' h; exact ⟨d1, hH.ev_old d2⟩
      · cases h
    · rcases (hmsgs _ _ _).mp hm' with h | ⟨-, h, -⟩
      · obtain ⟨d1, d2⟩ := o5 r to m' h; exact ⟨d1, hH.ev_old d2⟩
      · cases h
    · rcases (hmsgs _ _ _).mp hm' with h | ⟨rfl, h, -⟩
      · obtain ⟨d1, d2⟩ := o6 r to m' h; exact ⟨d1, hH.ev_old d2⟩
      · cases h
        refine ⟨m1, hH.ev_new ?_⟩
        rw [m2, m7, m8]; simp
  have hop : Inv.oneProposal S' := by
    obtain ⟨p1, p2, p3⟩ := s7
    refine ⟨fun r r' y c u u' he he' => ?_, fun r r' y c u u' he he' => ?_,
      fun r r' y c u u' he he' => ?_⟩
    · obtain ⟨d1, d2, d3⟩ := p1 r r' y c u u' (hpO _ _ _ _ he) (hpO _ _ _ _ he')
      refine ⟨d1, d2, ?_⟩
      rw [hH.count_eq (fun _ => hnotE _ (fun _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h) rfl)]
      exact d3
    · rcases haccO r y c u he with h | ⟨-, rfl, rfl, rfl⟩ <;>
        rcases haccO r' y c u' he' with h' | ⟨-, h1, h2, rfl⟩
      · exact p2 r r' y c u u' h h'
      · subst h1 h2; exact absurd h (hnoacc r u)
      · exact absurd h' (hnoacc r' u')
      · rfl
    · rcases haccO r' y c u' he' with h | ⟨-, rfl, rfl, rfl⟩
      · exact p3 r r' y c u u' (hpO _ _ _ _ he) h
      · exact hph r u (hpO _ _ _ _ he)
  have hvf : Inv.votesFollowProposals S' := by
    refine ⟨fun r y c st u he hst => ?_, fun r y c u he => ?_⟩
    · rcases hvoteO r y c st u he with h | ⟨-, -, -, rfl, -⟩
      · obtain ⟨l, u0, h1, h2⟩ := s8.1 r y c st u h hst
        exact ⟨l, u0, hH.ev_old h1, h2⟩
      · exact absurd hst (by rintro (h | h) <;> cases h)
    · rcases hvoteO r y c _ u he with h | ⟨-, rfl, rfl, -, rfl⟩
      · obtain ⟨l, h1⟩ := s8.2 r y c u h; exact ⟨l, hH.ev_old h1⟩
      · exact ⟨i, hH.ev_new (by simp)⟩
  have hrr : Inv.repliesReportVotes S' := by
    obtain ⟨q1, q2, q3⟩ := s9
    refine ⟨fun r m' e hp => ?_, fun a r m' hm' => ?_, fun a r m' hm' => ?_⟩
    · have hp0 := (hprepR r m' e).mp hp
      obtain ⟨d1, d2, d3, d4, d5⟩ := q1 r m' e hp0
      refine ⟨d1, fun hs => hH.evBefore_old (d2 hs), fun hs => (hcv' _ _).mpr (d3 hs),
        fun hs c st u hb' => d4 hs c st u (hevB _ _ _ _ hb' hp0.1),
        fun c st u hb' => ?_⟩
      obtain ⟨pp, pp', hlt', h1, h2⟩ := hb'
      have hv' : S'.ev r (.vote _ c st u) := List.mem_of_getElem? h2
      rcases hvoteO r _ c st u hv' with h | ⟨rfl, hy, rfl, -, -⟩
      · exact d5 c st u (hevB _ _ _ _ ⟨pp, pp', hlt', h1, h2⟩ h)
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
          exact c2 m2 e' hp0 hy (hevB _ _ _ _ hb' hsent)
      · cases h
  have hhi : Inv.prepReplyHighest S' := by
    intro r m' e hp c st u hb'
    have hp0 := (hprepR r m' e).mp hp
    exact s10 r m' e hp0 c st u (hevB _ _ _ _ hb' hp0.1)
  have hlbI : Inv.lbInv S' := by
    intro r hr y w2 lb2 h2 hl2
    rcases R1 r y w2 h2 with ⟨rfl, rfl, rfl⟩ | ⟨h, hne⟩
    · rw [W7] at hl2; cases hl2
      obtain ⟨a1, -, -, a4, -⟩ := hlbX
      obtain ⟨⟨Q, q1, q2, q3⟩, ⟨Q', q1', q2', q3'⟩⟩ := hQ
      refine ⟨by rw [k1]; exact hH.ev_old a1, by rw [k1]; exact k2, k5,
        fun c u hv0 => ?_,
        fun c1 => (by rw [k3] at c1; rcases c1 with h | h <;> cases h),
        ⟨Q, q1, q2, fun a m' hq => ?_⟩, ⟨Q', q1', q2', q3'⟩,
        fun _ _ _ _ => ?_, fun c1 => (by rw [k4] at c1; cases c1)⟩
      · rw [k1]
        rcases hv0 with hv0 | hv0
        · exact a4 c u (Or.inl (hpO _ _ _ _ hv0))
        · rcases haccO _ _ c u hv0 with h | ⟨-, -, rfl, -⟩
          · exact a4 c u (Or.inr h)
          · rw [hlt]; exact Int.le_refl _
      · obtain ⟨b1, b2, b3, b4, b5⟩ := q3 a m' hq
        exact ⟨b1, b2, b3, b4, b5, fun c1 => (by rw [k3] at c1; rcases c1 with h | h <;> cases h)⟩
      · have hv : (⟨lb'.cmds.getD [], lb'.seq, lb'.deps⟩ : Val) = v := by
          rw [k10, k11, k12]; rfl
        rw [hv, k1, hlt]
        exact ⟨hH.ev_new (by simp), hH.ev_new (by simp)⟩
    · obtain ⟨a1, a2, a3, a4, a5, ⟨Q, q1, q2, q3⟩, ⟨Q', q1', q2', q3'⟩, a8, a9⟩ :=
        s11 r hr y w2 lb2 h hl2
      refine ⟨hH.ev_old a1, a2, a3,
        fun c u hv0 => a4 c u (hv0.imp (hpO _ _ _ _) (fun h => haO _ _ _ _ h hne)),
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
      · rw [hlx, (hfl r).2.2.2.2.2]; exact p2 r hr k
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
    intro r e y cy z cz d hrec hne hb' hi'
    refine s17 r e y cy z cz d hrec hne (hevB _ _ _ _ hb' ?_) hi'
    obtain ⟨pp, pp', -, -, h⟩ := hb'
    exact hold r _ (List.mem_of_getElem? h) (fun _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
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
      · exact ⟨w', lb', R3, W7⟩
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
        subst hds
        have : m.deps = v.deps := by rw [← m8]
        rw [this]; exact hdeps
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
      exact c4' r m' e hp0 c u (hevB _ _ _ _ hb' hp0.1)
    · obtain ⟨w1, h1, hle⟩ := c5' r m' e hr ((hprepR r m' e).mp hp)
      rcases R2 r _ w1 h1 with ⟨rfl, hy, rfl⟩ | h
      · exact ⟨w', by rw [← hy]; exact R3, by rw [W2]; omega⟩
      · exact ⟨w1, h, hle⟩
    · rcases hvoteO r y c st u h3 with h3 | ⟨-, -, -, rfl, -⟩
      · rcases hvoteO r y c st' u' h4 with h4 | ⟨-, -, -, rfl, -⟩
        · exact c6' r y c st st' u u' h1 h2 h3 h4
        · exact absurd h2 (by rintro (h | h) <;> cases h)
      · exact absurd h1 (by rintro (h | h) <;> cases h)
    · exact c7' y u m' e (hold _ _ h1 (fun _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h))
        ((hprepR _ m' e).mp h2) h3
    · rcases haccO r y _ u h1 with h | ⟨-, rfl, hb', rfl⟩
      · exact fastBlocked_mono hsafeM (c8' r y u h u')
      · exact hinit hb'.symm u'
  refine ⟨⟨hwf, hmw, hrt, hntpa, hbal, hown, hop, hvf, hrr, hhi, hlbI,
    hagr, hdc, chosenSafe_of_safe _ hwf hbal hown hvf hsafe, hdcv, hwit, hac, hexec.1,
    hexec.2.1, hexec.2.2.1, hexec.2.2.2, hslots, hco, hcm, hpk, hsafe, hrepo⟩, ?_⟩
  have hlbv : ∀ r y w2 lb2, (S'.rep r).inst y = some w2 → w2.lb = some lb2 →
      (i = r ∧ x = y ∧ w' = w2 ∧ lb' = lb2) ∨
        ((S.rep r).inst y = some w2 ∧ ¬ (r = i ∧ y = x)) := by
    intro r y w2 lb2 h2 hl2
    rcases R1 r y w2 h2 with ⟨rfl, rfl, rfl⟩ | h
    · rw [W7] at hl2; cases hl2; exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
    · exact Or.inr h
  have hnotPA : ¬ isPA lb'.status := by rw [k3]; rintro (h | h) <;> cases h
  have hcntPA : ∀ fr to y c, S'.cnt fr to (Msg.isPAat y c) = S.cnt fr to (Msg.isPAat y c) :=
    fun fr to y c => hcnt0 fr to _ rfl
  have hcntPAR : ∀ fr to y c, S'.cnt fr to (Msg.isPARat y c) = S.cnt fr to (Msg.isPARat y c) :=
    fun fr to y c => hcnt0 fr to _ rfl
  have hcntAR : ∀ fr to y c, S'.cnt fr to (Msg.isARat y c) = S.cnt fr to (Msg.isARat y c) :=
    fun fr to y c => hcnt0 fr to _ rfl
  have hint1 : ∀ to, (intendedOf B.norm to).length ≤ 1 := by
    intro to; unfold intendedOf; split
    · split <;> simp
    · simp
  exact {
    stRange := fun r hr y w2 h2 => by
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · exact Or.inr (Or.inr (Or.inl W4))
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
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, hne⟩
      · exact Or.inl W4
      · exact hA.accKeep r hr y w2 h c u (hvO _ _ _ _ _ hv0 hne) hle
    recCommit := fun r hr y w2 h2 hs => by
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · exact absurd hs hnc'
      · obtain ⟨c, u, d1, d2⟩ := hA.recCommit r hr y w2 h hs
        exact ⟨c, u, hH.ev_old d1, d2⟩
    commitRec := fun r y c u hr he => by
      have h := hold _ _ he (fun _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      obtain ⟨w1, h1, hs⟩ := hA.commitRec r y c u hr h
      rcases R2 r y w1 h1 with ⟨-, -, rfl⟩ | h'
      · exact absurd hs hnc
      · exact ⟨w1, h', hs⟩
    fastCommitEv := fun r y u he => by
      obtain ⟨d1, c, d2⟩ := hA.fastCommitEv r y u
        (hold _ _ he (fun _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h))
      exact ⟨d1, c, hH.ev_old d2⟩
    makerLb := fun r y c hr he => by
      obtain ⟨w1, lb1, h1, hl1, hle⟩ := hA.makerLb r y c hr
        (hold _ _ he (fun _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h))
      rcases R2 r y w1 h1 with ⟨rfl, rfl, rfl⟩ | h
      · rw [hlb] at hl1; cases hl1; exact ⟨w', lb', R3, W7, by rw [k1]; exact hle⟩
      · exact ⟨w1, lb1, h, hl1, hle⟩
    lastLeBal := fun r hr y w2 lb2 h2 hl2 => by
      rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, rfl, rfl⟩ | ⟨h, -⟩
      · rw [k1, W2, hlt]; exact Int.le_refl _
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
      rcases (hmsgs _ _ _).mp hm' with hm' | ⟨-, rfl, -⟩
      · exact hA.crtMsg fr to m' y hm' hy
      · simp only [Msg.instOf, Option.some.injEq] at hy
        rw [m2] at hy; subst hy; exact hA.crtRec i hi x w hw
    crtEv := fun r e y he hy => by
      rw [(hfl y.q).2.2.1]
      rcases (hE r e).mp he with h | ⟨-, rfl | rfl⟩
      · exact hA.crtEv r e y h hy
      · simp only [Event.instOf, Option.some.injEq] at hy; subst hy
        exact ⟨hxq, hA.crtRec i hi x w hw⟩
      · simp only [Event.instOf, Option.some.injEq] at hy; subst hy
        exact ⟨hxq, hA.crtRec i hi x w hw⟩
    ownRow := fun q hq j hj => by
      rw [(hfl q).2.2.1] at hj
      obtain ⟨w1, lb1, h1, hl1⟩ := hA.ownRow q hq j hj
      rcases R2 q _ w1 h1 with ⟨rfl, hx', rfl⟩ | h
      · exact ⟨w', lb', by rw [← hx']; exact R3, W7⟩
      · exact ⟨w1, lb1, h, hl1⟩
    paNoAcc := fun r hr y w2 lb2 h2 hl2 hs u hv0 => by
      rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, -, rfl⟩ | ⟨h, hne⟩
      · exact hnotPA hs
      · exact hA.paNoAcc r hr y w2 lb2 h hl2 hs u (haO _ _ _ _ hv0 hne)
    paLeader := fun r hr y w2 lb2 h2 hl2 hs hp hc' hb' => by
      rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, -, rfl⟩ | ⟨h, -⟩
      · exact absurd hs hnotPA
      · obtain ⟨u, hu⟩ := hp
        exact hA.paLeader r hr y w2 lb2 h hl2 hs ⟨u, hpO _ _ _ _ hu⟩ hc' hb'
    prepNoProp := fun r hr y w2 lb2 h2 hl2 hp => by
      rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, -, rfl⟩ | ⟨h, hne⟩
      · rw [k4] at hp; cases hp
      · obtain ⟨d1, d2, d3, d4, d5⟩ := hA.prepNoProp r hr y w2 lb2 h hl2 hp
        exact ⟨d1, fun u h' => d2 u (hpO _ _ _ _ h'),
          fun u h' => d3 u (haO _ _ _ _ h' hne), d4, d5⟩
    paMsgOnce := fun fr to y c => by rw [hcntPA]; exact hA.paMsgOnce fr to y c
    accMsgOnce := fun fr to y c => by
      rw [hH.cnt_eq]
      split
      · rename_i hfr; subst fr
        by_cases hp : Msg.isAccAt y c (.accept m) = true
        · have h0 : S.cnt i to (Msg.isAccAt y c) = 0 := by
            simp only [Sys.cnt, List.length_eq_zero_iff, List.filter_eq_nil_iff]
            intro m' hm' hp'
            cases m' with
            | accept a =>
              simp only [Msg.isAccAt, decide_eq_true_eq] at hp hp'
              rw [m2, m7] at hp
              exact hnoaccMsg i to a hm' (by rw [hp'.1, ← hp.1]) (by rw [hp'.2, ← hp.2])
            | _ => simp [Msg.isAccAt] at hp'
          rw [h0]; simp only [List.nil_append, Nat.zero_add]
          exact Nat.le_trans (List.length_filter_le _ _) (hint1 to)
        · simp only [List.nil_append]
          have : (intendedOf B.norm to).filter (Msg.isAccAt y c) = [] := by
            simp only [List.filter_eq_nil_iff]
            intro m' hm'
            obtain ⟨h1, -⟩ := mem_intended_norm hm'
            rw [h1, hBm]; simpa using hp
          rw [this]; simpa using hA.accMsgOnce i to y c
      · simpa using hA.accMsgOnce fr to y c
    paVoteDeliv := fun r y c st u hst hv0 => by
      rcases hvoteO r y c st u hv0 with h | ⟨-, -, -, rfl, -⟩
      · rcases hA.paVoteDeliv r y c st u hst h with ⟨u0, h0⟩ | h0
        · exact Or.inl ⟨u0, hH.ev_old h0⟩
        · exact Or.inr (fun fr' => hallP _ _ _ rfl (h0 fr'))
      · exact absurd hst (by rintro (h | h) <;> cases h)
    parOnce := fun a r y c h1 => by
      rw [hcntPAR] at h1 ⊢
      obtain ⟨d1, d2⟩ := hA.parOnce a r y c h1
      exact ⟨d1, hallP _ _ _ rfl d2⟩
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
        · rw [hlb] at hl1; cases hl1; exact ⟨w', lb', R3, W7, by rw [k1]; exact hlt'⟩
        · exact ⟨w1, lb1, h, hl1, hlt'⟩
      · refine Or.inr ⟨d1, ?_⟩
        by_cases hp : Msg.isAccAt y c (.accept m) = true
        · by_cases hri : r = i
          · exfalso
            subst hri
            simp only [Msg.isAccAt, decide_eq_true_eq] at hp
            rw [m2, m7] at hp
            obtain ⟨n0, m0, hn0, hp0⟩ : ∃ n0 m0, (S.msgs a r)[n0]? = some m0 ∧
                Msg.isARat y c m0 = true := by
              have : ((S.msgs a r).filter (Msg.isARat y c)) ≠ [] := by
                intro h0; simp only [Sys.cnt, h0, List.length_nil] at h1; omega
              obtain ⟨m0, hm0⟩ := List.exists_mem_of_ne_nil _ this
              rw [List.mem_filter] at hm0
              obtain ⟨n0, hn0⟩ := List.mem_iff_getElem?.mp hm0.1
              exact ⟨n0, m0, hn0, hm0.2⟩
            cases m0 with
            | acceptReply ar =>
              simp only [Msg.isARat, decide_eq_true_eq] at hp0
              exact noAR a ar (List.mem_of_getElem? hn0) (by rw [hp0.1, ← hp.1])
                (by rw [hp0.2, ← hp.2])
            | _ => simp [Msg.isARat] at hp0
          · exact hH.allDeliv_old d2 (fun h => absurd h hri)
        · exact hallP _ _ _ (by simpa using hp) d2
    commitBal := fun fr to m' hm' => by
      rcases (hmsgs _ _ _).mp hm' with hm' | ⟨-, h, -⟩
      · exact hA.commitBal fr to m' hm'
      · cases h
    sentPR := fun r to m' he => by
      have he0 := hold _ _ he (fun _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      obtain ⟨d1, d2, d3⟩ := hA.sentPR r to m' he0
      refine ⟨fun hr => ?_, fun c st u hb' => ?_, fun to' m2 hb' hy => d3 to' m2 ?_ hy⟩
      · obtain ⟨w1, h1, hle⟩ := d1 hr
        rcases R2 r _ w1 h1 with ⟨rfl, hy, rfl⟩ | h
        · exact ⟨w', by rw [← hy]; exact R3, by rw [W2]; omega⟩
        · exact ⟨w1, h, hle⟩
      · obtain ⟨pp, pp', hlt', h1, h2⟩ := hb'
        rcases hvoteO r _ c st u (List.mem_of_getElem? h2) with h | ⟨rfl, hy, rfl, -, -⟩
        · exact d2 c st u (hevB _ _ _ _ ⟨pp, pp', hlt', h1, h2⟩ h)
        · obtain ⟨w1, h1', hle⟩ := d1 hi
          rw [hy, hw] at h1'; cases h1'; omega
      · obtain ⟨pp, pp', hlt', h1, h2⟩ := hb'
        exact hevB _ _ _ _ ⟨pp, pp', hlt', h1, h2⟩
          (hold _ _ (List.mem_of_getElem? h2) (fun _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h))
    confCover := fun r hr e y cy he hrec c hc' => by
      rw [(hfl r).2.2.2.1]
      rcases (hE r e).mp he with h | ⟨-, rfl | rfl⟩
      · exact hA.confCover r hr e y cy h hrec c hc'
      · cases hrec
      · cases hrec
    classWf := fun r hr => by
      have hcl : (S'.rep r).lastScan = (S.rep r).lastScan ∧
          (S'.rep r).lastPut = (S.rep r).lastPut := by
        by_cases h : r = i
        · subst h; rw [hH.rep_self]; exact hcls
        · rw [hH.rep_other h]; exact ⟨rfl, rfl⟩
      refine AuxProof.clsWf_keep (hA.classWf r hr) hcl.1 hcl.2 (fun y h => ?_)
      obtain ⟨w1, h1⟩ := Option.ne_none_iff_exists'.mp h
      rcases R2 r y w1 h1 with ⟨rfl, rfl, -⟩ | h2
      · rw [R3]; simp
      · rw [h2]; simp
    classCover := fun r hr e y cy he hrec => by
      have hcl : (S'.rep r).lastScan = (S.rep r).lastScan ∧
          (S'.rep r).lastPut = (S.rep r).lastPut := by
        by_cases h : r = i
        · subst h; rw [hH.rep_self]; exact hcls
        · rw [hH.rep_other h]; exact ⟨rfl, rfl⟩
      rw [hcl.1, hcl.2]
      rcases (hE r e).mp he with h | ⟨-, rfl | rfl⟩
      · exact hA.classCover r hr e y cy h hrec
      · cases hrec
      · cases hrec
    paAttrs := fun r y c st u hst hv0 => by
      rcases hvoteO r y c st u hv0 with h | ⟨-, -, -, rfl, -⟩
      · exact hH.ev_old (hA.paAttrs r y c st u hst h)
      · exact absurd hst (by rintro (h | h) <;> cases h)
    valOk := fun r y c u hv0 => by
      rw [hH.owner]
      rcases hv0 with hv0 | hv0
      · exact hA.valOk r y c u (Or.inl (hpO _ _ _ _ hv0))
      · rcases haccO r y c u hv0 with h | ⟨-, rfl, rfl, rfl⟩
        · exact hA.valOk r y c u (Or.inr h)
        · exact hval
    cmdsNe := by
      obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hA.cmdsNe
      refine ⟨fun fr to m' hm' cs hcs => ?_,
        fun r hr y w2 cs h2 hc' => ?_, fun r hr y w2 lb2 cs h2 hl2 hc' => ?_,
        fun fr to m' hm' => ?_,
        fun r m' he => n5 r m' (hold _ _ he (fun _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)),
        fun r y c u hv0 => ?_⟩
      · rcases (hmsgs _ _ _).mp hm' with hm' | ⟨-, rfl, -⟩
        · exact n1 fr to m' hm' cs hcs
        · simp only [Msg.commandField, Option.some.injEq] at hcs
          subst hcs
          have : m.command = v.cmds := by rw [← m8]
          rw [this]; exact hcne
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
        · exact n6 r y c u (Or.inl (hpO _ _ _ _ hv0))
        · rcases haccO r y c u hv0 with h | ⟨-, rfl, rfl, rfl⟩
          · exact n6 r y c u (Or.inr h)
          · exact hcne
    prSent := fun fr to m' hm' => by
      rcases (hmsgs _ _ _).mp hm' with hm' | ⟨-, h, -⟩
      · exact hH.ev_old (hA.prSent fr to m' hm')
      · cases h
    selfOk := fun r m' he hs => hA.selfOk r m'
      (hold _ _ he (fun _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)) hs
    selfRaw := fun r m' he => hA.selfRaw r m'
      (hold _ _ he (fun _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h))
    pm := by
      have hP := hA.pm
      have hmono : ∀ r e, S.ev r e → S'.ev r e := fun r e h => hH.ev_old h
      have hbal : ∀ r y w1, (S.rep r).inst y = some w1 →
          ∃ w2, (S'.rep r).inst y = some w2 ∧ zz w1.bal ≤ zz w2.bal := by
        intro r y w1 h1
        rcases R2 r y w1 h1 with ⟨rfl, rfl, rfl⟩ | h
        · exact ⟨w', R3, by rw [W2]; exact hb⟩
        · exact ⟨w1, h, Int.le_refl _⟩
      have hph : ∀ r y c u, S'.ev r (.phase1 y c u) → S.ev r (.phase1 y c u) :=
        fun r y c u h => hold _ _ h (fun _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      have hcm : ∀ r y c u, S'.ev r (.commit y c u) → S.ev r (.commit y c u) :=
        fun r y c u h => hold _ _ h (fun _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      have hvPA : ∀ r y c st u, S'.ev r (.vote y c st u) → isPA st → S.ev r (.vote y c st u) := by
        intro r y c st u h hst
        rcases hvoteO r y c st u h with h | ⟨-, -, -, rfl, -⟩
        · exact h
        · rcases hst with h | h <;> cases h
      have hmsgAR : ∀ a r m', Msg.acceptReply m' ∈ S'.msgs a r → Msg.acceptReply m' ∈ S.msgs a r := by
        intro a r m' h; rcases (hmsgs _ _ _).mp h with h | ⟨-, h, -⟩
        · exact h
        · cases h
      have hmsgPAR : ∀ a r m', Msg.preAcceptReply m' ∈ S'.msgs a r →
          Msg.preAcceptReply m' ∈ S.msgs a r := by
        intro a r m' h; rcases (hmsgs _ _ _).mp h with h | ⟨-, h, -⟩
        · exact h
        · cases h
      have hsent : ∀ fr to m', m' ∈ S.sent fr to → m' ∈ S'.sent fr to := by
        intro fr to m' h; rw [hH.sent]; exact h
      exact {
        arOk := PMProof.arOk_frame2 hP hmsgAR (fun a r m' hm' u hu => by
            rcases haccO _ _ _ _ hu with h | ⟨rfl, hx, hb', rfl⟩
            · exact h
            · exact absurd hb' (noAR a m' hm' hx))
          (fun q y c u h => by
            rcases hvoteO q y c _ u h with h | ⟨rfl, rfl, rfl, -, -⟩
            · exact Or.inl h
            · refine Or.inr (fun w1 h1 => ?_); rw [hw] at h1; cases h1; exact hb)
          hmono (fun y u h => (hcv' _ _).mpr h) hbal
        commitProp := PMProof.commitProp_frame hP hcm hmono
        commitMsgProp := PMProof.commitMsgProp_frame hP (fun fr to m' h => by
          rcases (hmsgs _ _ _).mp h with h | ⟨-, h, -⟩
          · exact h
          · cases h) hmono
        lbProp := fun r hr y w2 lb2 h2 hl2 hs hv => by
          rcases hlbv r y w2 lb2 h2 hl2 with ⟨rfl, rfl, -, rfl⟩ | ⟨h, hne⟩
          · rw [k10]; simp only [Option.getD_some]
            rcases hlbP with h | h
            · rw [h]; exact Or.inl ⟨_, stACCEPTED, v, Or.inr rfl, hH.ev_new (by simp), rfl⟩
            · exact PMProof.propAt_mono hmono h
          · obtain ⟨u, hu⟩ := hv
            rcases haccO _ _ _ _ hu with hu | ⟨rfl, rfl, -, -⟩
            · exact PMProof.propAt_mono hmono (hP.lbProp r hr y w2 lb2 h hl2 hs ⟨u, hu⟩)
            · exact absurd ⟨rfl, rfl⟩ hne
        parCom := PMProof.parCom_frame hP hmsgPAR hmono
        parSt := PMProof.parSt_frame hP hmsgPAR hsent
        paFresh := fun r hr y w2 lb2 h2 hl2 hs h0 hv => by
          rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, -, rfl⟩ | ⟨h, -⟩
          · exact absurd hs hnotPA
          · obtain ⟨u, hu⟩ := hv
            exact hP.paFresh r hr y w2 lb2 h hl2 hs h0 ⟨u, hph _ _ _ _ hu⟩
        paCmds := fun r hr y w2 lb2 h2 hl2 hs u hu => by
          rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, -, rfl⟩ | ⟨h, -⟩
          · exact absurd hs hnotPA
          · exact hP.paCmds r hr y w2 lb2 h hl2 hs u (hph _ _ _ _ hu)
        paSent := PMProof.ps_hs hP hH hidle.1 (fun to m' h => by simp at h)
          (fun b' h => by
            obtain ⟨h1, -⟩ := norm_some h
            rw [h1]; exact hBt) (fun y w2 lb2 h2 hl2 hlt2 => by
            rcases hlbv _ y w2 lb2 h2 hl2 with ⟨h1, rfl, -, rfl⟩ | ⟨h, -⟩
            · exact ⟨w, lb, by rw [← h1]; exact hw, hlb, by rw [← k1]; exact hlt2, hpas⟩
            · exact ⟨w2, lb2, h, hl2, hlt2, rfl⟩)
        pendPA := PMProof.pendPA_hs hP hH (fun b' h y c hc => by
          obtain ⟨h1, -⟩ := norm_some h
          rw [h1, hBm] at hc; simp [Msg.isPAat] at hc)
        paVoteMsg := fun r y st u hst hne hv => by
          obtain ⟨p', h1, h2, h3⟩ := hP.paVoteMsg r y st u hst hne (hvPA _ _ _ _ _ hv hst)
          exact ⟨p', hsent _ _ _ h1, h2, h3⟩
        parNoPA := fun a r m' hm' hn st u hst hv =>
          hP.parNoPA a r m' (hmsgPAR _ _ _ hm') hn st u hst (hvPA _ _ _ _ _ hv hst)
        aeF := fun r hr y w2 lb2 h2 hl2 hs hae => by
          rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, -, rfl⟩ | ⟨h, -⟩
          · exact absurd hs hnotPA
          · obtain ⟨a, a', m1, m2, h1, h2', h3⟩ := hP.aeF r hr y w2 lb2 h hl2 hs hae
            exact ⟨a, a', m1, m2, hsent _ _ _ h1, hsent _ _ _ h2', h3⟩
        repLead := PMProof.repLead_frame hP (fun r m' e h => (hprepR r m' e).mp h) hbal
        paGe := fun r y c st u l v0 hst h1 h2 =>
          hP.paGe r y c st u l v0 hst (hvPA _ _ _ _ _ h1 hst) (hph _ _ _ _ h2)
        phAttrs := PMProof.phAttrs_frame hP hph hmono
        accWit := fun r y c u h hn => by
          rcases haccO _ _ _ _ h with h | ⟨-, rfl, -, rfl⟩
          · rcases hP.accWit r y c u h hn with h' | ⟨u', hu'⟩
            · exact Or.inl (PMProof.witnessed_mono hmono h')
            · exact Or.inr ⟨u', (hcv' _ _).mpr hu'⟩
          · rcases hwit hn with h' | ⟨u', hu'⟩
            · exact Or.inl (PMProof.witnessed_mono hmono h')
            · exact Or.inr ⟨u', (hcv' _ _).mpr hu'⟩
        accVote := fun r y c u h => by
          rcases haccO _ _ _ _ h with h | ⟨rfl, rfl, rfl, rfl⟩
          · exact hmono _ _ (hP.accVote _ _ _ _ h)
          · exact hH.ev_new (by simp)
        cmdSafe := CmdSafeProof.cmdSafe_frame hP hsafeM hpO
        accSup := CmdSafeProof.accSup_step hP hmono (fun r y c u h => by
          rcases haccO _ _ _ _ h with h | ⟨-, rfl, rfl, rfl⟩
          · exact Or.inl h
          · exact Or.inr hsup) }
    ownerCrt := fun y ps h => by
      rw [hH.owner] at h; rw [(hfl y.q).2.2.1]; exact hA.ownerCrt y ps h
    execLo := AuxProof.execLo_of_eq hA.execLo (fun r _ => (hfl r).2.2.2.2.1)
    exec := ExecOrd.invExec_hs hS.1 hA.exec hH hidle hagr hchan (fun r y h => by rw [hrep, if_neg]; rintro ⟨h1, h2⟩; rcases h with h | h; exact h h1; exact h h2) R3
      (fun w0 h0 hs => by rw [hw] at h0; cases h0; exact absurd hs hwnex)
      (fun lb2 hl hne => ⟨w, lb, hw, hlb, by rw [W7] at hl; cases hl; rw [k6] at hne; exact hne⟩) }

end RecAcceptProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
