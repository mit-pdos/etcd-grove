/-
`handlePropose` (`Step.propose`, p-model2): the law `inv_step_propose`. A full row (fix R-CAP)
drops the proposal (`ProposeProof.inv_propose_full`); otherwise the replica's `crtInstance` is
bumped to a fresh instance `x`, `x`'s owner becomes the batch (its tokens move from the channel to
`x`'s slots), and `startPhase1` runs at the initial ballot after `makeBallot`
(`inv_propose_start`: a copy of `RecPhase1Proof.inv_phase1_start` for a fresh instance — no
record, no event, message or owner about `x` before — with the `makeBallot` event first, the
`crtInstance` bump, and the owner/channel update).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.ProposeChan

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace ProposeProof

open HStepProof HLocal SafeProof AuxProof RecCommitProof RecAcceptProof ConfProof CommitProof
  RecPhase1Proof

/-- (`InvPM`) A handler step of an idle replica appends its direct sends to its outbox. -/
private theorem pmp_outbox_eq {S S' : Sys} {i : Nat} {σ' : RState} {E : List Event}
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

/-- (`InvPM`) A handler step of an idle replica without direct sends keeps what each replica
handed to the wire. -/
private theorem pmp_rcpt {S S' : Sys} {i : Nat} {σ' : RState} {E : List Event}
    {pend : Option Bcast} (hH : HS S S' i σ' E (fun _ => []) pend)
    (hidle : S.pending i = none) (fr to : Nat) :
    S'.sent fr to ++ S'.outbox fr to = S.sent fr to ++ S.outbox fr to := by
  rw [hH.sent, pmp_outbox_eq hH hidle]; split <;> simp

/-- **`handlePropose`'s start of a fresh instance keeps the invariant.** The step from `S`: the
batch leaves `i`'s channel and owns the fresh instance `x` (`S2`), then the handler step of `i`
(`hH`): `crtInstance[i]` bumped to `x.i` (`n`), the record and bookkeeping of `x` created
PRE-ACCEPTED at the initial ballot `b`, the events `makeBallot`, `phase1`, the own pre-accept
`vote`, `attrsRec`, `updateConflicts`, the PreAccept broadcast pending. -/
theorem inv_propose_start (S S2 S' : Sys) (i : Nat) (batch : List Proposal) (σ' σu σb : RState)
    (x : InstId) (lbN : LbRec) (b n : w32) (cmds : List WCmd) (seq : w32) (deps : List w32)
    (B : Bcast) (m : PreAccept) (hS : Inv S) (hi : i < nR) (hidle : S.idle i)
    (hsub : batch.Subperm (S.proposeChan i)) (hbne : batch ≠ []) (hcmd : cmds = batch.map (·.cmd))
    (hS2 : S2 = { S with proposeChan := upd S.proposeChan i ((S.proposeChan i).diff batch),
                         owner := upd S.owner x (some batch) })
    (hxq : x.q = i) (hbI : b = initBal x)
    (hd : deps = (updateAttributes σu cmds (W32 0) (List.replicate nR (W32 (-1)))).2.1)
    (hσu : σu.conflicts = (S.rep i).conflicts)
    (hσus : σu.lastScan = (S.rep i).lastScan ∧ σu.lastPut = (S.rep i).lastPut)
    (hH : HS S2 S' i σ' [.makeBallot x b, .phase1 x b ⟨cmds, W32 (-1), deps⟩,
      .vote x b stPREACCEPTED ⟨cmds, seq, deps⟩, .attrsRec x cmds deps] (fun _ => []) B.norm)
    (hchan : S'.proposeChan = S2.proposeChan)
    (hB : B.x = x ∧ B.m = .preAccept m ∧ B.peers = (S.rep i).peerOrder.take (nR - 1) ∧
      B.need = 2 * fR - 1 ∧ B.sent = 0)
    (hmm : m.leaderId = W32 i ∧ (⟨toN m.replica, toN m.inst⟩ : InstId) = x ∧ 0 ≤ zz m.replica ∧
      zz m.replica < nR ∧ 0 ≤ zz m.inst ∧ toN m.inst + 1 < MAX_INSTANCE ∧ m.ballot = b ∧
      m.command = cmds ∧ m.seq = W32 (-1) ∧ m.deps = deps)
    (hσ : σ'.inst = upd (S.rep i).inst x (some (p1Rec x cmds b seq deps lbN)))
    (hc : σ'.id = (S.rep i).id ∧ σ'.peerOrder = (S.rep i).peerOrder ∧
      σ'.crtInstance = upd (S.rep i).crtInstance i n ∧
      σ'.execedUpTo = (S.rep i).execedUpTo ∧ σ'.store = (S.rep i).store)
    (hconf : σb.conflicts = (S.rep i).conflicts ∧
      σ'.conflicts = (updateConflicts σb cmds x.q n seq).conflicts)
    (hcls : σb.lastScan = (S.rep i).lastScan ∧ σb.lastPut = (S.rep i).lastPut ∧
      σb.inst = σ'.inst ∧ σ'.lastScan = (updateConflicts σb cmds x.q n seq).lastScan ∧
      σ'.lastPut = (updateConflicts σb cmds x.q n seq).lastPut)
    (hn : 0 ≤ zz n ∧ toN n = x.i ∧ zz n = zz ((S.rep i).crtInstance i) + 1)
    (hxM : x.i + 1 < MAX_INSTANCE)
    (hk : lbN.lastTriedBallot = b ∧ lbN.ballot = W32 (-1) ∧ lbN.status = stPREACCEPTED ∧
      lbN.preparing = false ∧ lbN.tryingToPreAccept = false ∧
      lbN.clientProposals = some batch ∧ lbN.preAcceptOKs = W64 0 ∧ lbN.acceptOKs = W64 0 ∧
      lbN.cmds = some cmds ∧ lbN.deps = deps)
    (hae : lbN.allEqual = true := by rfl) (hpas : lbN.preAcceptsSent = W64 0 := by rfl)
    (htr : B.trackPA = true := by rfl) :
    Inv S' := by
  subst hS2
  obtain ⟨c1, c2, c3, c5, c6⟩ := hc
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k10, k12⟩ := hk
  obtain ⟨hBx, hBm, hBp, hBn, hBs⟩ := hB
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8a, m8b, m8c⟩ := hmm
  have hdeps : depsOk deps := by rw [hd]; exact ua_depsOk S i hS hi σu hσu hσus cmds
  generalize hw'd : p1Rec x cmds b seq deps lbN = w' at hσ
  have hA := hS.2
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19,
    s20, s21, s22, s23, s24, s25, s26, s27⟩ := hS.1
  have hxq' : x.q < nR := by rw [hxq]; exact hi
  have hb0 : 0 ≤ zz b := by rw [hbI, zz_initBal x hxq']; omega
  have hPA : isPA stPREACCEPTED := Or.inl rfl
  have hnotACC : ¬ isPA stACCEPTED := by rintro (h | h) <;> cases h
  have hcne : cmds ≠ [] := by rw [hcmd]; simpa using hbne
  -- freshness: nothing is about `x` yet
  have hxi : (x.i : Int) = zz ((S.rep i).crtInstance i) + 1 := by
    rw [← hn.2.1, toN_of_zz n hn.1]; exact hn.2.2
  have hfrE : ∀ r e, S.ev r e → e.instOf ≠ some x := by
    intro r e he hx
    have := (hA.crtEv r e x he hx).2; rw [hxq] at this; omega
  have hfrM : ∀ fr to m', m' ∈ S.msgs fr to → m'.instOf ≠ some x := by
    intro fr to m' hm' hx
    have := hA.crtMsg fr to m' x hm' hx; rw [hxq] at this; omega
  have hfrR : ∀ r < nR, (S.rep r).inst x = none := by
    intro r hr
    cases h : (S.rep r).inst x with
    | none => rfl
    | some w0 => have := hA.crtRec r hr x w0 h; rw [hxq] at this; omega
  have hw : (S.rep i).inst x = none := hfrR i hi
  have hfrO : S.owner x = none := by
    cases h : S.owner x with
    | none => rfl
    | some ps => have := (hA.ownerCrt x ps h).2; rw [hxq] at this; omega
  have hnoph : ∀ r u, ¬ S.ev r (.phase1 x b u) := fun r u h => hfrE r _ h rfl
  have hnoacc : ∀ r u, ¬ S.ev r (.accept x b u) := fun r u h => hfrE r _ h rfl
  have hnovPA : ∀ r st u, isPA st → ¬ S.ev r (.vote x b st u) := fun r st u _ h => hfrE r _ h rfl
  have hnoMk : ∀ r c, ¬ S.ev r (.makeBallot x c) := fun r c h => hfrE r _ h rfl
  have hnocv : ∀ u, ¬ S.committedVal x u := by
    rintro u (⟨r, c, h⟩ | ⟨fr, to, m', hm', hx, -⟩)
    · exact hfrE r _ h rfl
    · exact hfrM fr to _ hm' hx
  -- events
  have hE : ∀ r e, S'.ev r e ↔ S.ev r e ∨
      (r = i ∧ (e = .makeBallot x b ∨ e = .phase1 x b ⟨cmds, W32 (-1), deps⟩ ∨
        e = .vote x b stPREACCEPTED ⟨cmds, seq, deps⟩ ∨ e = .attrsRec x cmds deps)) := by
    intro r e; rw [hH.ev_iff]; simp; rfl
  have hold : ∀ r e, S'.ev r e → (∀ y c u, e ≠ .phase1 y c u) → (∀ y c st u, e ≠ .vote y c st u) →
      (∀ y c d, e ≠ .attrsRec y c d) → (∀ y c, e ≠ .makeBallot y c) → S.ev r e := by
    intro r e he h1 h2 h3 h4
    rcases (hE r e).mp he with h | ⟨-, rfl | rfl | rfl | rfl⟩
    · exact h
    · exact absurd rfl (h4 _ _)
    · exact absurd rfl (h1 _ _ _)
    · exact absurd rfl (h2 _ _ _ _)
    · exact absurd rfl (h3 _ _ _)
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
    rcases (hE r _).mp h with h | ⟨hr, h | h | h | h⟩
    · exact Or.inl h
    · cases h
    · cases h
    · simp only [Event.vote.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact Or.inr ⟨hr, rfl, rfl, rfl, rfl⟩
    · cases h
  have hphO : ∀ r y c u, S'.ev r (.phase1 y c u) → S.ev r (.phase1 y c u) ∨
      (r = i ∧ y = x ∧ c = b ∧ u = ⟨cmds, W32 (-1), deps⟩) := by
    intro r y c u h
    rcases (hE r _).mp h with h | ⟨hr, h | h | h | h⟩
    · exact Or.inl h
    · cases h
    · simp only [Event.phase1.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr ⟨hr, rfl, rfl, rfl⟩
    · cases h
    · cases h
  have hmkO : ∀ r y c, S'.ev r (.makeBallot y c) → S.ev r (.makeBallot y c) ∨
      (r = i ∧ y = x ∧ c = b) := by
    intro r y c h
    rcases (hE r _).mp h with h | ⟨hr, h | h | h | h⟩
    · exact Or.inl h
    · simp only [Event.makeBallot.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact Or.inr ⟨hr, rfl, rfl⟩
    all_goals cases h
  have haO : ∀ r y c u, S'.ev r (.accept y c u) → S.ev r (.accept y c u) :=
    fun r y c u h => hold r _ h (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)
  have hnoPAmsg : ∀ fr to (m' : PreAccept), Msg.preAccept m' ∈ S.msgs fr to →
      (⟨toN m'.replica, toN m'.inst⟩ : InstId) = x → m'.ballot ≠ b := by
    intro fr to m' hm' hx _
    exact hfrM fr to _ hm' (by simp only [Msg.instOf, hx])
  have noPAR : ∀ a (m' : PreAcceptReply), Msg.preAcceptReply m' ∈ S.msgs a i →
      (⟨toN m'.replica, toN m'.inst⟩ : InstId) = x → m'.ballot ≠ b := by
    intro a m' hm' hx _
    exact hfrM a i _ hm' (by simp only [Msg.instOf, hx])
  have hnotEold : ∀ r e, S.ev r e → (∀ y c d, e ≠ .attrsRec y c d) → r = i →
      e ∉ [Event.makeBallot x b, .phase1 x b ⟨cmds, W32 (-1), deps⟩,
        .vote x b stPREACCEPTED ⟨cmds, seq, deps⟩, .attrsRec x cmds deps] := by
    intro r e he h3 hr h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact hnoMk r _ he
    · exact hnoph r _ he
    · exact hnovPA r _ _ hPA he
    · exact h3 _ _ _ rfl
  have hevB : ∀ r e r' e', S'.evBefore r e r' e' → S.ev r' e' → (∀ y c d, e' ≠ .attrsRec y c d) →
      S.evBefore r e r' e' :=
    fun r e r' e' h h' h3 => hH.evBefore_back h h' (hnotEold r' e' h' h3)
  have hhist : S'.hist = S.hist ++ [Event.makeBallot x b, .phase1 x b ⟨cmds, W32 (-1), deps⟩,
      .vote x b stPREACCEPTED ⟨cmds, seq, deps⟩, .attrsRec x cmds deps].map (fun e => (i, e)) :=
    hH.hist
  have hce : ∀ fr to (p : Msg → Bool), S'.cnt fr to p = S.cnt fr to p +
      (if fr = i then ((([] : List Msg) ++ intendedOf B.norm to).filter p).length else 0) :=
    hH.cnt_eq
  have hcnt0 : ∀ fr to (p : Msg → Bool), p (.preAccept m) = false →
      S'.cnt fr to p = S.cnt fr to p := by
    intro fr to p hp
    rw [hce]
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
  have R2 : ∀ r y w1, (S.rep r).inst y = some w1 → (S'.rep r).inst y = some w1 := by
    intro r y w1 h
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc; rw [hw] at h; cases h
    · rw [hrep, if_neg hc]; exact h
  have hyx : ∀ r y w1, r < nR → (S.rep r).inst y = some w1 → y ≠ x := by
    rintro r y w1 hr h rfl; rw [hfrR r hr] at h; cases h
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
      (S'.rep r).execedUpTo = (S.rep r).execedUpTo ∧ (S'.rep r).store = (S.rep r).store := by
    intro r
    by_cases hr : r = i
    · subst hr; rw [hH.rep_self]; exact ⟨c1, c2, c5, c6⟩
    · rw [hH.rep_other hr]; exact ⟨rfl, rfl, rfl, rfl⟩
  -- `crtInstance`: only `i`'s own entry moves, to `x.i`
  have hcrt : ∀ r q, (S'.rep r).crtInstance q =
      if r = i ∧ q = i then n else (S.rep r).crtInstance q := by
    intro r q
    by_cases hr : r = i
    · subst hr; rw [hH.rep_self, c3]
      by_cases hq : q = r
      · subst hq; simp
      · simp [upd_other _ _ _ _ hq, hq]
    · rw [hH.rep_other hr]; simp [hr]
  have hcrtI : zz ((S'.rep i).crtInstance i) = x.i := by
    rw [hcrt]; simp only [and_self, if_true]; rw [← hn.2.1, toN_of_zz n hn.1]
  have hcrtle : ∀ r q, zz ((S.rep r).crtInstance q) ≤ zz ((S'.rep r).crtInstance q) := by
    intro r q; rw [hcrt]; split
    · rename_i h; obtain ⟨rfl, rfl⟩ := h; rw [hn.2.2]; omega
    · exact Int.le_refl _
  have W : w'.cmds = some cmds ∧ w'.bal = b ∧ w'.vbal = b ∧ w'.status = stPREACCEPTED ∧
      w'.seq = seq ∧ w'.deps = deps ∧ w'.lb = some lbN ∧ w'.id = x ∧
      instVal w' = ⟨cmds, seq, deps⟩ := by
    rw [← hw'd]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [instVal, p1Rec]⟩
  obtain ⟨W1, W2, W3, W4, W5, W6, W7, W8, W9⟩ := W
  have hnc' : ¬ isCommitted w'.status := by rw [W4]; rintro (h | h) <;> cases h
  have hw'nex : w'.status ≠ stEXECUTED := by rw [W4]; decide
  have hex : ∀ r y, (S'.rep r).executed y ↔ (S.rep r).executed y := by
    intro r y
    constructor
    · rintro ⟨w2, h2, hs⟩
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · exact absurd hs hw'nex
      · exact ⟨w2, h, hs⟩
    · rintro ⟨w1, h1, hs⟩
      exact ⟨w1, R2 r y w1 h1, hs⟩
  have hxlog : x ∉ S.execLog i := by
    intro h
    obtain ⟨w1, h1, hs⟩ := ((s18 i hi).2.1 x).mp h
    rw [hw] at h1; cases h1
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
      fun _ _ h => absurd hxq.symm h⟩
    rw [hw] at h0; cases h0
  have hsafeM : SafeMono S S' := by
    refine ⟨fun r y w1 h1 => ?_, fun r e h => hH.ev_old h,
      fun r y c st u h => ?_,
      fun y u h => Or.inl (hold _ _ h (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
        (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)),
      fun a y m' h hy hb' => ?_⟩
    · exact ⟨w1, R2 r y w1 h1, Int.le_refl _, fun h => Or.inl h⟩
    · rcases hvoteO r y c st u h with h | ⟨rfl, rfl, rfl, rfl, rfl⟩
      · exact Or.inl h
      · exact Or.inr hvoteNew
    · rcases (hmsgs _ _ _).mp h with h | ⟨-, h, -⟩
      · exact Or.inl h
      · cases h
        simp only [Msg.instOf, Option.some.injEq] at hy
        rw [m2] at hy; subst hy
        exact Or.inr (fun v0 h0 => hfrE _ _ h0 rfl)
  have hsafe : Inv.safe S' := by
    refine safe_step hsafeM s26 (fun r y c u h => Or.inl (haO r y c u h)) (fun r y c u h => ?_)
    rcases hphO r y c u h with h | ⟨-, rfl, rfl, -⟩
    · exact Or.inl h
    · refine Or.inr ⟨fun b' hr hlt _ => ?_, fun hlt => ?_⟩
      · rw [hbI] at hlt
        rcases hr with rfl | hr
        · omega
        · rw [zz_initBal _ hxq'] at hlt; omega
      · rw [hbI] at hlt; omega
  have hpeer := hA.peerOk i hi
  have hown' : S'.owner = upd S.owner x (some batch) := hH.owner
  have hownO : ∀ y, y ≠ x → S'.owner y = S.owner y := by
    intro y hy; rw [hown', upd_other _ _ _ _ hy]
  have hwf : Inv.wf S' := by
    obtain ⟨w1', w2', w3', w4', w5', w6', w7', w8'⟩ := s1
    refine ⟨fun r hr => by rw [(hfl r).1]; exact w1' r hr, fun r hr y w2 h2 => ?_,
      fun r hr q hq => ?_,
      fun r hr q k p hk => ?_, fun r hr q hq n' hn' => ?_, fun fr' to hne => ?_,
      fun fr' to n' hn' => ?_, fun r b' hb' => ?_⟩
    · rcases R1 r y w2 h2 with ⟨rfl, rfl, rfl⟩ | ⟨h, -⟩
      · refine ⟨W8, hxq', hxM, fun _ => by rw [W6]; exact hdeps,
          fun lb2 hl2 _ => ?_, fun hq => by rw [W7]; simp, fun lb2 ps hl2 hps => ?_⟩
        · rw [W7] at hl2; cases hl2; rw [k12]; exact hdeps
        · rw [W7] at hl2; cases hl2; rw [hown', upd_same]; rw [k6] at hps; exact hps
      · obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := w2' r hr y w2 h
        exact ⟨g1, g2, g3, g4, g5, g6, fun lb ps hlb hps => by
          rw [hownO y (hyx r y w2 hr h)]; exact g7 lb ps hlb hps⟩
    · rw [hcrt]; split
      · rename_i h; obtain ⟨rfl, -⟩ := h
        exact ⟨by omega, by rw [hn.2.1]; exact hxM⟩
      · exact w3' r hr q hq
    · have grow : ∀ y, (S.rep r).inst y ≠ none → (S'.rep r).inst y ≠ none := by
        intro y hy hy'
        obtain ⟨w1, h1⟩ := Option.ne_none_iff_exists'.mp hy
        rw [R2 r y w1 h1] at hy'; cases hy'
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
          ⟨hxq', fun _ => by rw [hσ]; simp [upd_apply, hn.2.1]⟩
          ⟨hxq', fun h => by simp [zz] at h⟩ q k p hk
        rw [hH.rep_self]
        exact ⟨this.1.1, this.1.2, this.2.2⟩
      · rw [hH.rep_other hr'] at hk ⊢
        exact w4' r hr q k p hk
    · rw [(hfl r).2.2.1] at hn'
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
        exact ⟨w1, R2 r y w1 h1, hle⟩
      · exact ⟨w', R3, by rw [W2]; exact Int.le_refl _⟩
  have hcountP : (S'.hist.filter (· = (i, .phase1 x b ⟨cmds, W32 (-1), deps⟩))).length = 1 := by
    rw [hhist, List.filter_append, List.length_append]
    have h0 : (S.hist.filter (· = (i, .phase1 x b ⟨cmds, W32 (-1), deps⟩))).length = 0 := by
      simp only [List.length_eq_zero_iff, List.filter_eq_nil_iff, decide_eq_true_eq]
      intro a ha hae; subst hae; exact hnoph i _ ha
    rw [h0]; simp
  have hown : Inv.ballotOwner S' := by
    obtain ⟨o1, o2, o3, o4, o5, o6⟩ := s6
    refine ⟨fun r y c he => ?_, fun r y c u he => ?_, fun r y c u he => ?_,
      fun r to m' hm' => ?_, fun r to m' hm' => ?_, fun r to m' hm' => ?_⟩
    · rcases hmkO r y c he with h | ⟨hr, hy, hc⟩
      · refine ⟨(o1 r y c h).1, ?_⟩
        rw [hH.count_eq (fun hr => hnotEold r _ h (fun _ _ _ h => by cases h) hr)]
        exact (o1 r y c h).2
      · rw [hr, hy, hc]
        refine ⟨Or.inl ⟨by rw [hbI, zz_initBal x hxq', hxq], hxq.symm⟩, ?_⟩
        rw [hhist, List.filter_append, List.length_append]
        have h0 : (S.hist.filter (· = (i, .makeBallot x b))).length = 0 := by
          simp only [List.length_eq_zero_iff, List.filter_eq_nil_iff, decide_eq_true_eq]
          intro a ha hae; subst hae; exact hnoMk i _ ha
        rw [h0]; simp
    · rcases hphO r y c u he with h | ⟨rfl, rfl, rfl, rfl⟩
      · exact hH.evBefore_old (o2 r y c u h)
      · exact (hH.evBefore_iff _ _ _ _).mpr
          (Or.inr (Or.inr ⟨rfl, rfl, 0, 1, by omega, rfl, rfl⟩))
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
          rcases hm' with hm' | hm' | hm' | hm' <;> cases hm'
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
          (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)⟩
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
          (fun _ _ _ h => by cases h) (fun _ _ h => by cases h), Or.inl ⟨to, ?_, rfl⟩⟩
        rcases (hmsgs _ _ _).mp hm' with h | ⟨-, h, -⟩
        · exact h
        · cases h
      · exact ⟨hold r _ he (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
          (fun _ _ _ h => by cases h) (fun _ _ h => by cases h), Or.inr rfl⟩
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
        rw [hy, hw] at h1'; cases h1'
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
      refine ⟨by rw [k1]; exact hH.ev_new (by simp), by rw [k1, k2, show zz (W32 (-1)) = -1 by decide]; omega,
        k5, fun c u hv0 => ?_, fun _ c2 => (by rw [k7] at c2; exact absurd rfl c2),
        ⟨[], List.nodup_nil, by rw [k7]; rfl, fun a m' h => by cases h⟩,
        ⟨[], List.nodup_nil, by rw [k8]; rfl, fun a h => by cases h⟩,
        fun c1 => (by rw [k3] at c1; cases c1), fun c1 => (by rw [k4] at c1; cases c1)⟩
      rw [k1]
      rcases hv0 with hv0 | hv0
      · rcases hphO _ _ c u hv0 with h | ⟨-, -, rfl, -⟩
        · exact absurd rfl (hfrE _ _ h)
        · exact Int.le_refl _
      · exact absurd rfl (hfrE _ _ (haO _ _ _ _ hv0))
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
      · rw [hlx, (hfl r).2.2.2]; exact p2 r hr k
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
      rcases h with h | h | h | h
      · cases h
      · cases h
      · cases h
      · simp only [Event.attrsRec.injEq] at h; obtain ⟨hz, hcz, hdz⟩ := h
        subst z; subst cz; subst d
        have hyq : y.q < nR := (hA.crtEv _ e y he (recorded_instOf hrec)).1
        rw [hd]
        exact ua_covers hA hi he hrec hyq σu hσu hσus.1 hσus.2 cmds (W32 0) _ (by simp) hint
    · subst hr
      have hp2 : p2 < 4 := by
        have := (List.getElem?_eq_some_iff.mp h2).1; simpa using this
      rcases p1 with _ | _ | _ | p1
      · simp at h1; subst h1; simp [Event.recorded] at hrec
      · simp at h1; subst h1; simp [Event.recorded] at hrec
      · simp at h1; subst h1; simp [Event.recorded] at hrec
      · omega
  have hops : S'.ops = S.ops := hH.ops
  have hgex : S'.gexec = S.gexec := hH.gexec
  have hslots : Inv.slots S' := by
    refine ⟨fun y u hu => ?_, fun y ps h p hp => ?_⟩
    · have hu0 := (hcv' _ _).mp hu
      have hy : y ≠ x := by rintro rfl; exact hnocv u hu0
      rw [hownO y hy]; exact s22.1 y u hu0
    · rw [hops]
      by_cases hy : y = x
      · subst hy; rw [hown', upd_same] at h; cases h
        rw [hxq]; exact hA.exec.chanOps i p (hsub.subset hp)
      · rw [hownO y hy] at h; exact s22.2 y ps h p hp
  -- slots of a global sequence are not `x`'s (it is not decided)
  have hgx : ∀ k e, e ∈ S.gexec k → e.1.1 ≠ x := by
    intro k e he hx
    obtain ⟨-, -, -, -, u, hu, -⟩ := s23.2.2.2.1 k e he
    rw [hx] at hu; exact hnocv u hu
  have hsoO : ∀ s, s.1 ≠ x → S'.slotOp s = S.slotOp s := by
    intro s hs; simp only [Sys.slotOp, hownO _ hs]
  have hsoX : ∀ s, s.1 = x → S'.slotOp s = batch[s.2]? := by
    intro s hs; simp only [Sys.slotOp, hs, hown', upd_same, Option.bind_some]
  have hco : Inv.clientOps S' :=
    ExecOrd.clientOps_frame s23 hops hgex hH.fired (fun k e he => hsoO _ (hgx _ _ he))
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
      exact ⟨w1, lb1, R2 to y w1 h1, hl1⟩
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
      exact ⟨w1, R2 r _ w1 h1, hle⟩
    · rcases hvoteO r y c st u h3 with h3 | ⟨rfl, rfl, rfl, -, rfl⟩ <;>
        rcases hvoteO r y c st' u' h4 with h4 | ⟨-, h5, h6, -, rfl⟩
      · exact c6' r y c st st' u u' h1 h2 h3 h4
      · subst h5 h6; exact absurd h3 (hnovPA r st u h1)
      · exact absurd h4 (hnovPA r st' u' h2)
      · rfl
    · exact c7' y u m' e (hold _ _ h1 (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
        (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)) ((hprepR _ m' e).mp h2) h3
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
  -- the execution conjuncts: the batch's tokens move from the channel to `x`'s slots
  have hdead : ∀ y, S.propDead y → S'.propDead y := by
    rintro y ⟨⟨v, c, h1, h2, h3⟩, h4⟩
    have hy : y ≠ x := by rintro rfl; exact hnocv v h1
    refine ⟨⟨v, c, (hcv' _ _).mpr h1, h2, h3⟩, fun w2 lb2 hw2 hl2 => ?_⟩
    rw [hrep, if_neg (fun h => hy h.2)] at hw2
    exact h4 w2 lb2 hw2 hl2
  have hsp := chan_split hsub (chanOnce_nodup hA.exec.chanOnce i)
  have hX' : InvExec S' := by
    have hX := hA.exec
    have hes : ∀ r, S'.eseq r = S.eseq r := by
      intro r; simp only [Sys.eseq, hH.execLog, hH.execCur]
    have hchan' : S'.proposeChan = upd S.proposeChan i ((S.proposeChan i).diff batch) := hchan
    have hsubC := upd_sub S i _ (List.diff_sublist (S.proposeChan i) batch)
    refine ⟨fun r hr a c ha hac => ?_, fun r hr l1 l2 a c he h1 h2 ht => ?_, fun k e he => ?_,
      fun s s' p p' hne h1 h2 h3 => ?_, fun j p s p' h1 h2 h3 => ?_, ?_, fun j p h => ?_⟩
    · rw [hes] at ha ⊢; rw [hdE] at hac; exact hX.reach r hr a c ha hac
    · rw [hes] at he; rw [hdE] at ht ⊢; rw [hsO]; exact hX.ord r hr l1 l2 a c he h1 h2 ht
    · rw [hgex] at he
      obtain ⟨r, hr, h⟩ := hX.gloc k e he
      exact ⟨r, hr, by rw [hlx]; exact h⟩
    · -- two slots of one op
      by_cases hs : s.1 = x <;> by_cases hs' : s'.1 = x
      · exfalso
        rw [hsoX s hs] at h1; rw [hsoX s' hs'] at h2
        apply hne
        have g1 : (batch.map (·.cid))[s.2]? = some p.cid := by rw [List.getElem?_map, h1]; rfl
        have g2 : (batch.map (·.cid))[s'.2]? = some p.cid := by
          rw [List.getElem?_map, h2, h3]; rfl
        have hidx : s.2 = s'.2 :=
          hsp.1.eq_of_getElem?_eq (List.getElem?_eq_some_iff.mp g1).1 (by rw [g1, g2])
        exact Prod.ext (hs.trans hs'.symm) hidx
      · rw [hsoX s hs] at h1; rw [hsoO s' hs'] at h2
        exact Or.inr (hdead _ (hX.tokChan i p s' p' (hsub.subset (List.mem_of_getElem? h1)) h2 h3.symm))
      · rw [hsoO s hs] at h1; rw [hsoX s' hs'] at h2
        exact Or.inl (hdead _ (hX.tokChan i p' s p (hsub.subset (List.mem_of_getElem? h2)) h1 h3))
      · rw [hsoO s hs] at h1; rw [hsoO s' hs'] at h2
        exact (hX.tokSlot s s' p p' hne h1 h2 h3).imp (hdead _) (hdead _)
    · -- a proposal still in a channel
      rw [hchan'] at h1
      by_cases hs : s.1 = x
      · exfalso
        rw [hsoX s hs] at h2
        have hp' : p' ∈ batch := List.mem_of_getElem? h2
        by_cases hj : j = i
        · subst hj; rw [upd_same] at h1
          exact hsp.2 p h1 p' hp' h3.symm
        · rw [upd_other _ _ _ _ hj] at h1
          exact hj (chanOnce_disj hX.chanOnce h1 (hsub.subset hp') h3.symm)
      · rw [hsoO s hs] at h2
        exact hdead _ (hX.tokChan j p s p' ((hsubC j).subset h1) h2 h3)
    · rw [hchan']; exact chanOnce_sub hX.chanOnce hsubC
    · rw [hchan'] at h; rw [hops]
      exact hX.chanOps j p ((hsubC j).subset h)
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
        · exact absurd rfl (hfrE _ _ h)
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
        · exact hfrE _ _ h rfl
        · cases h
      · exact hA.accKeep r hr y w2 h c u (hvO _ _ _ _ _ hv0 hne) hle
    recCommit := fun r hr y w2 h2 hs => by
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · exact absurd hs hnc'
      · obtain ⟨c, u, d1, d2⟩ := hA.recCommit r hr y w2 h hs
        exact ⟨c, u, hH.ev_old d1, d2⟩
    commitRec := fun r y c u hr he => by
      have h := hold _ _ he (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
        (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)
      obtain ⟨w1, h1, hs⟩ := hA.commitRec r y c u hr h
      exact ⟨w1, R2 r y w1 h1, hs⟩
    fastCommitEv := fun r y u he => by
      obtain ⟨d1, c, d2⟩ := hA.fastCommitEv r y u
        (hold _ _ he (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
          (fun _ _ _ h => by cases h) (fun _ _ h => by cases h))
      exact ⟨d1, c, hH.ev_old d2⟩
    makerLb := fun r y c hr he => by
      rcases hmkO r y c he with h | ⟨rfl, rfl, rfl⟩
      · obtain ⟨w1, lb1, h1, hl1, hle⟩ := hA.makerLb r y c hr h
        exact ⟨w1, lb1, R2 r y w1 h1, hl1, hle⟩
      · exact ⟨w', lbN, R3, W7, by rw [k1]; exact Int.le_refl _⟩
    lastLeBal := fun r hr y w2 lb2 h2 hl2 => by
      rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, rfl, rfl⟩ | ⟨h, -⟩
      · rw [k1, W2]; exact Int.le_refl _
      · exact hA.lastLeBal r hr y w2 lb2 h hl2
    peerOk := fun r hr => by rw [(hfl r).2.1]; exact hA.peerOk r hr
    crtOwn := fun r hr q hq => by
      by_cases hrq : r = i ∧ q = i
      · obtain ⟨rfl, rfl⟩ := hrq; exact Int.le_refl _
      · have h1 : (S'.rep r).crtInstance q = (S.rep r).crtInstance q := by
          rw [hcrt, if_neg hrq]
        rw [h1]; exact Int.le_trans (hA.crtOwn r hr q hq) (hcrtle q q)
    crtRec := fun r hr y w2 h2 => by
      rcases R1 r y w2 h2 with ⟨rfl, rfl, -⟩ | ⟨h, -⟩
      · rw [hxq, hcrtI]; exact Int.le_refl _
      · exact Int.le_trans (hA.crtRec r hr y w2 h) (hcrtle _ _)
    crtMsg := fun fr to m' y hm' hy => by
      rcases (hmsgs _ _ _).mp hm' with hm' | ⟨hfi, rfl, -⟩
      · exact Int.le_trans (hA.crtMsg fr to m' y hm' hy) (hcrtle _ _)
      · simp only [Msg.instOf, Option.some.injEq] at hy
        rw [m2] at hy; subst hy; rw [hxq, hcrtI]; exact Int.le_refl _
    crtEv := fun r e y he hy => by
      rcases (hE r e).mp he with h | ⟨-, rfl | rfl | rfl | rfl⟩
      · obtain ⟨d1, d2⟩ := hA.crtEv r e y h hy
        exact ⟨d1, Int.le_trans d2 (hcrtle _ _)⟩
      all_goals
        simp only [Event.instOf, Option.some.injEq] at hy; subst hy
        exact ⟨hxq', by rw [hxq, hcrtI]; exact Int.le_refl _⟩
    ownRow := fun q hq j hj => by
      by_cases hc : q = i ∧ j = x.i
      · obtain ⟨hq', hj'⟩ := hc
        have hx' : (⟨q, j⟩ : InstId) = x := by rw [hq', hj', ← hxq]
        exact ⟨w', lbN, by rw [hx', hq']; exact R3, W7⟩
      · have hj' : (j : Int) ≤ zz ((S.rep q).crtInstance q) := by
          rw [hcrt] at hj
          by_cases hq' : q = i
          · subst hq'
            simp only [and_self, if_true] at hj
            have h1 : j ≠ x.i := fun h => hc ⟨rfl, h⟩
            have h2 : (j : Int) ≠ (x.i : Int) := by exact_mod_cast h1
            rw [hn.2.2] at hj
            omega
          · simpa [hq'] using hj
        obtain ⟨w1, lb1, h1, hl1⟩ := hA.ownRow q hq j hj'
        exact ⟨w1, lb1, R2 q _ w1 h1, hl1⟩
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
      rw [hce]
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
        exact ⟨w1, lb1, R2 r y w1 h1', hl1, hlt'⟩
      · exact Or.inr ⟨d1, hallP _ _ _ rfl d2⟩
    commitBal := fun fr to m' hm' => by
      rcases (hmsgs _ _ _).mp hm' with hm' | ⟨-, h, -⟩
      · exact hA.commitBal fr to m' hm'
      · cases h
    sentPR := fun r to m' he => by
      have he0 := hold _ _ he (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
        (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)
      obtain ⟨d1, d2, d3⟩ := hA.sentPR r to m' he0
      refine ⟨fun hr => ?_, fun c st u hb' => ?_, fun to' m2 hb' hy => d3 to' m2 ?_ hy⟩
      · obtain ⟨w1, h1, hle⟩ := d1 hr
        exact ⟨w1, R2 r _ w1 h1, hle⟩
      · obtain ⟨pp, pp', hlt', h1, h2⟩ := hb'
        rcases hvoteO r _ c st u (List.mem_of_getElem? h2) with h | ⟨rfl, hy, rfl, -, -⟩
        · exact d2 c st u (hevB _ _ _ _ ⟨pp, pp', hlt', h1, h2⟩ h (fun _ _ _ h => by cases h))
        · obtain ⟨w1, h1', hle⟩ := d1 hi
          rw [hy, hw] at h1'; cases h1'
      · obtain ⟨pp, pp', hlt', h1, h2⟩ := hb'
        exact hevB _ _ _ _ ⟨pp, pp', hlt', h1, h2⟩
          (hold _ _ (List.mem_of_getElem? h2) (fun _ _ _ h => by cases h)
            (fun _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)) (fun _ _ _ h => by cases h)
    confCover := fun r hr e y cy he hrec c hc' => by
      rcases (hE r e).mp he with h | ⟨hri, rfl | rfl | rfl | rfl⟩
      · exact confLe_cover (hconfLe r) (hA.confCover r hr e y cy h hrec c hc')
      · cases hrec
      · cases hrec
      · cases hrec
      · simp only [Event.recorded, Option.some.injEq, Prod.mk.injEq] at hrec
        obtain ⟨rfl, rfl⟩ := hrec
        subst hri
        rw [hH.rep_self, hconf.2]
        obtain ⟨p, hp, h1, h2⟩ := uc_cov σb cmds x.q n seq c hc'
        have hz : (x.i : Int) = zz n := by rw [← hn.2.1]; exact toN_of_zz n hn.1
        exact ⟨p, hp, by rw [hz]; exact h1, fun h => by rw [hz]; exact h2 h⟩
    classWf := fun r hr => by
      have hgrow : ∀ y, (S.rep i).inst y ≠ none → σ'.inst y ≠ none := by
        intro y hy
        obtain ⟨w1, h1⟩ := Option.ne_none_iff_exists'.mp hy
        rw [← hH.rep_self, R2 i y w1 h1]; simp
      by_cases hri : r = i
      · subst hri; rw [hH.rep_self]
        obtain ⟨h1, h2, h3, h4, h5⟩ := hcls
        have hb : AuxProof.ClsWf σb :=
          AuxProof.clsWf_keep (hA.classWf r hr) h1 h2 (fun y hy => by rw [h3]; exact hgrow y hy)
        have hu := ConfProof.clsWf_uc hb cmds x.q n seq (fun _ => by
          have : (⟨x.q, toN n⟩ : InstId) = x := by rw [hn.2.1]
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
      rcases (hE r e).mp he with h | ⟨hri, rfl | rfl | rfl | rfl⟩
      · exact AuxProof.clsCov_mono hle (hA.classCover r hr e y cy h hrec)
      · cases hrec
      · cases hrec
      · cases hrec
      · simp only [Event.recorded, Option.some.injEq, Prod.mk.injEq] at hrec
        obtain ⟨rfl, rfl⟩ := hrec
        subst hri
        have hz : zz n = (x.i : Int) := by rw [← hn.2.1]; exact (toN_of_zz n hn.1).symm
        rw [hH.rep_self]; intro c hc'; rw [hcls.2.2.2.1, hcls.2.2.2.2]
        exact ConfProof.clsCov_uc σb cmds n seq x hz c hc'
    paAttrs := fun r y c st u hst hv0 => by
      rcases hvoteO r y c st u hv0 with h | ⟨rfl, rfl, rfl, -, rfl⟩
      · exact hH.ev_old (hA.paAttrs r y c st u hst h)
      · exact hH.ev_new (by simp)
    valOk := fun r y c u hv0 => by
      rcases hv0 with hv0 | hv0
      · rcases hphO r y c u hv0 with h | ⟨-, rfl, rfl, rfl⟩
        · have hy : y ≠ x := by rintro rfl; exact hfrE _ _ h rfl
          rw [hownO y hy]; exact hA.valOk r y c u (Or.inl h)
        · exact Or.inr ⟨batch, by rw [hown', upd_same], hcmd⟩
      · have h := haO _ _ _ _ hv0
        have hy : y ≠ x := by rintro rfl; exact hfrE _ _ h rfl
        rw [hownO y hy]; exact hA.valOk r y c u (Or.inr h)
    cmdsNe := by
      obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hA.cmdsNe
      refine ⟨fun fr to m' hm' cs hcs => ?_,
        fun r hr y w2 cs h2 hc' => ?_, fun r hr y w2 lb2 cs h2 hl2 hc' => ?_,
        fun fr to m' hm' => ?_,
        fun r m' he => n5 r m' (hold _ _ he (fun _ _ _ h => by cases h)
          (fun _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)),
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
        (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)) hs
    selfRaw := fun r m' he => hA.selfRaw r m'
      (hold _ _ he (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
        (fun _ _ _ h => by cases h) (fun _ _ h => by cases h))
    pm := by
      have hP := hA.pm
      have hmono : ∀ r e, S.ev r e → S'.ev r e := fun r e h => hH.ev_old h
      have hsent : ∀ fr to (m' : Msg), m' ∈ S.sent fr to → m' ∈ S'.sent fr to := by
        intro fr to m' h; rw [hH.sent]; exact h
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
      have hbalP : ∀ r y w1, (S.rep r).inst y = some w1 →
          ∃ w2, (S'.rep r).inst y = some w2 ∧ zz w1.bal ≤ zz w2.bal :=
        fun r y w1 h => ⟨w1, R2 r y w1 h, Int.le_refl _⟩
      have hcm : ∀ r y c u, S'.ev r (.commit y c u) → S.ev r (.commit y c u) :=
        fun r y c u h => hold _ _ h (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
          (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)
      have hrc : ∀ fr to, S'.sent fr to ++ S'.outbox fr to = S.sent fr to ++ S.outbox fr to := by
        intro fr to; have h := pmp_rcpt hH hidle.1 fr to; exact h
      have hRx : S'.paRcpt x = [] := by
        unfold Sys.paRcpt
        rw [List.filter_eq_nil_iff]
        intro a _ ha
        rw [hrc] at ha
        obtain ⟨m0, hm0, hp0⟩ := List.any_eq_true.mp ha
        have hm0' : m0 ∈ S.msgs x.q a := by
          unfold Sys.msgs; exact List.mem_append_left _ hm0
        cases m0 with
        | preAccept p =>
          simp only [Msg.isPAat, decide_eq_true_eq] at hp0
          exact hfrM _ _ _ hm0' (by simp only [Msg.instOf, hp0.1])
        | _ => simp [Msg.isPAat] at hp0
      exact {
        arOk := PMProof.arOk_frame hP (fun a r m' h => hmsgO _ _ _ h (fun _ h => by cases h)) haO
          (fun q y c v h => by
            rcases hvoteO q y c _ v h with h | ⟨-, -, -, h, -⟩
            · exact Or.inl h
            · exact absurd (h ▸ hPA) hnotACC)
          hmono hcv hbalP
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
            rcases (hE r _).mp hv with h | ⟨-, h | h | h | h⟩
            · rw [← h2'] at h; exact absurd h (hnoph r v)
            · cases h
            · rw [← h2'] at h; simp only [Event.phase1.injEq] at h; obtain ⟨-, -, rfl⟩ := h
              rw [k10]
            · cases h
            · cases h
          · exact hP.paCmds r hr y w2 lb2 h hl2 hs v (hpO _ _ _ _ hv hne)
        paSent := fun y w2 lb2 hq h2 hl2 hlt' => by
          rcases hlbv _ y w2 lb2 h2 hl2 with ⟨-, rfl, -, rfl⟩ | ⟨h, hne⟩
          · rw [hpas]
            refine ⟨Nat.zero_le _, fun B' hB' _ _ => ?_, by rw [hRx]; exact Nat.zero_le _⟩
            rw [hH.pending, hxq, upd_same] at hB'
            obtain ⟨rfl, -, -⟩ := norm_some hB'
            refine ⟨?_, by rw [hBs]; rfl, by rw [hBn]; exact Nat.le_refl _⟩
            rw [hBm]; simp only [Msg.isPAat, decide_eq_true_eq]
            exact ⟨m2, by rw [m7, hbI]⟩
          · obtain ⟨g1, g2, g3⟩ := hP.paSent y w2 lb2 hq h hl2 hlt'
            refine ⟨g1, fun B' hB' hBx' ht => ?_, ?_⟩
            · rw [hH.pending] at hB'
              by_cases hyq : y.q = i
              · rw [hyq, upd_same] at hB'
                obtain ⟨rfl, -, -⟩ := norm_some hB'
                exact absurd ⟨hyq, by rw [← hBx', hBx]⟩ hne
              · rw [upd_other _ _ _ _ hyq] at hB'; exact g2 B' hB' hBx' ht
            · have he : S'.paRcpt y = S.paRcpt y := by
                unfold Sys.paRcpt; simp only [hrc]
              rw [he]; exact g3
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
          rcases hvoteO r y _ st v hv with h | ⟨hr, rfl, -, -, -⟩
          · obtain ⟨p, h1, h2, h3⟩ := hP.paVoteMsg r y st v hst hne h
            exact ⟨p, hsent _ _ _ h1, h2, h3⟩
          · exact absurd (hr.trans hxq.symm) hne
        parNoPA := fun a r m' hm' hn st u hst hv => by
          have hm0 := hPAR _ _ _ hm'
          rcases hvoteO a _ _ st u hv with h | ⟨-, hy, -, -, -⟩
          · exact hP.parNoPA a r m' hm0 hn st u hst h
          · exact hfrM _ _ _ hm0 (by simp only [Msg.instOf]; rw [← hy])
        aeF := fun r hr y w2 lb2 h2 hl2 hs hae' => by
          rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, -, rfl⟩ | ⟨h, -⟩
          · rw [hae] at hae'; cases hae'
          · obtain ⟨a, a', m1, m1', g1, g2, g3, g4, g5, g6, g7⟩ :=
              hP.aeF r hr y w2 lb2 h hl2 hs hae'
            exact ⟨a, a', m1, m1', hsent _ _ _ g1, hsent _ _ _ g2, g3, g4, g5, g6, g7⟩
        repLead := PMProof.repLead_frame hP (fun r m' e h => (hprepR r m' e).mp h) hbalP
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
          · refine Or.inr ⟨⟨stPREACCEPTED, ⟨cmds, seq, deps⟩, Or.inl rfl, hH.ev_new (by simp), rfl⟩, fun b' hr hlt _ _ => ?_⟩
            rw [hbI] at hlt
            rcases hr with rfl | hr
            · omega
            · rw [zz_initBal _ hxq'] at hlt; omega)
        accSup := CmdSafeProof.accSup_frame hP hmono haO },
    ownerCrt := fun y ps h => by
      by_cases hy : y = x
      · subst hy; exact ⟨hxq', by rw [hxq, hcrtI]; exact Int.le_refl _⟩
      · rw [hownO y hy] at h
        obtain ⟨d1, d2⟩ := hA.ownerCrt y ps h
        exact ⟨d1, Int.le_trans d2 (hcrtle _ _)⟩
    execLo := AuxProof.execLo_of_eq hA.execLo (fun r _ => (hfl r).2.2.1)
    exec := hX' }

/-- The new instance's number: `crtInstance + 1` without overflow, below the row's capacity. -/
theorem crt_succ (c : w32) (h0 : -1 ≤ zz c) (h1 : toN c + 1 < MAX_INSTANCE)
    (hnf : ¬ (W32 (MAX_INSTANCE - 1 : Nat)).sle (c + 1) = true) :
    zz (c + 1) = zz c + 1 ∧ zz (c + 1) + 1 < MAX_INSTANCE := by
  have hle : ¬ zz (W32 (MAX_INSTANCE - 1 : Nat)) ≤ zz (c + 1) := by
    intro h; apply hnf; simp only [zz, sint.Z] at h; exact BitVec.sle_iff_toInt_le.mpr h
  have hW : zz (W32 (MAX_INSTANCE - 1 : Nat)) = MAX_INSTANCE - 1 := by
    rw [zz_W32] <;> simp [MAX_INSTANCE]
  rw [hW] at hle
  have hadd : zz (c + 1) = zz c + 1 := by
    simp only [zz, sint.Z, toN, MAX_INSTANCE] at h0 h1 ⊢
    rw [BitVec.toInt_add_of_not_saddOverflow]
    · simp
    · simp only [BitVec.saddOverflow]; simp; omega
  refine ⟨hadd, ?_⟩
  simp only [MAX_INSTANCE] at hle ⊢; omega

/-- The state after `Sys.propose`'s channel and owner update. -/
def propS2 (S : Sys) (i : Nat) (x : InstId) (batch : List Proposal) : Sys :=
  { S with proposeChan := upd S.proposeChan i ((S.proposeChan i).diff batch),
           owner := upd S.owner x (some batch) }

/-- **`handlePropose` keeps the invariant.** -/
theorem inv_step_propose' (S : Sys) (i : Nat) (batch : List Proposal) (hS : Inv S) (hi : i < nR)
    (hidle : S.idle i) (hb : batch ≠ []) (hsub : batch.Subperm (S.proposeChan i)) :
    Inv (S.propose i batch) := by
  by_cases hfull : rowFull (S.rep i) = true
  · exact inv_propose_full S i batch hS hfull
  have hid : (S.rep i).id = i := hS.1.1.1 i hi
  obtain ⟨hc0, hc1⟩ := hS.1.1.2.2.1 i hi i hi
  have hnf : ¬ (W32 (MAX_INSTANCE - 1 : Nat)).sle ((S.rep i).crtInstance i + 1) = true := by
    have := hfull; simp only [rowFull, hid] at this; exact this
  obtain ⟨hzn, hzM⟩ := crt_succ _ hc0 hc1 hnf
  generalize hn : (S.rep i).crtInstance i + 1 = n at hzn hzM
  have hn0 : 0 ≤ zz n := by omega
  generalize hx : (⟨i, toN n⟩ : InstId) = x
  have hxq : x.q = i := by rw [← hx]
  have hxi : (x.i : Int) = zz n := by rw [← hx]; exact toN_of_zz n hn0
  generalize hσ1 : ({ S.rep i with crtInstance := upd (S.rep i).crtInstance i n } : RState) = σ1
  generalize hcm : batch.map (·.cmd) = cmds
  generalize hr : startPhase1 σ1 cmds x (W32 i) n (W32 i) (some batch) = r
  have hP : hPropose (S.rep i) batch = (r.1, Out.ev (.makeBallot x (W32 i)) :: r.2) := by
    rw [← hr, ← hσ1, ← hcm, ← hx, ← hn]; unfold hPropose; rw [if_neg hfull]; simp only [hid]
  generalize hS2 : propS2 S i x batch = S2
  have hstep : S.propose i batch = S2.applyStep i (r.1, Out.ev (.makeBallot x (W32 i)) :: r.2) := by
    rw [← hS2, ← hP]; unfold Sys.propose; simp only [hfull, hid, hx, hn]; rfl
  rw [hstep]
  have hidle2 : S2.idle i := by rw [← hS2]; exact hidle
  have hH := RecoverProof.hs_apply S2 i r.1 (Out.ev (.makeBallot x (W32 i)) :: r.2) hidle2
  have hchan : (S2.applyStep i (r.1, Out.ev (.makeBallot x (W32 i)) :: r.2)).proposeChan =
      S2.proposeChan := by
    funext fr; rw [Sys.applyStep_proposeChan, ← hr, List.filterMap_cons, ExecOrd.rp_sp1]; simp [Out.reprop]
  generalize S2.applyStep i (r.1, Out.ev (.makeBallot x (W32 i)) :: r.2) = S' at hH hchan ⊢
  have hσ1c : σ1.conflicts = (S.rep i).conflicts := by rw [← hσ1]
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := RecPhase1Proof.sp1_spec σ1 cmds x (W32 i) n (W32 i)
    (some batch)
  rw [hr] at g1 g2 g3 g4 g5 g6 g7 g8
  rw [g8] at hH
  have hbI : W32 (i : Int) = initBal x := by rw [initBal, hxq]
  have hrid : r.1.id = i := by rw [g2, ← hσ1]; exact hid
  have hσ1i : σ1.inst = (S.rep i).inst := by rw [← hσ1]
  have hxM : x.i + 1 < MAX_INSTANCE := by omega
  have hW : zz (W32 (i : Int)) = i := zz_W32 _ (by omega) (by simp [nR] at hi; omega)
  refine inv_propose_start S S2 _ i batch r.1 σ1
    (σ1.setInst x (RecPhase1Proof.p1Rec x cmds (W32 i)
      (updateAttributes σ1 cmds (W32 0) (List.replicate nR (W32 (-1)))).1
      (updateAttributes σ1 cmds (W32 0) (List.replicate nR (W32 (-1)))).2.1
      (RecPhase1Proof.sp1Lb cmds (W32 i)
        (updateAttributes σ1 cmds (W32 0) (List.replicate nR (W32 (-1)))).2.1 (some batch))))
    x (RecPhase1Proof.sp1Lb cmds (W32 i)
        (updateAttributes σ1 cmds (W32 0) (List.replicate nR (W32 (-1)))).2.1 (some batch))
    (W32 i) n cmds (updateAttributes σ1 cmds (W32 0) (List.replicate nR (W32 (-1)))).1
    (updateAttributes σ1 cmds (W32 0) (List.replicate nR (W32 (-1)))).2.1
    (bcastPreAcceptOf r.1 x (preAcceptOf r.1 (W32 i) n (RecPhase1Proof.sp1Lb cmds (W32 i)
        (updateAttributes σ1 cmds (W32 0) (List.replicate nR (W32 (-1)))).2.1 (some batch))))
    (preAcceptOf r.1 (W32 i) n (RecPhase1Proof.sp1Lb cmds (W32 i)
        (updateAttributes σ1 cmds (W32 0) (List.replicate nR (W32 (-1)))).2.1 (some batch)))
    hS hi hidle hsub hb
    hcm.symm hS2.symm hxq hbI rfl hσ1c ⟨by rw [← hσ1], by rw [← hσ1]⟩ hH hchan ?_ ?_ ?_ ?_ ?_ ?_ ?_
    hxM ?_
  · refine ⟨rfl, rfl, ?_, rfl, rfl⟩
    simp only [bcastPreAcceptOf]; rw [g3, ← hσ1]
  · refine ⟨by simp only [preAcceptOf]; rw [hrid], ?_, show 0 ≤ zz (W32 (i : Int)) by rw [hW]; omega,
      show zz (W32 (i : Int)) < nR by rw [hW]; exact_mod_cast hi, hn0, ?_, rfl, rfl, rfl, rfl⟩
    · show (⟨toN (W32 (i : Int)), toN n⟩ : InstId) = x
      rw [toN_W32 i hi, ← hx]
    · show toN n + 1 < MAX_INSTANCE
      have : toN n = x.i := by rw [← hx]
      rw [this]; exact hxM
  · rw [g1, hσ1i]
  · refine ⟨by rw [g2, ← hσ1], by rw [g3, ← hσ1], by rw [g4, ← hσ1], by rw [g5, ← hσ1],
      by rw [g6, ← hσ1]⟩
  · exact ⟨by simp [RState.setInst, hσ1c], g7⟩
  · exact ⟨by rw [← hσ1]; rfl, by rw [← hσ1]; rfl, by rw [g1]; rfl,
      by rw [← hr]; exact (RecPhase1Proof.sp1_cls _ _ _ _ _ _ _).1,
      by rw [← hr]; exact (RecPhase1Proof.sp1_cls _ _ _ _ _ _ _).2⟩
  · exact ⟨hn0, by rw [← hx], hzn⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end ProposeProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
