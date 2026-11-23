/-
A handler step of replica `i` that commits its instance `x` with a value `v` that may be new
(not yet decided), and broadcasts the Commit: the record becomes COMMITTED with `v` at ballot `b`
(its `vbal` kept), the bookkeeping becomes a COMMITTED, non-preparing one, the events
`commit x b v` (and, on the fast path, `fastCommit x v`) are logged and the Commit broadcast is
left pending (`inv_commit_new`). The new-value obligations (agreement, choice, witnesses, slots,
the proposal facts of `InvPM`) are hypotheses. Used by `handlePreAcceptReply`'s fast path and
`handleAcceptReply`'s commit.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.RecAccept

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace RecCommitNewProof

open HStepProof HLocal SafeProof AuxProof RecCommitProof RecAcceptProof

/-- The committed record (its `vbal` kept). -/
def comNew (w : InstRec) (lb' : LbRec) (b : w32) (v : Val) : InstRec :=
  { w with cmds := some v.cmds, bal := b, seq := v.seq, deps := v.deps, status := stCOMMITTED,
           lb := some lb' }

/-- The bookkeeping after the commit (its counted replies are given in `S'` terms). -/
def LbComNew (lb lb' : LbRec) (v : Val) : Prop :=
  lb'.lastTriedBallot = lb.lastTriedBallot ∧ zz lb'.ballot ≤ zz lb.lastTriedBallot ∧
  lb'.status = stCOMMITTED ∧ lb'.preparing = false ∧ lb'.tryingToPreAccept = false ∧
  lb'.clientProposals = lb.clientProposals ∧ lb'.preAcceptsSent = lb.preAcceptsSent ∧
  depsOk lb'.deps ∧ lb'.cmds = some v.cmds

/-- The hypotheses of `inv_commit_new`, bundled. -/
structure Ctx (S S' : Sys) (i : Nat) (σ' : RState) (x : InstId) (w : InstRec) (lb lb' : LbRec)
    (b : w32) (v : Val) (fast : Bool) (B : Bcast) (mc : Commit) : Prop where
  hS : Inv S
  hi : i < nR
  hidle : S.idle i
  hH : HS S S' i σ' (.commit x b v :: (if fast then [.fastCommit x v] else []))
      (fun _ => []) B.norm
  hchan : S'.proposeChan = S.proposeChan
  hB : B.x = x ∧ B.m = .commit mc ∧ B.peers = (S.rep i).peerOrder.take (nR - 1) ∧
      B.need = nR - 1 ∧ B.sent = 0 ∧ B.trackPA = false
  hmc : (⟨toN mc.replica, toN mc.inst⟩ : InstId) = x ∧ 0 ≤ zz mc.replica ∧
      zz mc.replica < nR ∧ 0 ≤ zz mc.inst ∧ toN mc.inst + 1 < MAX_INSTANCE ∧
      (⟨mc.command, mc.seq, mc.deps⟩ : Val) = v ∧ 0 ≤ zz mc.ballot
  hσ : σ'.inst = upd (S.rep i).inst x (some (comNew w lb' b v))
  hc : σ'.id = (S.rep i).id ∧ σ'.peerOrder = (S.rep i).peerOrder ∧
      σ'.crtInstance = (S.rep i).crtInstance ∧ σ'.conflicts = (S.rep i).conflicts ∧
      σ'.execedUpTo = (S.rep i).execedUpTo ∧ σ'.store = (S.rep i).store
  hw : (S.rep i).inst x = some w
  hlb : w.lb = some lb
  hnc : ¬ isCommitted w.status
  hb : zz w.bal ≤ zz b
  hlt : zz lb.lastTriedBallot ≤ zz b
  hvb : zz w.vbal ≤ zz b
  hvb0 : 0 ≤ zz w.vbal
  hagr : ∀ u, S.committedVal x u → u = v
  hch : S.committedVal x v ∨ (∃ b0, S.slowChosen x b0 v) ∨ (S.fastReplies x v ∧ fast = true)
  hwit : S.committedVal x v ∨ v.cmds = noop ∨ S.witnessed x v
  hval : v.cmds = noop ∨ ∃ ps, S.owner x = some ps ∧ v.cmds = ps.map (·.cmd)
  hdeps : depsOk v.deps
  hcne : v.cmds ≠ []
  hprop : zz b ≤ zz (initBal x) → S.propAt x b v.cmds
  hpropM : S.propAt x mc.ballot v.cmds
  hfast : fast = true → i = x.q ∧ zz w.bal ≤ zz (initBal x)
  hk : LbComNew lb lb' v
  hQ : (∃ Q : List (Nat × PreAcceptReply), (Q.map (·.1)).Nodup ∧
      Q.length = lb'.preAcceptOKs.toNat ∧
      ∀ a m, (a, m) ∈ Q → a < nR ∧ a ≠ i ∧ S'.deliveredMsg a i (.preAcceptReply m) ∧
        (Msg.preAcceptReply m).instOf = some x ∧ m.ballot = lb'.lastTriedBallot) ∧
      (∃ Q : List Nat, Q.Nodup ∧ Q.length = lb'.acceptOKs.toNat ∧
      ∀ a ∈ Q, a < nR ∧ a ≠ i ∧ ∃ m : AcceptReply, S'.deliveredMsg a i (.acceptReply m) ∧
        (Msg.acceptReply m).instOf = some x ∧ m.ballot = lb'.lastTriedBallot)

theorem mem_E {x : InstId} {b : w32} {v : Val} {fast : Bool} (e : Event) :
    e ∈ (.commit x b v :: (if fast then [.fastCommit x v] else [])) ↔
      e = .commit x b v ∨ (fast = true ∧ e = .fastCommit x v) := by
  cases fast <;> simp

section
variable {S S' : Sys} {i : Nat} {σ' : RState} {x : InstId} {w : InstRec} {lb lb' : LbRec}
  {b : w32} {v : Val} {fast : Bool} {B : Bcast} {mc : Commit}
  (C : Ctx S S' i σ' x w lb lb' b v fast B mc)
include C

theorem c_ev : ∀ r e, S'.ev r e ↔ S.ev r e ∨
    (r = i ∧ (e = .commit x b v ∨ (fast = true ∧ e = .fastCommit x v))) := by
  intro r e; rw [C.hH.ev_iff, mem_E]

theorem c_hold : ∀ r e, S'.ev r e → (∀ y c u, e ≠ .commit y c u) → (∀ y u, e ≠ .fastCommit y u) →
    S.ev r e := by
  intro r e he h1 h2
  rcases (c_ev C r e).mp he with h | ⟨-, rfl | ⟨-, rfl⟩⟩
  · exact h
  · exact absurd rfl (h1 _ _ _)
  · exact absurd rfl (h2 _ _)

theorem c_xnc : ∀ c u, ¬ S.ev i (.commit x c u) := by
  intro c u h
  obtain ⟨w1, h1, hs⟩ := C.hS.2.commitRec i x c u C.hi h
  rw [C.hw] at h1; cases h1; exact C.hnc hs

theorem c_notEold : ∀ r e, S.ev r e → r = i →
    e ∉ (.commit x b v :: (if fast then [.fastCommit x v] else [])) := by
  intro r e he hr h
  subst hr
  rcases (mem_E e).mp h with rfl | ⟨-, rfl⟩
  · exact c_xnc C _ _ he
  · obtain ⟨-, c, hc⟩ := C.hS.2.fastCommitEv r x v he
    exact c_xnc C _ _ hc

theorem c_evB : ∀ r e r' e', S'.evBefore r e r' e' → S.ev r' e' → S.evBefore r e r' e' :=
  fun r e r' e' h h' => C.hH.evBefore_back h h' (c_notEold C r' e' h')

theorem c_msgs : ∀ fr to m', m' ∈ S'.msgs fr to ↔ m' ∈ S.msgs fr to ∨
    (fr = i ∧ m' = .commit mc ∧ to ∈ (S.rep i).peerOrder.take (nR - 1)) := by
  obtain ⟨hBx, hBm, hBp, hBn, hBs, hBt⟩ := C.hB
  intro fr to m'
  rw [C.hH.mem_msgs]
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

theorem c_mold : ∀ fr to m', m' ∈ S'.msgs fr to → (∀ c, m' ≠ .commit c) → m' ∈ S.msgs fr to := by
  intro fr to m' h hn
  rcases (c_msgs C _ _ _).mp h with h | ⟨-, rfl, -⟩
  · exact h
  · exact absurd rfl (hn mc)

theorem c_cv : ∀ y u, S'.committedVal y u ↔ S.committedVal y u ∨ (y = x ∧ u = v) := by
  intro y u
  constructor
  · rintro (⟨r, c, h⟩ | ⟨fr, to, m', hm', hy, rfl⟩)
    · rcases (c_ev C r _).mp h with h | ⟨-, h | ⟨-, h⟩⟩
      · exact Or.inl (Or.inl ⟨r, c, h⟩)
      · simp only [Event.commit.injEq] at h; obtain ⟨rfl, -, rfl⟩ := h; exact Or.inr ⟨rfl, rfl⟩
      · cases h
    · rcases (c_msgs C _ _ _).mp hm' with h | ⟨-, h, -⟩
      · exact Or.inl (Or.inr ⟨fr, to, m', h, hy, rfl⟩)
      · cases h
        simp only [Msg.instOf, Option.some.injEq] at hy
        rw [C.hmc.1] at hy
        exact Or.inr ⟨hy.symm, C.hmc.2.2.2.2.2.1⟩
  · rintro ((⟨r, c, h⟩ | ⟨fr, to, m', hm', hy, rfl⟩) | ⟨rfl, rfl⟩)
    · exact Or.inl ⟨r, c, C.hH.ev_old h⟩
    · exact Or.inr ⟨fr, to, m', C.hH.msgs_old hm', hy, rfl⟩
    · exact Or.inl ⟨i, b, C.hH.ev_new (by simp)⟩

theorem c_cvm : ∀ y u, S.committedVal y u → S'.committedVal y u :=
  fun y u h => (c_cv C y u).mpr (Or.inl h)

theorem c_xcases : S.committedVal x v ∨ ∀ u, ¬ S.committedVal x u := by
  by_cases h : S.committedVal x v
  · exact Or.inl h
  · exact Or.inr (fun u hu => by have := C.hagr u hu; subst this; exact h hu)

theorem c_prep : ∀ r m' e, S'.prepReport r m' e ↔ S.prepReport r m' e := by
  intro r m' e
  constructor
  · rintro ⟨he, ⟨to, hm', rfl⟩ | rfl⟩
    · exact ⟨c_hold C r _ he (fun _ _ _ h => by cases h) (fun _ _ h => by cases h),
        Or.inl ⟨to, c_mold C _ _ _ hm' (fun _ h => by cases h), rfl⟩⟩
    · exact ⟨c_hold C r _ he (fun _ _ _ h => by cases h) (fun _ _ h => by cases h), Or.inr rfl⟩
  · rintro ⟨he, ⟨to, hm', rfl⟩ | rfl⟩
    · exact ⟨C.hH.ev_old he, Or.inl ⟨to, C.hH.msgs_old hm', rfl⟩⟩
    · exact ⟨C.hH.ev_old he, Or.inr rfl⟩

theorem c_cnt0 : ∀ fr to (p : Msg → Bool), p (.commit mc) = false →
    S'.cnt fr to p = S.cnt fr to p := by
  intro fr to p hp
  rw [C.hH.cnt_eq]
  split
  · simp only [List.nil_append, Nat.add_eq_left, List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro m' hm'
    obtain ⟨h1, -⟩ := mem_intended_norm hm'
    rw [h1, C.hB.2.1, hp]; simp
  · rfl

theorem c_allP : ∀ fr to (p : Msg → Bool), p (.commit mc) = false → S.allDeliv fr to p →
    S'.allDeliv fr to p := by
  intro fr to p hp h
  refine C.hH.allDeliv_old h (fun _ m' hm' => ?_)
  simp only [List.nil_append] at hm'
  obtain ⟨h1, -⟩ := mem_intended_norm hm'
  rw [h1, C.hB.2.1, hp]

theorem c_rep : ∀ r y, (S'.rep r).inst y =
    if r = i ∧ y = x then some (comNew w lb' b v) else (S.rep r).inst y := by
  intro r y
  rw [C.hH.rep]
  by_cases hr : r = i
  · subst hr; simp only [upd_same, C.hσ, upd_apply, true_and]
  · simp [upd_other _ _ _ _ hr, hr]

theorem c_R1 : ∀ r y w2, (S'.rep r).inst y = some w2 →
    (i = r ∧ x = y ∧ comNew w lb' b v = w2) ∨ ((S.rep r).inst y = some w2 ∧ ¬ (r = i ∧ y = x)) := by
  intro r y w2 h; rw [c_rep C] at h; split at h
  · rename_i hc; obtain ⟨rfl, rfl⟩ := hc; simp only [Option.some.injEq] at h
    exact Or.inl ⟨rfl, rfl, h⟩
  · rename_i hc; exact Or.inr ⟨h, hc⟩

theorem c_R2 : ∀ r y w1, (S.rep r).inst y = some w1 →
    (i = r ∧ x = y ∧ w = w1) ∨ (S'.rep r).inst y = some w1 := by
  intro r y w1 h
  by_cases hc : r = i ∧ y = x
  · obtain ⟨rfl, rfl⟩ := hc; rw [C.hw] at h; cases h; exact Or.inl ⟨rfl, rfl, rfl⟩
  · right; rw [c_rep C, if_neg hc]; exact h

theorem c_R3 : (S'.rep i).inst x = some (comNew w lb' b v) := by rw [c_rep C]; simp

theorem c_fl : ∀ r, (S'.rep r).id = (S.rep r).id ∧ (S'.rep r).peerOrder = (S.rep r).peerOrder ∧
    (S'.rep r).crtInstance = (S.rep r).crtInstance ∧
    (S'.rep r).conflicts = (S.rep r).conflicts ∧
    (S'.rep r).execedUpTo = (S.rep r).execedUpTo ∧ (S'.rep r).store = (S.rep r).store := by
  intro r
  by_cases hr : r = i
  · subst hr; rw [C.hH.rep_self]; exact C.hc
  · rw [C.hH.rep_other hr]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem c_hlbv : ∀ r y w2 lb2, (S'.rep r).inst y = some w2 → w2.lb = some lb2 →
    (i = r ∧ x = y ∧ comNew w lb' b v = w2 ∧ lb' = lb2) ∨
      ((S.rep r).inst y = some w2 ∧ ¬ (r = i ∧ y = x)) := by
  intro r y w2 lb2 h2 hl2
  rcases c_R1 C r y w2 h2 with ⟨rfl, rfl, rfl⟩ | h
  · simp only [comNew, Option.some.injEq] at hl2; exact Or.inl ⟨rfl, rfl, rfl, hl2⟩
  · exact Or.inr h

theorem c_ex : ∀ r y, (S'.rep r).executed y ↔ (S.rep r).executed y := by
  intro r y
  constructor
  · rintro ⟨w2, h2, hs⟩
    rcases c_R1 C r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
    · simp [comNew] at hs; exact absurd hs (by decide)
    · exact ⟨w2, h, hs⟩
  · rintro ⟨w1, h1, hs⟩
    rcases c_R2 C r y w1 h1 with ⟨-, -, rfl⟩ | h
    · exact absurd (Or.inr hs) C.hnc
    · exact ⟨w1, h, hs⟩

theorem c_bal : ∀ r y w1, (S.rep r).inst y = some w1 →
    ∃ w2, (S'.rep r).inst y = some w2 ∧ zz w1.bal ≤ zz w2.bal := by
  intro r y w1 h1
  rcases c_R2 C r y w1 h1 with ⟨rfl, rfl, rfl⟩ | h
  · exact ⟨_, c_R3 C, C.hb⟩
  · exact ⟨w1, h, Int.le_refl _⟩

end

/-! ## Dependencies of a new decided value -/

theorem getD_eq_of_lt {l : List w32} {n : Nat} (h : n < l.length) (a a' : w32) :
    l.getD n a = l.getD n a' := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem covers_mono {d d' : List w32} {y : InstId} (h : depsLe d d') (hq : y.q < nR)
    (hc : covers d y) : covers d' y := by
  obtain ⟨h1, h2, h3⟩ := h
  have := h3 y.q hq
  unfold covers at hc ⊢
  rw [getD_eq_of_lt (by omega) _ 0] at hc
  rw [getD_eq_of_lt (by omega) _ 0]
  omega

theorem interfere_code {a a' : List WCmd} (h : interfere a a') :
    interfereCode a a' ∧ interfereCode a' a := by
  have hne : opPUT ≠ opGET := by decide
  have hsg : opSCAN ≠ opGET := by decide
  obtain ⟨c, hc, c', hc', h⟩ := h
  rcases h with ⟨hk, hp, -, -⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · refine ⟨⟨c, hc, c', hc', Or.inl ⟨hk, ?_⟩⟩, ⟨c', hc', c, hc, Or.inl ⟨hk.symm, ?_⟩⟩⟩
    · rcases hp with h | h
      · left; rw [h]; exact hne
      · right; rw [h]; exact hne
    · rcases hp with h | h
      · right; rw [h]; exact hne
      · left; rw [h]; exact hne
  · exact ⟨⟨c, hc, c', hc', Or.inr (Or.inl ⟨h1, h2⟩)⟩, ⟨c', hc', c, hc, Or.inr (Or.inr ⟨h2, h1⟩)⟩⟩
  · exact ⟨⟨c, hc, c', hc', Or.inr (Or.inr ⟨h1, h2⟩)⟩, ⟨c', hc', c, hc, Or.inr (Or.inl ⟨h2, h1⟩)⟩⟩

theorem interfere_ne_noop {a a' : List WCmd} (h : interfere a a') : a ≠ noop ∧ a' ≠ noop := by
  obtain ⟨c, hc, c', hc', h⟩ := h
  have h12 : c.op ≠ opNONE ∧ c'.op ≠ opNONE := by
    rcases h with ⟨-, -, h1, h2⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
    · exact ⟨h1, h2⟩
    · rw [h1, h2]; exact ⟨by decide, by decide⟩
    · rw [h1, h2]; exact ⟨by decide, by decide⟩
  refine ⟨fun e => ?_, fun e => ?_⟩
  · subst e; simp only [noop, List.mem_singleton] at hc; subst hc; exact h12.1 rfl
  · subst e; simp only [noop, List.mem_singleton] at hc'; subst hc'; exact h12.2 rfl

/-- A witnessed value and a decided interfering one: one covers the other (their witnesses meet
at a replica, whose later attribute computation covers the earlier record). -/
theorem depsCover_new {S : Sys} (hS : Inv S) {x y : InstId} {v vy : Val} (hxy : x ≠ y)
    (hW : S.witnessed x v) (hy : S.committedVal y vy) (hi : interfere v.cmds vy.cmds) :
    covers v.deps y ∨ covers vy.deps x := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, s16, s17, -⟩ := hS.1
  obtain ⟨-, hny⟩ := interfere_ne_noop hi
  obtain ⟨W, hW1, hW2, hW3⟩ := hW
  obtain ⟨W', hW1', hW2', hW3'⟩ := s16 y vy hy hny
  obtain ⟨c, hc, hc'⟩ := meet (U := List.range nR) hW1 hW1'
    (fun a ha => List.mem_range.mpr (hW3 a ha).1) (fun a ha => List.mem_range.mpr (hW3' a ha).1)
    (by rw [List.length_range]; unfold fR at hW2 hW2'; unfold nR; omega)
  obtain ⟨-, dx, ex, lex⟩ := (hW3 c hc)
  obtain ⟨-, dy, ey, ley⟩ := (hW3' c hc')
  have hxq := (hS.2.crtEv c _ x ex rfl).1
  have hyq := (hS.2.crtEv c _ y ey rfl).1
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp ex
  obtain ⟨p', hp'⟩ := List.mem_iff_getElem?.mp ey
  rcases Nat.lt_or_ge p p' with h | h
  · right
    exact covers_mono ley hxq (s17 c (.attrsRec x v.cmds dx) x v.cmds y vy.cmds dy rfl hxy
      ⟨p, p', h, hp, hp'⟩ (interfere_code hi).2)
  · rcases Nat.lt_or_eq_of_le h with h | rfl
    · left
      exact covers_mono lex hyq (s17 c (.attrsRec y vy.cmds dy) y vy.cmds x v.cmds dx rfl
        (Ne.symm hxy) ⟨p', p, h, hp', hp⟩ (interfere_code hi).1)
    · rw [hp] at hp'
      simp only [Option.some.injEq, Prod.mk.injEq, Event.attrsRec.injEq] at hp'
      exact absurd hp'.2.1 hxy

section
variable {S S' : Sys} {i : Nat} {σ' : RState} {x : InstId} {w : InstRec} {lb lb' : LbRec}
  {b : w32} {v : Val} {fast : Bool} {B : Bcast} {mc : Commit}
  (C : Ctx S S' i σ' x w lb lb' b v fast B mc)
include C

theorem c_vote : ∀ r y c st u, S'.ev r (.vote y c st u) → S.ev r (.vote y c st u) :=
  fun r y c st u h => c_hold C r _ h (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)

theorem c_acc : ∀ r y c u, S'.ev r (.accept y c u) → S.ev r (.accept y c u) :=
  fun r y c u h => c_hold C r _ h (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)

theorem c_ph : ∀ r y c u, S'.ev r (.phase1 y c u) → S.ev r (.phase1 y c u) :=
  fun r y c u h => c_hold C r _ h (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)

theorem c_mono : SafeMono S S' := by
  refine ⟨fun r y w1 h1 => ?_, fun r e h => C.hH.ev_old h,
    fun r y c st u h => Or.inl (c_vote C r y c st u h), fun y u h => ?_,
    fun a y m' h _ _ => Or.inl (c_mold C _ _ _ h (fun _ h => by cases h))⟩
  · rcases c_R2 C r y w1 h1 with ⟨rfl, rfl, rfl⟩ | h
    · exact ⟨_, c_R3 C, C.hb, fun _ => Or.inl (by simp only [comNew]; decide)⟩
    · exact ⟨w1, h, Int.le_refl _, fun h => Or.inl h⟩
  · rcases (c_ev C _ _).mp h with h | ⟨hr, h | ⟨hf, h⟩⟩
    · exact Or.inl h
    · cases h
    · simp only [Event.fastCommit.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2⟩ := C.hfast hf
      refine Or.inr (fun w0 h0 => ?_)
      rw [← h1, C.hw] at h0; cases h0; exact h2

theorem c_safe : Inv.safe S' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, s26, -⟩ := C.hS.1
  exact safe_frame (c_mono C) s26 (c_acc C) (c_ph C)

theorem c_reports : Inv.reports S' := by
  have hm := c_mono C
  have hP := C.hS.2.pm
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, s27⟩ := C.hS.1
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := s27
  have hprep := fun r m e (h : S'.prepReport r m e) => (c_prep C r m e).mp h
  refine ⟨fun r m e hp => c1 r m e (hprep r m e hp), fun r m e hp => c2 r m e (hprep r m e hp),
    fun r m e hp => c3 r m e (hprep r m e hp),
    fun r m e hp c u hb => c4 r m e (hprep r m e hp) c u (c_evB C _ _ _ _ hb (hprep r m e hp).1),
    fun r m e hr hp => ?_,
    fun r y c st st' u u' h1 h2 h3 h4 => c6 r y c st st' u u' h1 h2 (c_vote C _ _ _ _ _ h3)
      (c_vote C _ _ _ _ _ h4),
    fun y u m e h1 h2 h3 => ?_,
    fun r y u h1 u' => fastBlocked_mono hm (c8 r y u (c_acc C _ _ _ _ h1) u'),
    fun r m e hp => c9 r m e (hprep r m e hp)⟩
  · obtain ⟨w1, hw1, hle⟩ := c5 r m e hr (hprep r m e hp)
    obtain ⟨w2, hw2, hle', -⟩ := hm.bal r _ w1 hw1
    exact ⟨w2, hw2, Int.le_trans hle hle'⟩
  · rcases (c_ev C _ _).mp h1 with h1 | ⟨hr, h | ⟨hf, h⟩⟩
    · exact c7 y u m e h1 (hprep _ m e h2) h3
    · cases h
    · simp only [Event.fastCommit.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exfalso
      obtain ⟨hix, hle⟩ := C.hfast hf
      have hp0 := hprep _ m e h2
      obtain ⟨w1, hw1, hlt⟩ := hP.repLead _ m e hp0 (by rw [← h3])
      rw [h3, ← hix, C.hw] at hw1; cases hw1
      rw [h3] at hlt; omega

end

section
variable {S S' : Sys} {i : Nat} {σ' : RState} {x : InstId} {w : InstRec} {lb lb' : LbRec}
  {b : w32} {v : Val} {fast : Bool} {B : Bcast} {mc : Commit}
  (C : Ctx S S' i σ' x w lb lb' b v fast B mc)
include C

theorem c_wf : Inv.wf S' := by
  obtain ⟨hBx, hBm, hBp, hBn, hBs, hBt⟩ := C.hB
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := C.hk
  have hi := C.hi
  have hpeer := C.hS.2.peerOk i hi
  obtain ⟨w1', w2', w3', w4', w5', w6', w7', w8'⟩ := C.hS.1.1
  have hfl := c_fl C
  refine ⟨fun r hr => by rw [(hfl r).1]; exact w1' r hr, fun r hr y w2 h2 => ?_,
    fun r hr q hq => by rw [(hfl r).2.2.1]; exact w3' r hr q hq,
    fun r hr q k p hk => ?_, fun r hr q hq n' hn' => ?_, fun fr' to hne => ?_,
    fun fr' to n' hn' => ?_, fun r b' hb' => ?_⟩
  · rcases c_R1 C r y w2 h2 with ⟨rfl, rfl, rfl⟩ | ⟨h, -⟩
    · obtain ⟨g1, g2, g3, -, -, g6, g7⟩ := w2' i hi x w C.hw
      refine ⟨g1, g2, g3, fun _ => C.hdeps, fun lb2 hl2 _ => ?_, fun _ => by simp [comNew],
        fun lb2 ps hl2 hps => ?_⟩
      · simp only [comNew, Option.some.injEq] at hl2; subst hl2; exact k8
      · simp only [comNew, Option.some.injEq] at hl2; subst hl2
        rw [C.hH.owner]; rw [k6] at hps; exact g7 lb ps C.hlb hps
    · obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := w2' r hr y w2 h
      exact ⟨g1, g2, g3, g4, g5, g6, fun lb ps hlb hps => by rw [C.hH.owner]; exact g7 lb ps hlb hps⟩
  · rw [(hfl r).2.2.2.1] at hk
    obtain ⟨k1', k2', k3'⟩ := w4' r hr q k p hk
    have grow : ∀ y, (S.rep r).inst y ≠ none → (S'.rep r).inst y ≠ none := by
      intro y hy hy'
      obtain ⟨w1, h1⟩ := Option.ne_none_iff_exists'.mp hy
      rcases c_R2 C r y w1 h1 with ⟨rfl, rfl, -⟩ | h
      · rw [c_R3 C] at hy'; cases hy'
      · rw [h] at hy'; cases hy'
    exact ⟨k1', fun h0 => grow _ (k2' h0), fun h0 => grow _ (k3' h0)⟩
  · rw [(hfl r).2.2.2.2.1] at hn'
    exact (c_ex C r _).mpr (w5' r hr q hq n' hn')
  · by_cases h0 : S.msgs fr' to = []
    · obtain ⟨m', hm'⟩ := List.exists_mem_of_ne_nil _ hne
      rcases (c_msgs C _ _ _).mp hm' with h | ⟨rfl, -, hto⟩
      · rw [h0] at h; cases h
      · exact ⟨hi, (hpeer.2 to hto).1, fun h => (hpeer.2 to hto).2 h.symm⟩
    · exact w6' fr' to h0
  · rcases C.hH.delOk fr' to n' hn' with h | h
    · rw [C.hH.sent]; exact w7' fr' to n' h
    · rw [C.hH.sent]; exact h
  · rw [C.hH.pending] at hb'
    by_cases hr : r = i
    · subst hr
      rw [upd_same] at hb'
      obtain ⟨rfl, hpn, hsn⟩ := norm_some hb'
      refine ⟨hi, by rw [C.hH.execCur]; exact C.hidle.2, hpn, hsn, by rw [hBp]; exact hpeer.1,
        fun q hq => by rw [hBp] at hq; exact hpeer.2 q hq, _, lb', by rw [hBx]; exact c_R3 C, rfl⟩
    · rw [upd_other _ _ _ _ hr] at hb'
      obtain ⟨d1, d2, d3, d4, d5, d6, w1, lb1, h1, hl1⟩ := w8' r b' hb'
      refine ⟨d1, by rw [C.hH.execCur]; exact d2, d3, d4, d5, d6, w1, lb1, ?_, hl1⟩
      rw [c_rep C, if_neg (fun h => hr h.1)]; exact h1

theorem c_ballots : Inv.ballots S' := by
  obtain ⟨-, -, -, -, s5, -⟩ := C.hS.1
  refine ⟨fun r hr y w2 h2 => ?_, fun r hr y c st u he => ?_⟩
  · rcases c_R1 C r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
    · exact C.hvb
    · exact s5.1 r hr y w2 h
  · obtain ⟨w1, h1, hle⟩ := s5.2 r hr y c st u (c_vote C _ _ _ _ _ he)
    obtain ⟨w2, h2, hle'⟩ := c_bal C r y w1 h1
    exact ⟨w2, h2, Int.le_trans hle hle'⟩

theorem c_simple : Inv.msgWf S' ∧ Inv.replyTargets S' ∧ Inv.noTPA S' ∧ Inv.ballotOwner S' ∧
    Inv.oneProposal S' ∧ Inv.votesFollowProposals S' := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, -⟩ := C.hS.1
  obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := C.hmc
  have hnotE : ∀ e : Event, (∀ y c u, e ≠ .commit y c u) → (∀ y u, e ≠ .fastCommit y u) → i = i →
      e ∉ (.commit x b v :: (if fast then [.fastCommit x v] else [])) := by
    intro e h1 h2 _ h
    rcases (mem_E e).mp h with h | ⟨-, h⟩
    · exact h1 _ _ _ h
    · exact h2 _ _ h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro fr to m' hm'
    rcases (c_msgs C _ _ _).mp hm' with hm' | ⟨-, rfl, -⟩
    · exact s2 fr to m' hm'
    · refine ⟨fun q n' hq => ?_, fun ds hds => ?_⟩
      · simp only [Msg.rawId, Option.some.injEq, Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        exact ⟨m2, m3, m4, m5⟩
      · simp only [Msg.depsFields, List.mem_singleton] at hds
        subst hds
        have : mc.deps = v.deps := by rw [← m6]
        rw [this]; exact C.hdeps
  · intro fr to m' y hm' hy hk'
    rcases (c_msgs C _ _ _).mp hm' with hm' | ⟨-, rfl, -⟩
    · obtain ⟨w1, lb1, h1, hl1⟩ := s3 fr to m' y hm' hy hk'
      rcases c_R2 C to y w1 h1 with ⟨rfl, rfl, rfl⟩ | h
      · exact ⟨_, lb', c_R3 C, rfl⟩
      · exact ⟨w1, lb1, h, hl1⟩
    · rcases hk' with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
  · intro fr to m' hm'
    rcases (c_msgs C _ _ _).mp hm' with hm' | ⟨-, rfl, -⟩
    · exact s4 fr to m' hm'
    · exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
  · obtain ⟨o1, o2, o3, o4, o5, o6⟩ := s6
    refine ⟨fun r y c he => ?_, fun r y c u he => ?_, fun r y c u he => ?_,
      fun r to m' hm' => ?_, fun r to m' hm' => ?_, fun r to m' hm' => ?_⟩
    · have h := c_hold C r _ he (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)
      refine ⟨(o1 r y c h).1, ?_⟩
      rw [C.hH.count_eq (fun _ => hnotE _ (fun _ _ _ h => by cases h) (fun _ _ h => by cases h) rfl)]
      exact (o1 r y c h).2
    · exact C.hH.evBefore_old (o2 r y c u (c_ph C r y c u he))
    · exact C.hH.ev_old (o3 r y c u (c_acc C r y c u he))
    · obtain ⟨d1, d2⟩ := o4 r to m' (c_mold C _ _ _ hm' (fun _ h => by cases h))
      exact ⟨d1, C.hH.ev_old d2⟩
    · obtain ⟨d1, d2⟩ := o5 r to m' (c_mold C _ _ _ hm' (fun _ h => by cases h))
      exact ⟨d1, C.hH.ev_old d2⟩
    · obtain ⟨d1, d2⟩ := o6 r to m' (c_mold C _ _ _ hm' (fun _ h => by cases h))
      exact ⟨d1, C.hH.ev_old d2⟩
  · obtain ⟨p1, p2, p3⟩ := s7
    refine ⟨fun r r' y c u u' he he' => ?_, fun r r' y c u u' he he' => ?_,
      fun r r' y c u u' he he' => ?_⟩
    · obtain ⟨d1, d2, d3⟩ := p1 r r' y c u u' (c_ph C _ _ _ _ he) (c_ph C _ _ _ _ he')
      refine ⟨d1, d2, ?_⟩
      rw [C.hH.count_eq (fun _ => hnotE _ (fun _ _ _ h => by cases h) (fun _ _ h => by cases h) rfl)]
      exact d3
    · exact p2 r r' y c u u' (c_acc C _ _ _ _ he) (c_acc C _ _ _ _ he')
    · exact p3 r r' y c u u' (c_ph C _ _ _ _ he) (c_acc C _ _ _ _ he')
  · refine ⟨fun r y c st u he hst => ?_, fun r y c u he => ?_⟩
    · obtain ⟨l, u0, h1, h2⟩ := s8.1 r y c st u (c_vote C _ _ _ _ _ he) hst
      exact ⟨l, u0, C.hH.ev_old h1, h2⟩
    · obtain ⟨l, h1⟩ := s8.2 r y c u (c_vote C _ _ _ _ _ he); exact ⟨l, C.hH.ev_old h1⟩

theorem c_rr : Inv.repliesReportVotes S' ∧ Inv.prepReplyHighest S' := by
  obtain ⟨-, -, -, -, -, -, -, -, s9, s10, -⟩ := C.hS.1
  have hevB := c_evB C
  have hcvm := c_cvm C
  obtain ⟨q1, q2, q3⟩ := s9
  refine ⟨⟨fun r m' e hp => ?_, fun a r m' hm' => ?_, fun a r m' hm' => ?_⟩, ?_⟩
  · have hp0 := (c_prep C r m' e).mp hp
    obtain ⟨d1, d2, d3, d4, d5⟩ := q1 r m' e hp0
    refine ⟨d1, fun hs => C.hH.evBefore_old (d2 hs), fun hs => hcvm _ _ (d3 hs),
      fun hs c st u hb' => d4 hs c st u (hevB _ _ _ _ hb' hp0.1),
      fun c st u hb' => ?_⟩
    obtain ⟨pp, pp', hlt', h1, h2⟩ := hb'
    have hv' : S'.ev r (.vote _ c st u) := List.mem_of_getElem? h2
    exact d5 c st u (hevB _ _ _ _ ⟨pp, pp', hlt', h1, h2⟩ (c_vote C _ _ _ _ _ hv'))
  · have hm0 := c_mold C _ _ _ hm' (fun _ h => by cases h)
    obtain ⟨d1, d2, d3, d4⟩ := q2 a r m' hm0
    refine ⟨?_, fun hs => ?_, fun hs => ?_, fun hs => ?_⟩
    · obtain ⟨u, hu⟩ := d1; exact ⟨u, C.hH.ev_old hu⟩
    · obtain ⟨e1, u, e2, e3⟩ := d2 hs; exact ⟨e1, u, C.hH.ev_old e2, e3⟩
    · obtain ⟨u, e2, e3⟩ := d3 hs; exact ⟨u, C.hH.ev_old e2, e3⟩
    · obtain ⟨u, e2, e3⟩ := d4 hs; exact ⟨u, hcvm _ _ e2, e3⟩
  · have hm0 := c_mold C _ _ _ hm' (fun _ h => by cases h)
    rcases q3 a r m' hm0 with ⟨u, hu⟩ | ⟨⟨c, u, hu⟩, c2⟩
    · exact Or.inl ⟨u, C.hH.evBefore_old hu⟩
    · refine Or.inr ⟨⟨c, u, C.hH.evBefore_old hu⟩, fun m2 e' hp hy hb' => ?_⟩
      have hp0 := (c_prep C _ _ _).mp hp
      have hsent : S.ev a (.sent r (.acceptReply m')) := by
        obtain ⟨pp, pp', -, -, h1⟩ := hu; exact List.mem_of_getElem? h1
      exact c2 m2 e' hp0 hy (hevB _ _ _ _ hb' hsent)
  · intro r m' e hp c st u hb'
    have hp0 := (c_prep C r m' e).mp hp
    exact s10 r m' e hp0 c st u (hevB _ _ _ _ hb' hp0.1)

theorem c_lb : Inv.lbInv S' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, s11, -⟩ := C.hS.1
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := C.hk
  intro r hr y w2 lb2 h2 hl2
  rcases c_hlbv C r y w2 lb2 h2 hl2 with ⟨rfl, rfl, rfl, rfl⟩ | ⟨h, hne⟩
  · obtain ⟨a1, -, -, a4, -⟩ := s11 _ hr _ w lb C.hw C.hlb
    obtain ⟨⟨Q, q1, q2, q3⟩, ⟨Q', q1', q2', q3'⟩⟩ := C.hQ
    refine ⟨by rw [k1]; exact C.hH.ev_old a1, by rw [k1]; exact k2, k5,
      fun c u hv0 => by
        rw [k1]; exact a4 c u (hv0.imp (c_ph C _ _ _ _) (c_acc C _ _ _ _)),
      fun c1 => (by rw [k3] at c1; rcases c1 with h | h <;> cases h),
      ⟨Q, q1, q2, fun a m' hq => ?_⟩, ⟨Q', q1', q2', q3'⟩,
      fun c1 => (by rw [k3] at c1; cases c1), fun c1 => (by rw [k4] at c1; cases c1)⟩
    obtain ⟨b1, b2, b3, b4, b5⟩ := q3 a m' hq
    exact ⟨b1, b2, b3, b4, b5, fun c1 => (by rw [k3] at c1; rcases c1 with h | h <;> cases h)⟩
  · obtain ⟨a1, a2, a3, a4, a5, ⟨Q, q1, q2, q3⟩, ⟨Q', q1', q2', q3'⟩, a8, a9⟩ :=
      s11 r hr y w2 lb2 h hl2
    refine ⟨C.hH.ev_old a1, a2, a3,
      fun c u hv0 => a4 c u (hv0.imp (c_ph C _ _ _ _) (c_acc C _ _ _ _)),
      fun c1 c2 => ?_, ⟨Q, q1, q2, fun a m' hq => ?_⟩, ⟨Q', q1', q2', fun a hq => ?_⟩,
      fun c1 c2 c3 c4 => ?_, fun hp => ?_⟩
    · obtain ⟨d1, d2, u, d3, d4⟩ := a5 c1 c2; exact ⟨d1, d2, u, C.hH.ev_old d3, d4⟩
    · obtain ⟨b1, b2, b3, b4⟩ := q3 a m' hq; exact ⟨b1, b2, C.hH.deliveredMsg_old b3, b4⟩
    · obtain ⟨b1, b2, m', b3, b4⟩ := q3' a hq; exact ⟨b1, b2, m', C.hH.deliveredMsg_old b3, b4⟩
    · obtain ⟨d1, d2⟩ := a8 c1 c2 c3 c4; exact ⟨C.hH.ev_old d1, C.hH.ev_old d2⟩
    · obtain ⟨c1, c2⟩ := a9 hp
      refine ⟨c1, fun e he' => ?_⟩
      obtain ⟨d1, d2, d3⟩ := c2 e he'
      refine ⟨d1, d2, ?_⟩
      rcases d3 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Or.inl ⟨e1, C.hH.deliveredMsg_old e2⟩
      · exact Or.inr ⟨e1, C.hH.ev_old e2⟩

end

theorem interfere_symm {a a' : List WCmd} (h : interfere a a') : interfere a' a := by
  obtain ⟨c, hc, c', hc', h⟩ := h
  rcases h with ⟨hk, hp, h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact ⟨c', hc', c, hc, Or.inl ⟨hk.symm, hp.symm, h2, h1⟩⟩
  · exact ⟨c', hc', c, hc, Or.inr (Or.inr ⟨h2, h1, h3⟩)⟩
  · exact ⟨c', hc', c, hc, Or.inr (Or.inl ⟨h2, h1, h3⟩)⟩

section
variable {S S' : Sys} {i : Nat} {σ' : RState} {x : InstId} {w : InstRec} {lb lb' : LbRec}
  {b : w32} {v : Val} {fast : Bool} {B : Bcast} {mc : Commit}
  (C : Ctx S S' i σ' x w lb lb' b v fast B mc)
include C

theorem c_agr : Inv.agreement S' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, s12, -⟩ := C.hS.1
  refine ⟨fun y u u' h1 h2 => ?_, fun r hr y w2 h2 hc' => ?_⟩
  · rcases (c_cv C _ _).mp h1 with h1 | ⟨rfl, rfl⟩ <;>
      rcases (c_cv C _ _).mp h2 with h2 | ⟨hy, rfl⟩
    · exact s12.1 _ _ _ h1 h2
    · subst hy; exact C.hagr _ h1
    · exact (C.hagr _ h2).symm
    · rfl
  · rcases c_R1 C r y w2 h2 with ⟨rfl, rfl, rfl⟩ | ⟨h, -⟩
    · refine ⟨by simp [comNew], (c_cv C _ _).mpr (Or.inr ⟨rfl, ?_⟩)⟩
      simp [instVal, comNew]
    · obtain ⟨d1, d2⟩ := s12.2 r hr y w2 h hc'
      exact ⟨d1, c_cvm C _ _ d2⟩

theorem c_dc : Inv.decidedChosen S' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, s13, -⟩ := C.hS.1
  have hsl : ∀ y c u, S.slowChosen y c u → S'.slowChosen y c u := by
    rintro y c u ⟨Q, q1, q2, q3⟩
    exact ⟨Q, q1, q2, fun r hr => ⟨(q3 r hr).1, C.hH.ev_old (q3 r hr).2⟩⟩
  have hfr : ∀ y u, S.fastReplies y u → S'.fastReplies y u := by
    rintro y u ⟨Q, q1, q2, q3⟩
    refine ⟨Q, q1, q2, fun r hr => ?_⟩
    obtain ⟨d1, d2, st, d3, d4⟩ := q3 r hr
    exact ⟨d1, d2, st, d3, C.hH.ev_old d4⟩
  have hold : ∀ y u, S.committedVal y u →
      (∃ c, S'.slowChosen y c u) ∨ (S'.fastReplies y u ∧ S'.ev y.q (.fastCommit y u)) := by
    intro y u hu
    rcases s13 y u hu with ⟨c, h⟩ | ⟨h, hf⟩
    · exact Or.inl ⟨c, hsl _ _ _ h⟩
    · exact Or.inr ⟨hfr _ _ h, C.hH.ev_old hf⟩
  intro y u hu
  rcases (c_cv C _ _).mp hu with hu | ⟨rfl, rfl⟩
  · exact hold _ _ hu
  · rcases C.hch with h | ⟨c, h⟩ | ⟨h, hf⟩
    · exact hold _ _ h
    · exact Or.inl ⟨c, hsl _ _ _ h⟩
    · refine Or.inr ⟨hfr _ _ h, ?_⟩
      rw [← (C.hfast hf).1]
      exact C.hH.ev_new ((mem_E _).mpr (Or.inr ⟨hf, rfl⟩))

theorem c_dcv : Inv.depsCover S' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, s15, -⟩ := C.hS.1
  have hdx : ∀ z u', x ≠ z → S.committedVal z u' → interfere v.cmds u'.cmds →
      covers v.deps z ∨ covers u'.deps x := by
    intro z u' hne hz hi'
    rcases C.hwit with h | h | h
    · exact s15 _ _ _ _ hne h hz hi'
    · exact absurd h (interfere_ne_noop hi').1
    · exact depsCover_new C.hS hne h hz hi'
  intro y z u u' hne h1 h2 hi'
  rcases (c_cv C _ _).mp h1 with h1 | ⟨rfl, rfl⟩ <;>
    rcases (c_cv C _ _).mp h2 with h2 | ⟨rfl, rfl⟩
  · exact s15 _ _ _ _ hne h1 h2 hi'
  · exact (hdx y u (Ne.symm hne) h1 (interfere_symm hi')).symm
  · exact hdx z u' hne h2 hi'
  · exact absurd rfl hne

theorem c_wit : Inv.witnesses S' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, s16, -⟩ := C.hS.1
  have hmono : ∀ r e, S.ev r e → S'.ev r e := fun r e h => C.hH.ev_old h
  intro y u hu hn'
  rcases (c_cv C _ _).mp hu with hu | ⟨rfl, rfl⟩
  · exact (PMProof.witnessed_mono hmono (s16 y u hu hn') : S'.witnessed y u)
  · rcases C.hwit with h | h | h
    · exact (PMProof.witnessed_mono hmono (s16 _ _ h hn') : S'.witnessed _ _)
    · exact absurd h hn'
    · exact (PMProof.witnessed_mono hmono h : S'.witnessed _ _)

theorem c_misc : Inv.attrsCover S' ∧ Inv.slots S' ∧ Inv.commitMsgs S' ∧ Inv.pendingKind S' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, s17, -, -, -, -, s22, -, s24, s25, -⟩ :=
    C.hS.1
  obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := C.hmc
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r e y cy z cz d hrec hne hb' hi'
    refine s17 r e y cy z cz d hrec hne (c_evB C _ _ _ _ hb' ?_) hi'
    obtain ⟨pp, pp', -, -, h⟩ := hb'
    exact c_hold C r _ (List.mem_of_getElem? h) (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)
  · refine ⟨fun y u hu => ?_, fun y ps h p hp => ?_⟩
    · rw [C.hH.owner]
      rcases (c_cv C _ _).mp hu with hu | ⟨rfl, rfl⟩
      · exact s22.1 y u hu
      · exact C.hval
    · rw [C.hH.owner] at h; rw [C.hH.ops]; exact s22.2 y ps h p hp
  · intro fr to m' hm'
    rcases (c_msgs C _ _ _).mp hm' with hm' | ⟨-, h, -⟩
    · obtain ⟨r, c, h⟩ := s24 fr to m' hm'
      exact ⟨r, c, C.hH.ev_old h⟩
    · cases h
      refine ⟨i, b, ?_⟩
      rw [m1, m6]; exact C.hH.ev_new (by simp)
  · intro r b' hb'
    rw [C.hH.pending] at hb'
    by_cases hr : r = i
    · subst hr; rw [upd_same] at hb'
      obtain ⟨rfl, -⟩ := norm_some hb'
      rw [C.hB.2.1]; rfl
    · rw [upd_other _ _ _ _ hr] at hb'; exact s25 r b' hb'

theorem c_exec : Inv.execClosed S' ∧ Inv.execCursor S' ∧ Inv.execOrder S' ∧
    Inv.execPrefix S' ∧ Inv.clientOps S' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, s18, s19, s20, s21, -, s23, -⟩ :=
    C.hS.1
  have hcvm := c_cvm C
  have huq := (c_agr C).1
  have hi := C.hi
  have hwnex : w.status ≠ stEXECUTED := fun h => C.hnc (Or.inr h)
  have hxlog : x ∉ S.execLog i := by
    intro h
    obtain ⟨w1, h1, hs⟩ := ((s18 i hi).2.1 x).mp h
    rw [C.hw] at h1; cases h1; exact hwnex hs
  have hlx : ∀ r k, S'.lexec r k = S.lexec r k := by
    intro r k
    have hcur : S'.curSlots r k = S.curSlots r k := by
      by_cases hr : r = i
      · subst hr; simp only [Sys.curSlots, C.hH.execCur, C.hidle.2]
      · simp only [Sys.curSlots, C.hH.execCur, C.hH.execIdx, C.hH.rep_other hr]
    simp only [Sys.lexec, hcur, C.hH.execLog]
    congr 1
    by_cases hr : r = i
    · subst hr
      refine RecCommitProof.slotsOn_congr _ _ _ _ (fun y hy => ?_)
      rw [c_rep C, if_neg]; rintro ⟨-, rfl⟩; exact hxlog hy
    · rw [C.hH.rep_other hr]
  refine ⟨fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · obtain ⟨e1, e2, e3⟩ := s18 r hr
    refine ⟨by rw [C.hH.execLog]; exact e1, fun y => by rw [C.hH.execLog, c_ex C]; exact e2 y,
      fun y w2 h2 hs => ?_⟩
    rcases c_R1 C r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, hne⟩
    · simp [comNew] at hs; exact absurd hs (by decide)
    obtain ⟨d1, d2⟩ := e3 y w2 h hs
    refine ⟨hcvm _ _ d1, fun z hz => ?_⟩
    rw [c_ex C, C.hH.execCur]
    apply d2 z
    obtain ⟨w3, h3, hq, hz'⟩ := hz
    rw [c_rep C, if_neg hne] at h3
    exact ⟨w3, h3, hq, hz'⟩
  · by_cases hri : r = i
    · subst r
      have hc0 : S.execCur i = [] := C.hidle.2
      rw [C.hH.execCur, C.hH.execIdx]
      exact ⟨fun _ => (s19 i hr).1 hc0, fun h => absurd hc0 h⟩
    · rw [C.hH.rep_other hri, C.hH.execCur, C.hH.execIdx]; exact s19 r hr
  · intro r hr a c y z hac h1 h2 ht
    rw [C.hH.execLog] at h1 h2
    have hy : y ∈ S.eseq r := List.mem_append_left _ (List.mem_of_getElem? h1)
    obtain ⟨d1, d2⟩ := s20 r hr a c y z hac h1 h2
      (ExecOrd.tg_keep C.hS.1 C.hS.2.exec hcvm huq hr hy ht)
    exact ⟨ExecOrd.tg_mono hcvm d1, ExecOrd.sccOrd_mono hcvm d2⟩
  · obtain ⟨p1, p2, p3⟩ := s21
    refine ⟨fun r hr k => ?_, fun r hr k => ?_, fun r hr k pre e post h => ?_⟩
    · rw [hlx, C.hH.gexec]; exact p1 r hr k
    · rw [hlx, (c_fl C r).2.2.2.2.2]; exact p2 r hr k
    · rw [hlx] at h; rw [C.hH.gexec]; exact p3 r hr k pre e post h
  · obtain ⟨o1, o2, o3, o4, o5⟩ := s23
    have hso : S'.slotOp = S.slotOp := by funext s; simp only [Sys.slotOp, C.hH.owner]
    refine ⟨by rw [C.hH.ops]; exact o1, ?_, ?_, ?_, ?_⟩
    · intro k k' e e' p p' he he' h1 h2 h3
      rw [C.hH.gexec] at he he'; rw [hso] at h1 h2; exact o2 k k' e e' p p' he he' h1 h2 h3
    · intro k; rw [C.hH.gexec]; exact o3 k
    · intro k e he
      rw [C.hH.gexec] at he
      obtain ⟨d1, d2, d0, d3, u, d4, d5⟩ := o4 k e he
      exact ⟨d1, d2, by rw [C.hH.gexec]; exact d0, by rw [hso]; exact d3, u, hcvm _ _ d4, d5⟩
    · intro cid o
      rw [C.hH.fired, C.hH.gexec, hso]; exact o5 cid o

end

section
variable {S S' : Sys} {i : Nat} {σ' : RState} {x : InstId} {w : InstRec} {lb lb' : LbRec}
  {b : w32} {v : Val} {fast : Bool} {B : Bcast} {mc : Commit}
  (C : Ctx S S' i σ' x w lb lb' b v fast B mc)
include C

theorem c_pm : InvPM S' := by
  have hP := C.hS.2.pm
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := C.hk
  have hmono : ∀ r e, S.ev r e → S'.ev r e := fun r e h => C.hH.ev_old h
  have hnotPA : ¬ isPA lb'.status := by rw [k3]; rintro (h | h) <;> cases h
  have hmAR : ∀ a r m', Msg.acceptReply m' ∈ S'.msgs a r → Msg.acceptReply m' ∈ S.msgs a r :=
    fun a r m' h => c_mold C _ _ _ h (fun _ h => by cases h)
  have hmPAR : ∀ a r m', Msg.preAcceptReply m' ∈ S'.msgs a r →
      Msg.preAcceptReply m' ∈ S.msgs a r :=
    fun a r m' h => c_mold C _ _ _ h (fun _ h => by cases h)
  have hsent : ∀ fr to m', m' ∈ S.sent fr to → m' ∈ S'.sent fr to := by
    intro fr to m' h; rw [C.hH.sent]; exact h
  exact {
    arOk := PMProof.arOk_frame hP hmAR (c_acc C) (fun q y c u h => Or.inl (c_vote C _ _ _ _ _ h))
      hmono (c_cvm C) (c_bal C)
    commitProp := fun r y c u he hle => by
      rcases (c_ev C _ _).mp he with h | ⟨-, h | ⟨-, h⟩⟩
      · exact PMProof.propAt_mono hmono (hP.commitProp r y c u h hle)
      · simp only [Event.commit.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
        exact PMProof.propAt_mono hmono (C.hprop hle)
      · cases h
    commitMsgProp := fun fr to m' hm' => by
      rcases (c_msgs C _ _ _).mp hm' with h | ⟨-, h, -⟩
      · exact PMProof.propAt_mono hmono (hP.commitMsgProp fr to m' h)
      · cases h
        have : mc.command = v.cmds := by rw [← C.hmc.2.2.2.2.2.1]
        rw [C.hmc.1, this]
        exact PMProof.propAt_mono hmono C.hpropM
    lbProp := fun r hr y w2 lb2 h2 hl2 hs hv => by
      rcases c_hlbv C r y w2 lb2 h2 hl2 with ⟨-, -, -, rfl⟩ | ⟨h, -⟩
      · rw [k3] at hs; cases hs
      · obtain ⟨u, hu⟩ := hv
        exact PMProof.propAt_mono hmono (hP.lbProp r hr y w2 lb2 h hl2 hs ⟨u, c_acc C _ _ _ _ hu⟩)
    parCom := PMProof.parCom_frame hP hmPAR hmono
    parSt := PMProof.parSt_frame hP hmPAR hsent
    paFresh := fun r hr y w2 lb2 h2 hl2 hs h0 hv => by
      rcases c_hlbv C r y w2 lb2 h2 hl2 with ⟨-, -, -, rfl⟩ | ⟨h, -⟩
      · exact absurd hs hnotPA
      · obtain ⟨u, hu⟩ := hv
        exact hP.paFresh r hr y w2 lb2 h hl2 hs h0 ⟨u, c_ph C _ _ _ _ hu⟩
    paCmds := fun r hr y w2 lb2 h2 hl2 hs u hu => by
      rcases c_hlbv C r y w2 lb2 h2 hl2 with ⟨-, -, -, rfl⟩ | ⟨h, -⟩
      · exact absurd hs hnotPA
      · exact hP.paCmds r hr y w2 lb2 h hl2 hs u (c_ph C _ _ _ _ hu)
    paSent := PMProof.ps_hs hP C.hH C.hidle.1 (fun to m' h => by simp at h)
      (fun b' h => by
        obtain ⟨h1, -⟩ := norm_some h
        rw [h1]; exact C.hB.2.2.2.2.2) (fun y w2 lb2 h2 hl2 hlt2 => by
        rcases c_hlbv C _ y w2 lb2 h2 hl2 with ⟨h1, rfl, -, rfl⟩ | ⟨h, -⟩
        · exact ⟨w, lb, by rw [← h1]; exact C.hw, C.hlb, by rw [← k1]; exact hlt2, k7⟩
        · exact ⟨w2, lb2, h, hl2, hlt2, rfl⟩)
    pendPA := PMProof.pendPA_hs hP C.hH (fun b' h y c hc => by
      obtain ⟨h1, -⟩ := norm_some h
      rw [h1, C.hB.2.1] at hc; simp [Msg.isPAat] at hc)
    paVoteMsg := PMProof.paVoteMsg_frame hP (c_vote C) hsent
    parNoPA := PMProof.parNoPA_frame hP hmPAR (c_vote C)
    aeF := fun r hr y w2 lb2 h2 hl2 hs hae => by
      rcases c_hlbv C r y w2 lb2 h2 hl2 with ⟨-, -, -, rfl⟩ | ⟨h, -⟩
      · exact absurd hs hnotPA
      · obtain ⟨a, a', m1, m2, h1, h2', h3⟩ := hP.aeF r hr y w2 lb2 h hl2 hs hae
        exact ⟨a, a', m1, m2, hsent _ _ _ h1, hsent _ _ _ h2', h3⟩
    repLead := PMProof.repLead_frame hP (fun r m e h => (c_prep C r m e).mp h) (c_bal C)
    paGe := PMProof.paGe_frame hP (c_vote C) (c_ph C)
    phAttrs := PMProof.phAttrs_frame hP (c_ph C) hmono
    accWit := PMProof.accWit_frame hP (c_acc C) hmono (c_cvm C)
    accVote := PMProof.accVote_frame hP (c_acc C) hmono
    cmdSafe := CmdSafeProof.cmdSafe_frame hP (c_mono C) (c_ph C)
    accSup := CmdSafeProof.accSup_frame hP hmono (c_acc C) }

end

section
variable {S S' : Sys} {i : Nat} {σ' : RState} {x : InstId} {w : InstRec} {lb lb' : LbRec}
  {b : w32} {v : Val} {fast : Bool} {B : Bcast} {mc : Commit}
  (C : Ctx S S' i σ' x w lb lb' b v fast B mc)
include C

theorem c_aux (hcls : σ'.lastScan = (S.rep i).lastScan ∧ σ'.lastPut = (S.rep i).lastPut) :
    InvAux S' := by
  have hA := C.hS.2
  have hi := C.hi
  have hw := C.hw
  obtain ⟨s1, -, -, -, s5, -⟩ := C.hS.1
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := C.hk
  obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := C.hmc
  have R1 := c_R1 C
  have R2 := c_R2 C
  have R3 := c_R3 C
  have hlbv := c_hlbv C
  have hfl := c_fl C
  have hold := c_hold C
  have hvote := c_vote C
  have hevB := c_evB C
  have hxq : x.q < nR := (s1.2.1 i hi x w hw).2.1
  have hcom' : isCommitted (comNew w lb' b v).status := Or.inl rfl
  have hwnex : w.status ≠ stEXECUTED := fun h => C.hnc (Or.inr h)
  have hnotPA : ¬ isPA lb'.status := by rw [k3]; rintro (h | h) <;> cases h
  have hnn : ∀ y c u, (Event.commit y c u) ≠ .fastCommit x v := fun _ _ _ h => by cases h
  exact {
    stRange := fun r hr y w2 h2 => by
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · exact Or.inr (Or.inr (Or.inr hcom'))
      · exact hA.stRange r hr y w2 h
    cmdsSome := fun r hr y w2 h2 hs => by
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · simp [comNew]
      · exact hA.cmdsSome r hr y w2 h hs
    noneRec := fun r hr y w2 h2 hs => by
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · simp only [comNew] at hs; exact absurd hs (by decide)
      · obtain ⟨d1, d2⟩ := hA.noneRec r hr y w2 h hs
        exact ⟨d1, fun c st u hv0 => d2 c st u (hvote _ _ _ _ _ hv0)⟩
    vbalNonneg := fun r hr y w2 h2 hs => by
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · exact C.hvb0
      · exact hA.vbalNonneg r hr y w2 h hs
    votesLe := fun r hr y w2 h2 c st u hv0 => by
      rcases R1 r y w2 h2 with ⟨rfl, rfl, rfl⟩ | ⟨h, -⟩
      · exact hA.votesLe _ hr _ w hw c st u (hvote _ _ _ _ _ hv0)
      · exact hA.votesLe r hr y w2 h c st u (hvote _ _ _ _ _ hv0)
    recVote := fun r hr y w2 h2 hs => by
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · simp only [comNew] at hs
        exact absurd hs (by rintro ((h | h) | h) <;> exact absurd h (by decide))
      · exact C.hH.ev_old (hA.recVote r hr y w2 h hs)
    accKeep := fun r hr y w2 h2 c u hv0 hle => by
      rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
      · exact Or.inr hcom'
      · exact hA.accKeep r hr y w2 h c u (hvote _ _ _ _ _ hv0) hle
    recCommit := fun r hr y w2 h2 hs => by
      rcases R1 r y w2 h2 with ⟨rfl, rfl, rfl⟩ | ⟨h, -⟩
      · exact ⟨b, v, C.hH.ev_new (by simp), Int.le_refl _⟩
      · obtain ⟨c, u, d1, d2⟩ := hA.recCommit r hr y w2 h hs
        exact ⟨c, u, C.hH.ev_old d1, d2⟩
    commitRec := fun r y c u hr he => by
      rcases (c_ev C r _).mp he with h | ⟨rfl, h | ⟨-, h⟩⟩
      · obtain ⟨w1, h1, hs⟩ := hA.commitRec r y c u hr h
        rcases R2 r y w1 h1 with ⟨-, -, rfl⟩ | h'
        · exact absurd hs C.hnc
        · exact ⟨w1, h', hs⟩
      · simp only [Event.commit.injEq] at h; obtain ⟨rfl, -, -⟩ := h
        exact ⟨_, R3, hcom'⟩
      · cases h
    fastCommitEv := fun r y u he => by
      rcases (c_ev C r _).mp he with h | ⟨rfl, h | ⟨hf, h⟩⟩
      · obtain ⟨d1, c, d2⟩ := hA.fastCommitEv r y u h
        exact ⟨d1, c, C.hH.ev_old d2⟩
      · cases h
      · simp only [Event.fastCommit.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        exact ⟨(C.hfast hf).1, b, C.hH.ev_new (by simp)⟩
    makerLb := fun r y c hr he => by
      obtain ⟨w1, lb1, h1, hl1, hle⟩ :=
        hA.makerLb r y c hr (hold _ _ he (fun _ _ _ h => by cases h) (fun _ _ h => by cases h))
      rcases R2 r y w1 h1 with ⟨rfl, rfl, rfl⟩ | h
      · rw [C.hlb] at hl1; cases hl1; exact ⟨_, lb', R3, rfl, by rw [k1]; exact hle⟩
      · exact ⟨w1, lb1, h, hl1, hle⟩
    lastLeBal := fun r hr y w2 lb2 h2 hl2 => by
      rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, rfl, rfl⟩ | ⟨h, -⟩
      · rw [k1]; exact C.hlt
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
      rcases (c_msgs C _ _ _).mp hm' with hm' | ⟨-, rfl, -⟩
      · exact hA.crtMsg fr to m' y hm' hy
      · simp only [Msg.instOf, Option.some.injEq] at hy
        rw [m1] at hy; subst hy; exact hA.crtRec i hi _ w hw
    crtEv := fun r e y he hy => by
      rw [(hfl y.q).2.2.1]
      rcases (c_ev C r e).mp he with h | ⟨-, rfl | ⟨-, rfl⟩⟩
      · exact hA.crtEv r e y h hy
      · simp only [Event.instOf, Option.some.injEq] at hy; subst hy
        exact ⟨hxq, hA.crtRec i hi _ w hw⟩
      · simp only [Event.instOf, Option.some.injEq] at hy; subst hy
        exact ⟨hxq, hA.crtRec i hi _ w hw⟩
    ownRow := fun q hq j hj => by
      rw [(hfl q).2.2.1] at hj
      obtain ⟨w1, lb1, h1, hl1⟩ := hA.ownRow q hq j hj
      rcases R2 q _ w1 h1 with ⟨rfl, hx', rfl⟩ | h
      · exact ⟨_, lb', by rw [← hx']; exact R3, rfl⟩
      · exact ⟨w1, lb1, h, hl1⟩
    paNoAcc := fun r hr y w2 lb2 h2 hl2 hs u hv0 => by
      rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, -, rfl⟩ | ⟨h, -⟩
      · exact hnotPA hs
      · exact hA.paNoAcc r hr y w2 lb2 h hl2 hs u (c_acc C _ _ _ _ hv0)
    paLeader := fun r hr y w2 lb2 h2 hl2 hs hp hc' hb' => by
      rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, -, rfl⟩ | ⟨h, -⟩
      · exact absurd hs hnotPA
      · obtain ⟨u, hu⟩ := hp
        exact hA.paLeader r hr y w2 lb2 h hl2 hs ⟨u, c_ph C _ _ _ _ hu⟩ hc' hb'
    prepNoProp := fun r hr y w2 lb2 h2 hl2 hp => by
      rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, -, rfl⟩ | ⟨h, -⟩
      · rw [k4] at hp; cases hp
      · obtain ⟨d1, d2, d3, d4, d5⟩ := hA.prepNoProp r hr y w2 lb2 h hl2 hp
        exact ⟨d1, fun u h' => d2 u (c_ph C _ _ _ _ h'),
          fun u h' => d3 u (c_acc C _ _ _ _ h'), d4, d5⟩
    paMsgOnce := fun fr to y c => by rw [c_cnt0 C _ _ _ rfl]; exact hA.paMsgOnce fr to y c
    accMsgOnce := fun fr to y c => by rw [c_cnt0 C _ _ _ rfl]; exact hA.accMsgOnce fr to y c
    paVoteDeliv := fun r y c st u hst hv0 => by
      rcases hA.paVoteDeliv r y c st u hst (hvote _ _ _ _ _ hv0) with ⟨u0, h0⟩ | h0
      · exact Or.inl ⟨u0, C.hH.ev_old h0⟩
      · exact Or.inr (fun fr' => c_allP C _ _ _ rfl (h0 fr'))
    parOnce := fun a r y c h1 => by
      rw [c_cnt0 C _ _ _ rfl] at h1 ⊢
      obtain ⟨d1, d2⟩ := hA.parOnce a r y c h1
      exact ⟨d1, c_allP C _ _ _ rfl d2⟩
    arFrom := fun a r m' hm' => by
      obtain ⟨c, u, d1, d2⟩ := hA.arFrom a r m' (c_mold C _ _ _ hm' (fun _ h => by cases h))
      exact ⟨c, u, d1, C.hH.ev_old d2⟩
    arOnce := fun a r y c h1 => by
      rw [c_cnt0 C _ _ _ rfl] at h1 ⊢
      rcases hA.arOnce a r y c h1 with ⟨w1, lb1, h1', hl1, hlt'⟩ | ⟨d1, d2⟩
      · refine Or.inl ?_
        rcases R2 r y w1 h1' with ⟨rfl, rfl, rfl⟩ | h
        · rw [C.hlb] at hl1; cases hl1; exact ⟨_, lb', R3, rfl, by rw [k1]; exact hlt'⟩
        · exact ⟨w1, lb1, h, hl1, hlt'⟩
      · exact Or.inr ⟨d1, c_allP C _ _ _ rfl d2⟩
    commitBal := fun fr to m' hm' => by
      rcases (c_msgs C _ _ _).mp hm' with hm' | ⟨-, h, -⟩
      · exact hA.commitBal fr to m' hm'
      · cases h; exact m7
    sentPR := fun r to m' he => by
      have he0 := hold _ _ he (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)
      obtain ⟨d1, d2, d3⟩ := hA.sentPR r to m' he0
      refine ⟨fun hr => ?_, fun c st u hb' => d2 c st u ?_, fun to' m2 hb' hy => d3 to' m2 ?_ hy⟩
      · obtain ⟨w1, h1, hle⟩ := d1 hr
        obtain ⟨w2, h2, hle'⟩ := c_bal C r _ w1 h1
        exact ⟨w2, h2, Int.le_trans hle hle'⟩
      · obtain ⟨pp, pp', hlt', h1, h2⟩ := hb'
        exact hevB _ _ _ _ ⟨pp, pp', hlt', h1, h2⟩ (hvote _ _ _ _ _ (List.mem_of_getElem? h2))
      · obtain ⟨pp, pp', hlt', h1, h2⟩ := hb'
        exact hevB _ _ _ _ ⟨pp, pp', hlt', h1, h2⟩
          (hold _ _ (List.mem_of_getElem? h2) (fun _ _ _ h => by cases h) (fun _ _ h => by cases h))
    confCover := fun r hr e y cy he hrec c hc' => by
      rw [(hfl r).2.2.2.1]
      rcases (c_ev C r e).mp he with h | ⟨-, rfl | ⟨-, rfl⟩⟩
      · exact hA.confCover r hr e y cy h hrec c hc'
      · cases hrec
      · cases hrec
    classWf := fun r hr => by
      have hcl : (S'.rep r).lastScan = (S.rep r).lastScan ∧
          (S'.rep r).lastPut = (S.rep r).lastPut := by
        by_cases h : r = i
        · subst h; rw [C.hH.rep_self]; exact hcls
        · rw [C.hH.rep_other h]; exact ⟨rfl, rfl⟩
      refine AuxProof.clsWf_keep (hA.classWf r hr) hcl.1 hcl.2 (fun y h => ?_)
      obtain ⟨w1, h1⟩ := Option.ne_none_iff_exists'.mp h
      rcases R2 r y w1 h1 with ⟨rfl, rfl, -⟩ | h2
      · rw [R3]; simp
      · rw [h2]; simp
    classCover := fun r hr e y cy he hrec => by
      have hcl : (S'.rep r).lastScan = (S.rep r).lastScan ∧
          (S'.rep r).lastPut = (S.rep r).lastPut := by
        by_cases h : r = i
        · subst h; rw [C.hH.rep_self]; exact hcls
        · rw [C.hH.rep_other h]; exact ⟨rfl, rfl⟩
      rw [hcl.1, hcl.2]
      rcases (c_ev C r e).mp he with h | ⟨-, rfl | ⟨-, rfl⟩⟩
      · exact hA.classCover r hr e y cy h hrec
      · cases hrec
      · cases hrec
    paAttrs := fun r y c st u hst hv0 =>
      C.hH.ev_old (hA.paAttrs r y c st u hst (hvote _ _ _ _ _ hv0))
    valOk := fun r y c u hv0 => by
      rw [C.hH.owner]
      exact hA.valOk r y c u (hv0.imp (c_ph C _ _ _ _) (c_acc C _ _ _ _))
    cmdsNe := by
      obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hA.cmdsNe
      refine ⟨fun fr to m' hm' cs hcs => ?_,
        fun r hr y w2 cs h2 hc' => ?_, fun r hr y w2 lb2 cs h2 hl2 hc' => ?_,
        fun fr to m' hm' => n4 fr to m' (c_mold C _ _ _ hm' (fun _ h => by cases h)),
        fun r m' he => n5 r m' (hold _ _ he (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)),
        fun r y c u hv0 => n6 r y c u (hv0.imp (c_ph C _ _ _ _) (c_acc C _ _ _ _))⟩
      · rcases (c_msgs C _ _ _).mp hm' with hm' | ⟨-, rfl, -⟩
        · exact n1 fr to m' hm' cs hcs
        · simp only [Msg.commandField, Option.some.injEq] at hcs
          subst hcs
          have : mc.command = v.cmds := by rw [← m6]
          rw [this]; exact C.hcne
      · rcases R1 r y w2 h2 with ⟨-, -, rfl⟩ | ⟨h, -⟩
        · simp only [comNew, Option.some.injEq] at hc'; subst hc'; exact C.hcne
        · exact n2 r hr y w2 cs h hc'
      · rcases hlbv r y w2 lb2 h2 hl2 with ⟨-, -, -, rfl⟩ | ⟨h, -⟩
        · rw [k9] at hc'; cases hc'; exact C.hcne
        · exact n3 r hr y w2 lb2 cs h hl2 hc'
    prSent := fun fr to m' hm' =>
      C.hH.ev_old (hA.prSent fr to m' (c_mold C _ _ _ hm' (fun _ h => by cases h)))
    selfOk := fun r m' he hs => hA.selfOk r m'
      (hold _ _ he (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)) hs
    selfRaw := fun r m' he => hA.selfRaw r m'
      (hold _ _ he (fun _ _ _ h => by cases h) (fun _ _ h => by cases h))
    pm := c_pm C
    ownerCrt := fun y ps h => by
      rw [C.hH.owner] at h; rw [(hfl y.q).2.2.1]; exact hA.ownerCrt y ps h
    execLo := AuxProof.execLo_of_eq hA.execLo (fun r _ => (hfl r).2.2.2.2.1)
    exec := ExecOrd.invExec_hs C.hS.1 hA.exec C.hH C.hidle (c_agr C) C.hchan
      (fun r y h => by
        rw [c_rep C, if_neg]; rintro ⟨h1, h2⟩; rcases h with h | h; exact h h1; exact h h2) R3
      (fun w0 h0 hs => by rw [hw] at h0; cases h0; exact absurd hs hwnex)
      (fun lb2 hl hne => ⟨w, lb, hw, C.hlb, by
        simp only [comNew, Option.some.injEq] at hl; subst hl; rw [k6] at hne; exact hne⟩) }

end

/-- **Committing a possibly new value, with the Commit broadcast, keeps the invariant.** -/
theorem inv_commit_new (S S' : Sys) (i : Nat) (σ' : RState) (x : InstId) (w : InstRec)
    (lb lb' : LbRec) (b : w32) (v : Val) (fast : Bool) (B : Bcast) (mc : Commit) (hS : Inv S)
    (hi : i < nR) (hidle : S.idle i)
    (hH : HS S S' i σ' (.commit x b v :: (if fast then [.fastCommit x v] else []))
      (fun _ => []) B.norm)
    (hchan : S'.proposeChan = S.proposeChan)
    (hB : B.x = x ∧ B.m = .commit mc ∧ B.peers = (S.rep i).peerOrder.take (nR - 1) ∧
      B.need = nR - 1 ∧ B.sent = 0 ∧ B.trackPA = false)
    (hmc : (⟨toN mc.replica, toN mc.inst⟩ : InstId) = x ∧ 0 ≤ zz mc.replica ∧
      zz mc.replica < nR ∧ 0 ≤ zz mc.inst ∧ toN mc.inst + 1 < MAX_INSTANCE ∧
      (⟨mc.command, mc.seq, mc.deps⟩ : Val) = v ∧ 0 ≤ zz mc.ballot)
    (hσ : σ'.inst = upd (S.rep i).inst x (some (comNew w lb' b v)))
    (hc : σ'.id = (S.rep i).id ∧ σ'.peerOrder = (S.rep i).peerOrder ∧
      σ'.crtInstance = (S.rep i).crtInstance ∧ σ'.conflicts = (S.rep i).conflicts ∧
      σ'.execedUpTo = (S.rep i).execedUpTo ∧ σ'.store = (S.rep i).store)
    (hcls : σ'.lastScan = (S.rep i).lastScan ∧ σ'.lastPut = (S.rep i).lastPut)
    (hw : (S.rep i).inst x = some w) (hlb : w.lb = some lb) (hnc : ¬ isCommitted w.status)
    (hb : zz w.bal ≤ zz b) (hlt : zz lb.lastTriedBallot ≤ zz b) (hvb : zz w.vbal ≤ zz b)
    (hvb0 : 0 ≤ zz w.vbal)
    (hagr : ∀ u, S.committedVal x u → u = v)
    (hch : S.committedVal x v ∨ (∃ b0, S.slowChosen x b0 v) ∨ (S.fastReplies x v ∧ fast = true))
    (hwit : S.committedVal x v ∨ v.cmds = noop ∨ S.witnessed x v)
    (hval : v.cmds = noop ∨ ∃ ps, S.owner x = some ps ∧ v.cmds = ps.map (·.cmd))
    (hdeps : depsOk v.deps) (hcne : v.cmds ≠ [])
    (hprop : zz b ≤ zz (initBal x) → S.propAt x b v.cmds)
    (hpropM : S.propAt x mc.ballot v.cmds)
    (hfast : fast = true → i = x.q ∧ zz w.bal ≤ zz (initBal x))
    (hk : LbComNew lb lb' v)
    (hQ : (∃ Q : List (Nat × PreAcceptReply), (Q.map (·.1)).Nodup ∧
      Q.length = lb'.preAcceptOKs.toNat ∧
      ∀ a m, (a, m) ∈ Q → a < nR ∧ a ≠ i ∧ S'.deliveredMsg a i (.preAcceptReply m) ∧
        (Msg.preAcceptReply m).instOf = some x ∧ m.ballot = lb'.lastTriedBallot) ∧
      (∃ Q : List Nat, Q.Nodup ∧ Q.length = lb'.acceptOKs.toNat ∧
      ∀ a ∈ Q, a < nR ∧ a ≠ i ∧ ∃ m : AcceptReply, S'.deliveredMsg a i (.acceptReply m) ∧
        (Msg.acceptReply m).instOf = some x ∧ m.ballot = lb'.lastTriedBallot)) :
    Inv S' := by
  have C : Ctx S S' i σ' x w lb lb' b v fast B mc :=
    ⟨hS, hi, hidle, hH, hchan, hB, hmc, hσ, hc, hw, hlb, hnc, hb, hlt, hvb, hvb0, hagr, hch, hwit,
      hval, hdeps, hcne, hprop, hpropM, hfast, hk, hQ⟩
  obtain ⟨hmw, hrt, hntpa, hown, hop, hvf⟩ := c_simple C
  obtain ⟨hrr, hhi⟩ := c_rr C
  obtain ⟨hac, hsl, hcm, hpk⟩ := c_misc C
  obtain ⟨he1, he2, he3, he4, hco⟩ := c_exec C
  have hwf := c_wf C
  have hbal := c_ballots C
  have hown' := hown
  have hsafe := c_safe C
  exact ⟨⟨hwf, hmw, hrt, hntpa, hbal, hown, hop, hvf, hrr, hhi, c_lb C, c_agr C, c_dc C,
    chosenSafe_of_safe _ hwf hbal hown' hvf hsafe, c_dcv C, c_wit C, hac, he1, he2, he3, he4,
    hsl, hco, hcm, hpk, hsafe, c_reports C⟩, c_aux C hcls⟩

end RecCommitNewProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
