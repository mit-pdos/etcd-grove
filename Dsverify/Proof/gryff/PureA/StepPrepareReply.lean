/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/StepPrepareReply.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A1b, internal: preservation of the agreement invariant by `stepPrepareReply`
(`handlePrepareReply`), the recovery's decision.

`oneCopy_inv`: a step of replica `a` that consumes one message, changes only its own copy of one
instance `(q, i)` (same ballot), extends the history of `(q, i)` only by `a` (`ExtA`) and sends
messages that are no Prepare nor OK PrepareReply, keeps `CInv` given the new copy's facts, the new
messages' facts and the new copy's multiplicities (`prepMult`). Every path of `stepPrepareReply`
is such a step (`prepareReply_inv`).
-/
module

public import Dsverify.Proof.gryff.PureA.StepPrepare

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.A1b

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn Perennial.gryff.pureA

theorem copyOk_Geq {c : Cfg gNet} {G G' : GG} {q i : w32} {a : Fin 3} {cp : Copy}
    (e : G' q i = G q i) (h : CopyOk c G q i a cp) : CopyOk c G' q i a cp := by
  refine ⟨h.nonneg, h.ballotForm, h.vbalLe, h.stOk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [e]
  · exact h.noVotes
  · exact h.accVote
  · exact h.committed
  · exact h.rstVbal
  · exact h.eqCre
  · exact h.leader0
  · exact h.ownFresh
  · exact h.preparing
  · exact h.eqTrack

theorem copyOk_balEq {c c1 : Cfg gNet} {G : GG} {q i : w32} {a : Fin 3} {cp : Copy}
    (hb : balOf c1 q i = balOf c q i) (h : CopyOk c G q i a cp) : CopyOk c1 G q i a cp :=
  { h with preparing := by rw [hb]; exact h.preparing }

/-- **A step changing one copy of its replica** (same ballot) keeps the invariant. -/
theorem oneCopy_inv {c c1 : Cfg gNet} {G G' : GG} {a : Fin 3} {e : Ev} {z : Msg} {s1 : RState}
    {o : List Out} {q i : w32} {cp0 cp' : Copy}
    (I : CInv c G)
    (hst : c1.st = fun j => if j = a then s1 else c.st j)
    (hinf : c1.inflight = fun j =>
      (if j = a then consume (gNet.recv e) (c.inflight j) else c.inflight j) ++ sentTo gNet j o)
    (hze : gNet.recv e = some z) (hz : z ∈ infR c a) (hzpa : ∀ x, z ≠ .preAccept x)
    (hs1 : ∀ q' i', s1.inst q' i' = if q' = q ∧ i' = i then some cp' else (c.st a).inst q' i')
    (hs1id : s1.id = (c.st a).id) (hs1crt : s1.crtInstance = (c.st a).crtInstance)
    (hc0 : cpOf c a q i = some cp0) (hb : cp'.ballot = cp0.ballot)
    (hcomm : isCommitted cp0.status → isCommitted cp'.status)
    (hstn : cp'.status ≠ St.NONE ∨ cp'.status = cp0.status)
    (hpa0 : 0 < sint.Z cp0.ballot ∨ cp'.status = cp0.status)
    (hGo : ∀ q' i', ¬ (q' = q ∧ i' = i) → G' q' i' = G q' i')
    (X : ExtA (G q i) (G' q i) a (sint.Z cp'.ballot))
    (hA : AInv (G' q i) (balOf c q i) (rowOf q))
    (hE : Evolve (rowOf q) (G q i) (balOf c q i) (G' q i) (balOf c q i))
    (hnew : CopyOk c G' q i a cp')
    (hpm : ∀ lb, cp'.lb = some lb → lb.preparing = true → ¬ isCommitted cp'.status →
      Own (sint.Z cp'.ballot) a →
      (∀ Y : Fin 3, (infR c1 Y).countP (isPrepareAt q i cp'.ballot) +
        (infR c1 a).countP (isOKReplyAt q i cp'.ballot Y) ≤ 1) ∧
      (sint.Z lb.prepareOKs = 1 → a ≠ rowOf q ∧
        (infR c1 (rowOf q)).countP (isPrepareAt q i cp'.ballot) = 0 ∧
        (infR c1 a).countP (isOKReplyAt q i cp'.ballot (rowOf q)) = 0))
    (hsent : ∀ (d : Fin 3) y, y ∈ sentR d o → MsgOk c1 G' d y ∧
      (msgInst y = none ∨ msgInst y = some (q, i)) ∧ (∀ x, y = .preAccept x → x.ballot ≠ 0) ∧
      (∀ q' i' b, isPrepareAt q' i' b y = false) ∧ (∀ q' i' b Y, isOKReplyAt q' i' b Y y = false)) :
    CInv c1 G' ∧ ∀ q' i', Evolve (rowOf q') (G q' i') (balOf c q' i') (G' q' i') (balOf c1 q' i') := by
  have hsta : c1.st a = s1 := by rw [hst]; exact if_pos rfl
  have hsto : ∀ j : Fin 3, j ≠ a → c1.st j = c.st j := by
    intro j hj; rw [hst]; exact if_neg hj
  have hcpa : ∀ q' i', cpOf c1 a q' i' =
      if q' = q ∧ i' = i then some cp' else cpOf c a q' i' := by
    intro q' i'; simp only [cpOf, hsta]; exact hs1 q' i'
  have hcpo : ∀ j : Fin 3, j ≠ a → ∀ q' i', cpOf c1 j q' i' = cpOf c j q' i' := by
    intro j hj q' i'; simp only [cpOf, hsto j hj]
  have hcpn : ∀ (j : Fin 3) q' i', ¬ (j = a ∧ q' = q ∧ i' = i) → cpOf c1 j q' i' = cpOf c j q' i' := by
    intro j q' i' hn
    by_cases hj : j = a
    · subst hj; rw [hcpa, if_neg (fun h' => hn ⟨rfl, h'⟩)]
    · exact hcpo j hj _ _
  have hid : ∀ j : Fin 3, (c1.st j).id = rid32 j := by
    intro j; by_cases hj : j = a
    · subst hj; rw [hsta, hs1id]; exact I.ids _
    · rw [hsto j hj]; exact I.ids j
  have hcrt : ∀ (j : Fin 3) q', (c1.st j).crt q' = (c.st j).crt q' := by
    intro j q'; by_cases hj : j = a
    · subst hj; rw [hsta]; simp only [RState.crt, hs1crt]
    · rw [hsto j hj]
  have hbal : ∀ q' i', balOf c1 q' i' = balOf c q' i' := by
    intro q' i'; funext j; simp only [balOf]
    by_cases hn : j = a ∧ q' = q ∧ i' = i
    · obtain ⟨rfl, rfl, rfl⟩ := hn
      rw [hcpa, if_pos ⟨rfl, rfl⟩, hc0]; simp [hb]
    · rw [hcpn j q' i' hn]
  have E : ∀ q' i', Evolve (rowOf q') (G q' i') (balOf c q' i') (G' q' i') (balOf c1 q' i') := by
    intro q' i'; rw [hbal]
    by_cases hq : q' = q ∧ i' = i
    · obtain ⟨rfl, rfl⟩ := hq; exact hE
    · rw [hGo q' i' hq]; exact Evolve.refl (I.inst q' i').ainv
  have hcre : ∀ q' i' v, (G' q' i').cre v → (G q' i').cre v := by
    intro q' i' v h; by_cases hq : q' = q ∧ i' = i
    · obtain ⟨rfl, rfl⟩ := hq; exact X.cre v h
    · rw [hGo q' i' hq] at h; exact h
  have hcnt := countP_step hinf hze hz
  have hle : ∀ (j : Fin 3) (p : Msg → Bool), (∀ d y, y ∈ sentR d o → p y = false) →
      (infR c1 j).countP p ≤ (infR c j).countP p := by
    intro j p hp
    have e := hcnt j p
    have : (sentR j o).countP p = 0 := List.countP_eq_zero.2 fun y hy => by simp [hp j y hy]
    omega
  have I0 := I.inst q i
  refine ⟨⟨hid, fun q' i' => ?_, fun (d : Fin 3) (y : Msg) hy => ?_, fun j q' => ?_,
    fun j q' i' cp hc => ?_, fun (d : Fin 3) (y : Msg) q' j hy hj => ?_, fun (j : Fin 3) => ?_,
    fun (q0 : Fin 3) j0 h0 h1 => ?_, fun (R' : Fin 3) q' i' cp lb hc hl hp hnc ho => ?_⟩, E⟩
  · -- instances
    by_cases hq : q' = q ∧ i' = i
    · obtain ⟨h1, h2⟩ := hq; subst q' i'
      refine ⟨by rw [hbal]; exact hA, fun j cp hc => ?_, fun j hc => ?_, fun v hv => ?_,
        fun _ => ?_, fun b' R' h1 h2 => ?_, fun hn => ?_⟩
      · by_cases hj : j = a
        · subst hj; rw [hcpa, if_pos ⟨rfl, rfl⟩] at hc; cases hc
          exact copyOk_balEq (hbal _ _) hnew
        · rw [hcpo j hj] at hc
          exact copyOk_ext X hj (E _ _) (I0.copies j cp hc)
      · by_cases hj : j = a
        · subst hj; rw [hcpa, if_pos ⟨rfl, rfl⟩] at hc; cases hc
        · rw [hcpo j hj] at hc
          obtain ⟨k1, k2⟩ := I0.noCopy j hc
          exact ⟨fun b' u hu => k1 b' u ((X.acc j b' u hu).resolve_right hj), fun h' => k2 (X.eq j h')⟩
      · obtain ⟨cpx, hx1, hx2⟩ := I0.fastL v (X.fast v hv)
        by_cases hj : rowOf q = a
        · rw [hj, hcpa, if_pos ⟨rfl, rfl⟩]; rw [hj, hc0] at hx1; cases hx1
          exact ⟨cp', rfl, hcomm hx2⟩
        · rw [hcpo _ hj]; exact ⟨cpx, hx1, hx2⟩
      · obtain ⟨cpL, hL, hLn⟩ := I0.leaderCopy ⟨a, cp0, hc0⟩
        by_cases hj : rowOf q = a
        · rw [hj, hcpa, if_pos ⟨rfl, rfl⟩]; rw [hj, hc0] at hL; cases hL
          refine ⟨cp', rfl, ?_⟩
          rcases hstn with h' | h'
          · exact h'
          · rw [h']; exact hLn
        · rw [hcpo _ hj]; exact ⟨cpL, hL, hLn⟩
      · rw [hbal]
        have h2' : (G q i).rst b' ∨ ∃ u, (G q i).prop b' u ∨ (Own b' a ∧ b' ≤ sint.Z cp'.ballot) := by
          rcases h2 with h2 | ⟨u, h2⟩
          · rcases X.rst _ h2 with h2 | h2
            · exact Or.inl h2
            · exact Or.inr ⟨default, Or.inr h2⟩
          · exact Or.inr ⟨u, X.prop _ _ h2⟩
        rcases h2' with h2' | ⟨u, h2' | ⟨ho, hle'⟩⟩
        · exact I0.ownMono b' R' h1 (Or.inl h2')
        · exact I0.ownMono b' R' h1 (Or.inr ⟨u, h2'⟩)
        · obtain rfl := own_uniq h1 ho
          refine ⟨sint.Z cp0.ballot, ?_, by rw [← hb]; exact hle'⟩
          simp only [balOf, hc0, Option.map_some]
      · have := hn a; rw [hcpa, if_pos ⟨rfl, rfl⟩] at this; cases this
    · have hcq : ∀ j, cpOf c1 j q' i' = cpOf c j q' i' :=
        fun j => hcpn j q' i' (fun h' => hq h'.2)
      have eG := hGo q' i' hq
      refine ⟨?_, fun j cp hc => ?_, fun j hc => ?_, fun v hv => ?_, fun h' => ?_,
        fun b' R' h1 h2 => ?_, fun hn => ?_⟩ <;> (try rw [eG])
      · rw [hbal]; exact (I.inst q' i').ainv
      · rw [hcq] at hc
        exact copyOk_Geq eG (copyOk_balEq (hbal _ _) ((I.inst q' i').copies j cp hc))
      · rw [hcq] at hc; exact (I.inst q' i').noCopy j hc
      · rw [eG] at hv; rw [hcq]; exact (I.inst q' i').fastL v hv
      · simp only [hcq] at h' ⊢; exact (I.inst q' i').leaderCopy h'
      · rw [eG] at h2; rw [hbal]; exact (I.inst q' i').ownMono b' R' h1 h2
      · exact (I.inst q' i').fresh (fun j => (hcq j).symm.trans (hn j))
  · -- messages
    rcases mem_step hinf hze (y := y) hy with hy1 | hy1
    · refine msgOk_evolve E hcre (fun x hx _ hc0' hc1 => ?_) (I.msgs d y hy1)
      subst hx
      refine ⟨fun cp hc => ?_, ?_⟩
      · by_cases hq : d = a ∧ x.replica = q ∧ x.inst = i
        · obtain ⟨rfl, h1, h2⟩ := hq
          rw [hcpa, if_pos ⟨h1, h2⟩] at hc; cases hc
          rw [← h1, ← h2] at hc0
          rcases hpa0 with h' | h'
          · exact Or.inl (by rw [hb]; exact h')
          · have := hc0' cp0 hc0; rw [h', hb]; exact this
        · rw [hcpn d _ _ hq] at hc; exact hc0' cp hc
      · have k := hcnt d (fun y => y == Msg.preAccept x)
        have e1 : (c1.inflight d).count (Msg.preAccept x : gNet.M) =
            (infR c1 d).countP (fun y => y == Msg.preAccept x) := rfl
        have e2 : (c.inflight d).count (Msg.preAccept x : gNet.M) =
            (infR c d).countP (fun y => y == Msg.preAccept x) := rfl
        rw [e1]; rw [e2] at hc1
        have z1 : (z == Msg.preAccept x) = false := by simpa using hzpa x
        have z2 : (sentR d o).countP (fun y => y == Msg.preAccept x) = 0 := by
          refine List.countP_eq_zero.2 fun y hy => ?_
          have := (hsent d y hy).2.2.1
          simp only [beq_iff_eq]
          intro hyx; exact this x hyx (by assumption)
        rw [z2] at k
        split at k
        · rename_i hh; rw [z1] at hh; exact absurd hh.2 (by simp)
        · omega
    · exact (hsent d y hy1).1
  · rw [hcrt, hcrt]; exact I.crtOwn j q'
  · rw [hcrt]
    by_cases hj : j = a ∧ q' = q ∧ i' = i
    · obtain ⟨h1, h2, h3⟩ := hj; subst j q' i'; exact I.copyBelow _ _ _ cp0 hc0
    · rw [hcpn j q' i' hj] at hc; exact I.copyBelow j q' i' cp hc
  · rw [hcrt]
    rcases mem_step hinf hze (y := y) hy with hy1 | hy1
    · exact I.msgBelow d y q' j hy1 hj
    · rcases (hsent d y hy1).2.1 with h' | h'
      · rw [h'] at hj; cases hj
      · rw [h'] at hj; cases hj; exact I.copyBelow _ _ _ cp0 hc0
  · by_cases hj : j = a
    · subst hj; rw [hsta, hs1crt]; exact I.crtLen _
    · rw [hsto j hj]; exact I.crtLen j
  · rw [hcrt] at h1
    obtain ⟨cp, hc, hn⟩ := I.leaderHas q0 j0 h0 h1
    by_cases hj : q0 = a ∧ rid32 q0 = q ∧ j0 = i
    · obtain ⟨h1', h2', h3'⟩ := hj; subst h1'; rw [hcpa, if_pos ⟨h2', h3'⟩]
      rw [h2', h3', hc0] at hc; cases hc
      refine ⟨cp', rfl, ?_⟩
      rcases hstn with h' | h'
      · exact h'
      · rw [h']; exact hn
    · rw [hcpn q0 _ _ hj]; exact ⟨cp, hc, hn⟩
  · -- multiplicities
    by_cases hA' : R' = a ∧ q' = q ∧ i' = i
    · obtain ⟨h1, h2, h3⟩ := hA'; subst R' q' i'
      rw [hcpa, if_pos ⟨rfl, rfl⟩] at hc; cases hc
      exact hpm lb hl hp hnc ho
    · rw [hcpn R' q' i' hA'] at hc
      obtain ⟨k1, k2⟩ := I.prepMult R' q' i' cp lb hc hl hp hnc ho
      have hP : ∀ Y : Fin 3, (infR c1 Y).countP (isPrepareAt q' i' cp.ballot) ≤
          (infR c Y).countP (isPrepareAt q' i' cp.ballot) :=
        fun Y => hle Y _ fun d y hy => (hsent d y hy).2.2.2.1 _ _ _
      have hO : ∀ Y : Fin 3, (infR c1 R').countP (isOKReplyAt q' i' cp.ballot Y) ≤
          (infR c R').countP (isOKReplyAt q' i' cp.ballot Y) :=
        fun Y => hle R' _ fun d y hy => (hsent d y hy).2.2.2.2 _ _ _ _
      refine ⟨fun Y => ?_, fun h1 => ?_⟩
      · have k := k1 Y; have := hP Y; have := hO Y
        change (infR c Y).countP _ + (infR c R').countP _ ≤ 1 at k
        change (infR c1 Y).countP _ + (infR c1 R').countP _ ≤ 1
        omega
      · obtain ⟨hRL, hP0, hO0⟩ := k2 h1
        change (infR c _).countP _ = 0 at hP0
        change (infR c R').countP _ = 0 at hO0
        refine ⟨hRL, ?_, ?_⟩
        · change (infR c1 _).countP _ = 0
          have := hP (rowOf q'); omega
        · change (infR c1 R').countP _ = 0
          have := hO (rowOf q'); omega

/-! ## Broadcasts, `startPhase1` -/

theorem mapM_memA {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → ∀ y ∈ r, ∃ a ∈ l, f a = some y
  | [], r, h => by simp at h; subst h; simp
  | a :: l, r, h => by
    simp only [List.mapM_cons, bind, Option.bind] at h
    cases hfa : f a with
    | none => simp [hfa] at h
    | some b =>
      simp only [hfa] at h
      cases hl : l.mapM f with
      | none => simp [hl] at h
      | some bs =>
        simp only [hl, pure, Option.some.injEq] at h
        subst h
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact ⟨a, by simp, hfa⟩
        · obtain ⟨a', ha', h'⟩ := mapM_memA hl y hy
          exact ⟨a', by simp [ha'], h'⟩

theorem dstOf_some {q : w32} {d : Fin 3} (h : dstOf q = some d) : rid32 d = q := by
  unfold dstOf at h
  split at h
  · rename_i h'
    cases h
    have e : rowOf q = ⟨(sint.Z q).toNat, by omega⟩ := by
      unfold rowOf; rw [dite_eq_left_of_eq_true (eq_true h')]
    rw [← e]; exact rid32_rowOf (by unfold rowOk; exact decide_eq_true h')
  · cases h

theorem mem_sentR {o : List Out} {d : Fin 3} {y : Msg} (h : y ∈ sentR d o) : Out.send d y ∈ o := by
  unfold sentR at h
  obtain ⟨x, hx, hx'⟩ := List.mem_filterMap.1 h
  cases x with
  | send d' m' =>
    simp only at hx'
    split at hx'
    · cases hx'; subst_vars; exact hx
    · cases hx'
  | ext x => cases hx'

/-- A broadcast's messages: `msg`, to peers. -/
theorem bcast_sent' {s : RState} {msg : Msg} {o : List Out}
    (h : bcast s msg = some o) : ∀ (d : Fin 3) y, y ∈ sentR d o → y = msg ∧ rid32 d ≠ s.id := by
  intro d y hy
  obtain ⟨q, -, hq⟩ := mapM_memA h _ (mem_sentR hy)
  unfold sendPeer at hq; split at hq
  · cases hq
  · rename_i hne
    unfold sendTo at hq
    obtain ⟨d', hd', e⟩ := Option.map_eq_some_iff.1 hq
    cases e
    exact ⟨rfl, by rw [dstOf_some hd']; exact hne⟩

theorem bcast_sent {s : RState} {a : Fin 3} {msg : Msg} {o : List Out} (hid : s.id = rid32 a)
    (h : bcast s msg = some o) : ∀ (d : Fin 3) y, y ∈ sentR d o → y = msg ∧ d ≠ a := by
  intro d y hy
  obtain ⟨q, -, hq⟩ := mapM_memA h _ (mem_sentR hy)
  unfold sendPeer at hq; split at hq
  · cases hq
  · rename_i hne
    unfold sendTo at hq
    obtain ⟨d', hd', e⟩ := Option.map_eq_some_iff.1 hq
    cases e
    refine ⟨rfl, fun hda => hne ?_⟩
    rw [hid, ← hda, dstOf_some hd']

/-- `stepPrepareReply` needs the copy. -/
theorem stepPrepareReply_some {s s' : RState} {m : PrepareReplyM} {o : List Out}
    (h : stepPrepareReply s m = .ok (s', o)) : ∃ c, s.inst m.replica m.inst = some c := by
  rcases hc : s.inst m.replica m.inst with _ | c
  · unfold stepPrepareReply at h
    by_cases hcmd : cmdsOk m.cmds = true
    · by_cases hbox : inBox m.replica m.inst = true
      · simp [hcmd, hbox, hc, dead, FailM.failDead] at h
      · simp [hcmd, hbox, dead, FailM.failDead, bind, Except.bind] at h
    · simp [hcmd, never, FailM.failNever, bind, Except.bind] at h
  · exact ⟨c, rfl⟩

/-- `startPhase1`'s result: one new PREACCEPTED copy at the ballot (not preparing), PreAccepts at the
ballot. -/
theorem startPhase1_facts {s s' : RState} {q i b : w32} {ps : List Proposal} {cmds : List Cmd}
    {o : List Out} (h : startPhase1 s q i b ps cmds = .ok (s', o)) :
    ∃ cp, (∀ q' i', s'.inst q' i' = if q' = q ∧ i' = i then some cp else s.inst q' i') ∧
      s'.id = s.id ∧ s'.crtInstance = s.crtInstance ∧ cp.ballot = b ∧ cp.vbal = b ∧
      cp.status = St.PREACCEPTED ∧ (∀ lb, cp.lb = some lb → lb.preparing = false) ∧
      ∀ (d : Fin 3) y, y ∈ sentR d o → ∃ x : PreAcceptM, y = .preAccept x ∧ x.leaderId = s.id ∧
        x.replica = q ∧ x.inst = i ∧ x.ballot = b ∧ rid32 d ≠ s.id := by
  unfold startPhase1 at h
  peel h
  all_goals (
    rename_i hbc
    cases h
    obtain ⟨e1, e2, e3⟩ := updateConflicts_inst (s.setInst q i _) cmds q i _
    refine ⟨_, fun q' i' => by rw [e1]; rfl, e2, e3, rfl, rfl, rfl, fun lb hl => by cases hl; rfl, ?_⟩
    intro d y hy
    obtain ⟨h1, h2⟩ := bcast_sent' hbc d y hy
    exact ⟨_, h1, e2, rfl, rfl, rfl, by rw [e2] at h2; exact h2⟩)

theorem com_facts : isCommitted St.COMMITTED ∧ ¬ isPre St.COMMITTED ∧ St.COMMITTED ≠ St.NONE ∧
    St.COMMITTED ≠ St.ACCEPTED ∧ St.COMMITTED ≠ St.PREACCEPTED_EQ ∧ St.COMMITTED ≠ St.PREACCEPTED := by
  unfold isCommitted isPre; decide

theorem acc_facts : ¬ isCommitted St.ACCEPTED ∧ ¬ isPre St.ACCEPTED ∧ St.ACCEPTED ≠ St.NONE ∧
    St.ACCEPTED ≠ St.PREACCEPTED_EQ ∧ St.ACCEPTED ≠ St.PREACCEPTED := by
  unfold isCommitted isPre; decide

theorem pre_facts : ¬ isCommitted St.PREACCEPTED ∧ isPre St.PREACCEPTED ∧ St.PREACCEPTED ≠ St.NONE ∧
    St.PREACCEPTED ≠ St.PREACCEPTED_EQ ∧ St.PREACCEPTED ≠ St.ACCEPTED := by
  unfold isCommitted isPre; decide

/-- A replica's votes are at most its copy's ballot (not committed). -/
theorem votes_le_ballot {c : Cfg gNet} {G : GG} {q i : w32} {a : Fin 3} {cp : Copy}
    (k : CopyOk c G q i a cp) (hnc : ¬ isCommitted cp.status) :
    ∀ b' u, (G q i).acc a b' u → b' ≤ sint.Z cp.ballot := by
  intro b' u hu
  rcases k.stOk with h' | h' | h' | h'
  · exact absurd hu (k.noVotes (Or.inl h') b' u)
  · exact absurd hu (k.noVotes (Or.inr h') b' u)
  · have := (k.accVote h').2 b' u hu; have := k.vbalLe; omega
  · exact absurd h' hnc

/-- The Accept decisions (an ACCEPTED or counted candidate, a no-op): the recoverer's copy becomes
ACCEPTED at its ballot with the proposal `c'.valA`, Accepts to the peers. -/
theorem accept_branch {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {m : PrepareReplyM} {s' : RState}
    {o : List Out} {cp0 c' : Copy} (I : CInv c G)
    (hst : c1.st = fun j => if j = a then s' else c.st j)
    (hinf : c1.inflight = fun j =>
      (if j = a then consume (gNet.recv (.msg (.prepareReply m))) (c.inflight j) else c.inflight j) ++
        sentTo gNet j o)
    (hm' : Msg.prepareReply m ∈ infR c a)
    (hc0' : cpOf c a m.replica m.inst = some cp0) (hnc' : ¬ isCommitted cp0.status)
    (hown : Own (sint.Z cp0.ballot) a)
    (hs' : s' = (c.st a).setInst m.replica m.inst c')
    (hbc : bcastAccept ((c.st a).setInst m.replica m.inst c') m.replica m.inst c'.ballot c'.cmds
      c'.seq c'.deps c'.base = some o)
    (hs : c'.status = St.ACCEPTED) (hcb : c'.ballot = cp0.ballot) (hcv : c'.vbal = cp0.ballot)
    (hcl : ∀ lb, c'.lb = some lb → lb.preparing = false)
    (hAE : AInv ((G m.replica m.inst).addProp (sint.Z cp0.ballot) c'.valA a)
        (balOf c m.replica m.inst) (rowOf m.replica) ∧
      Evolve (rowOf m.replica) (G m.replica m.inst) (balOf c m.replica m.inst)
        ((G m.replica m.inst).addProp (sint.Z cp0.ballot) c'.valA a) (balOf c m.replica m.inst)) :
    ∃ G', CInv c1 G' ∧ ∀ q i, Evolve (rowOf q) (G q i) (balOf c q i) (G' q i) (balOf c1 q i) := by
  have k0 := (I.inst m.replica m.inst).copies a cp0 hc0'
  have hvl := votes_le_ballot k0 hnc'
  let g' := (G m.replica m.inst).addProp (sint.Z cp0.ballot) c'.valA a
  have hG : GG.set G m.replica m.inst g' m.replica m.inst = g' := if_pos ⟨rfl, rfl⟩
  have hGo : ∀ q' i', ¬ (q' = m.replica ∧ i' = m.inst) →
      GG.set G m.replica m.inst g' q' i' = G q' i' := fun q' i' h => if_neg h
  have X : ExtA (G m.replica m.inst) (GG.set G m.replica m.inst g' m.replica m.inst) a
      (sint.Z c'.ballot) := by
    rw [hG, hcb]; exact ExtA.addProp _ _ hown
  have hnew0 : CopyOk c (fun _ _ => g') m.replica m.inst a c' := by
    refine ⟨by rw [hcb]; exact k0.nonneg, by rw [hcb]; exact k0.ballotForm,
      by rw [hcv, hcb]; exact Int.le_refl _, Or.inr (Or.inr (Or.inl hs)), fun h' => ?_, fun _ => ?_,
      fun h' => absurd (hs ▸ h') acc_facts.1, fun h' => absurd (hs ▸ h') acc_facts.2.1,
      fun h' => absurd (hs.symm.trans h') acc_facts.2.2.2.1,
      fun _ _ h' => absurd (hs.symm.trans h') acc_facts.2.2.2.2, fun h' => ?_,
      fun lb hl hp => absurd ((hcl lb hl).symm.trans hp) (by decide), fun _ _ => Or.inl hs⟩
    · rcases h' with h' | h'
      · exact absurd (hs.symm.trans h') acc_facts.2.2.1
      · exact absurd (hs ▸ h') acc_facts.2.1
    · refine ⟨Or.inr ⟨rfl, by rw [hcv], rfl⟩, fun b' u hu => ?_⟩
      rcases hu with hu | ⟨_, h2, _⟩
      · rw [hcv]; exact hvl b' u hu
      · rw [hcv, h2]; exact Int.le_refl _
    · rcases h' with h' | h'
      · exact absurd (hs.symm.trans h') acc_facts.2.2.1
      · exact absurd (hs ▸ h') acc_facts.2.1
  have hnew := copyOk_Geq (G := fun _ _ => g') hG hnew0
  have hid : ((c.st a).setInst m.replica m.inst c').id = rid32 a := I.ids a
  refine ⟨GG.set G m.replica m.inst g', oneCopy_inv I hst hinf rfl hm' (fun x h => by cases h)
    (fun q' i' => by rw [hs']; rfl) (by rw [hs']; rfl) (by rw [hs']; rfl) hc0' hcb
    (fun h => absurd h hnc') (Or.inl (by rw [hs]; exact acc_facts.2.2.1)) (Or.inl (own_pos hown))
    hGo X (by rw [hG]; exact hAE.1) (by rw [hG]; exact hAE.2) hnew
    (fun lb hl hp => absurd ((hcl lb hl).symm.trans hp) (by decide)) ?_⟩
  intro d y hy
  obtain ⟨rfl, hda⟩ := bcast_sent hid hbc d y hy
  refine ⟨?_, Or.inr rfl, fun x hx => (by cases hx), fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  simp only [MsgOk]
  rw [hG]
  exact ⟨Or.inr ⟨by rw [hcb], rfl⟩, a, hid, fun e => hda e.symm, Or.inr (by rw [hcb]; exact hown),
    Or.inr ⟨rfl, by rw [hcb], rfl⟩⟩

/-- The restart decision: `startPhase1` at the recoverer's ballot. -/
theorem restart_branch {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {m : PrepareReplyM} {s' : RState}
    {o : List Out} {cp0 : Copy} {lbx : LB} {ps : List Proposal} {cmds : List Cmd} (I : CInv c G)
    (hst : c1.st = fun j => if j = a then s' else c.st j)
    (hinf : c1.inflight = fun j =>
      (if j = a then consume (gNet.recv (.msg (.prepareReply m))) (c.inflight j) else c.inflight j) ++
        sentTo gNet j o)
    (hm' : Msg.prepareReply m ∈ infR c a)
    (hc0' : cpOf c a m.replica m.inst = some cp0) (hnc' : ¬ isCommitted cp0.status)
    (hown : Own (sint.Z cp0.ballot) a)
    (hnp : ∀ u, ¬ (G m.replica m.inst).prop (sint.Z cp0.ballot) u)
    (hvb : ∀ b' u, b' < sint.Z cp0.ballot → (G m.replica m.inst).acc a b' u → False)
    (hpm : startPhase1 ((c.st a).setInst m.replica m.inst { cp0 with lb := some lbx })
      m.replica m.inst cp0.ballot ps cmds = .ok (s', o))
    (hAE : AInv ((G m.replica m.inst).addRst (sint.Z cp0.ballot))
        (balOf c m.replica m.inst) (rowOf m.replica) ∧
      Evolve (rowOf m.replica) (G m.replica m.inst) (balOf c m.replica m.inst)
        ((G m.replica m.inst).addRst (sint.Z cp0.ballot)) (balOf c m.replica m.inst)) :
    ∃ G', CInv c1 G' ∧ ∀ q i, Evolve (rowOf q) (G q i) (balOf c q i) (G' q i) (balOf c1 q i) := by
  obtain ⟨cp', hinst, hid', hcrt', hballot, hvbal, hstat, hlbp, hsentPA⟩ := startPhase1_facts hpm
  have k0 := (I.inst m.replica m.inst).copies a cp0 hc0'
  have hvl := votes_le_ballot k0 hnc'
  have hb0 := own_pos hown
  have hnov : ∀ b' u, ¬ (G m.replica m.inst).acc a b' u := by
    intro b' u hu
    rcases Int.lt_or_eq_of_le (hvl b' u hu) with hlt | heq
    · exact hvb b' u hlt hu
    · subst heq; exact hnp u ((I.inst _ _).ainv.acc_prop _ _ _ hu)
  let g' := (G m.replica m.inst).addRst (sint.Z cp0.ballot)
  have hG : GG.set G m.replica m.inst g' m.replica m.inst = g' := if_pos ⟨rfl, rfl⟩
  have hGo : ∀ q' i', ¬ (q' = m.replica ∧ i' = m.inst) →
      GG.set G m.replica m.inst g' q' i' = G q' i' := fun q' i' h => if_neg h
  have X : ExtA (G m.replica m.inst) (GG.set G m.replica m.inst g' m.replica m.inst) a
      (sint.Z cp'.ballot) := by
    rw [hG, hballot]; exact ExtA.addRst _ hown
  have hb' : sint.Z cp'.ballot = sint.Z cp0.ballot := by rw [hballot]
  have hv' : sint.Z cp'.vbal = sint.Z cp0.ballot := by rw [hvbal]
  have hnew0 : CopyOk c (fun _ _ => g') m.replica m.inst a cp' := by
    refine ⟨by rw [hb']; exact k0.nonneg, by rw [hballot]; exact k0.ballotForm,
      by rw [hv', hb']; exact Int.le_refl _, Or.inr (Or.inl (Or.inl hstat)), fun _ => hnov,
      fun h' => absurd (hstat.symm.trans h') pre_facts.2.2.2.2,
      fun h' => absurd (hstat ▸ h') pre_facts.1, fun _ _ => ⟨by rw [hv']; exact hb0, Or.inr hv'⟩,
      fun h' => absurd (hstat.symm.trans h') pre_facts.2.2.2.1, fun _ h0 _ => ?_,
      fun _ _ u hu => hnp u (hb' ▸ hu), fun lb hl hp => absurd ((hlbp lb hl).symm.trans hp) (by decide),
      fun _ _ => Or.inr (Or.inr (Or.inr ⟨_, hb0, by rw [hb']; exact Int.le_refl _, Or.inr rfl⟩))⟩
    have := z_zero h0; omega
  have hnew := copyOk_Geq (G := fun _ _ => g') hG hnew0
  have hid : (c.st a).id = rid32 a := I.ids a
  refine ⟨GG.set G m.replica m.inst g', oneCopy_inv I hst hinf rfl hm' (fun x h => by cases h)
    (fun q' i' => ?_) hid' hcrt' hc0' hballot
    (fun h => absurd h hnc') (Or.inl (by rw [hstat]; exact pre_facts.2.2.1)) (Or.inl hb0)
    hGo X (by rw [hG]; exact hAE.1) (by rw [hG]; exact hAE.2) hnew
    (fun lb hl hp => absurd ((hlbp lb hl).symm.trans hp) (by decide)) ?_⟩
  · rw [hinst]; split
    · rfl
    · rename_i hq; exact if_neg hq
  · intro d y hy
    obtain ⟨x, rfl, hxl, hxr, hxi, hxb, hd⟩ := hsentPA d y hy
    have hxb' : sint.Z x.ballot = sint.Z cp0.ballot := by rw [hxb]
    refine ⟨?_, Or.inr (by simp [msgInst, hxr, hxi]), fun x' hx' => ?_, fun _ _ _ => rfl,
      fun _ _ _ _ => rfl⟩
    · simp only [MsgOk]
      rw [hxr, hxi, hG]
      refine ⟨fun h0 => ?_, fun _ => ⟨by rw [hxb']; exact hb0, Or.inr hxb', a, by rw [hxb']; exact hown,
        by rw [hxl]; exact hid, fun e => hd (by rw [← e]; exact hid.symm)⟩⟩
      have := z_zero h0; omega
    · cases hx'; intro h0; have := z_zero h0; omega

/-! ## `handlePrepareReply` -/

/-- **`stepPrepareReply` keeps the invariant.** -/
theorem prepareReply_inv {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {m : PrepareReplyM} {s' : RState}
    {o : List Out} (I : CInv c G)
    (hst : c1.st = fun j => if j = a then s' else c.st j)
    (hinf : c1.inflight = fun j =>
      (if j = a then consume (gNet.recv (.msg (.prepareReply m))) (c.inflight j) else c.inflight j) ++
        sentTo gNet j o)
    (hm : Msg.prepareReply m ∈ c.inflight a) (h : stepPrepareReply (c.st a) m = .ok (s', o)) :
    ∃ G', CInv c1 G' ∧ ∀ q i, Evolve (rowOf q) (G q i) (balOf c q i) (G' q i) (balOf c1 q i) := by
  have hze : gNet.recv (.msg (.prepareReply m)) = some (.prepareReply m) := rfl
  have hm' : Msg.prepareReply m ∈ infR c a := hm
  have hzpa : ∀ x, Msg.prepareReply m ≠ .preAccept x := fun x h => by cases h
  have hcnt := countP_step hinf hze hm'
  have hdec : o = [] → ∀ (j : Fin 3) p, (infR c1 j).countP p ≤ (infR c j).countP p := by
    intro ho j p; have := hcnt j p; subst ho; simp only [sentR, List.filterMap_nil,
      List.countP_nil] at this; omega
  obtain ⟨cp0, hc0⟩ := stepPrepareReply_some h
  have hc0' : cpOf c a m.replica m.inst = some cp0 := hc0
  have hid := I.ids a
  have hMsg := I.msgs a _ hm
  have k0 := (I.inst m.replica m.inst).copies a cp0 hc0'
  have hnosent : ∀ (d : Fin 3) y, y ∉ sentR d [] := fun d y hy => by simp [sentR] at hy
  rcases stepPrepareReply_cases h with ⟨rfl, rfl⟩ | ⟨c0, lb0, hc, hl, rfl, rfl⟩ |
    ⟨c0, lb0, hc, hl, hp, hnc, hok, hb, hms, rfl, hbc⟩ |
    ⟨c0, lb0, hc, hl, hp, hnc, hok, hb, hms, hcmd, hbox, hpm⟩
  · -- nothing changes
    refine ⟨G, oneCopy_inv (cp' := cp0) (G' := G) I hst hinf hze hm' hzpa (fun q' i' => ?_) rfl rfl
      hc0' rfl id (Or.inr rfl) (Or.inr rfl) (fun _ _ _ => rfl) (ExtA.refl _ _ _)
      (I.inst _ _).ainv (Evolve.refl (I.inst _ _).ainv) k0 (fun lb hl hp hnc ho => ?_)
      (fun d y hy => absurd hy (hnosent d y))⟩
    · split
      · rename_i hq; obtain ⟨h1, h2⟩ := hq; subst h1 h2; exact hc0
      · rfl
    · obtain ⟨k1, k2⟩ := I.prepMult a _ _ cp0 lb hc0' hl hp hnc ho
      refine ⟨fun Y => ?_, fun h1 => ?_⟩
      · have k := k1 Y
        change (infR c Y).countP _ + (infR c a).countP _ ≤ 1 at k
        have := hdec rfl Y (isPrepareAt m.replica m.inst cp0.ballot)
        have := hdec rfl a (isOKReplyAt m.replica m.inst cp0.ballot Y)
        omega
      · obtain ⟨j1, j2, j3⟩ := k2 h1
        change (infR c _).countP _ = 0 at j2
        change (infR c a).countP _ = 0 at j3
        have := hdec rfl (rowOf m.replica) (isPrepareAt m.replica m.inst cp0.ballot)
        have := hdec rfl a (isOKReplyAt m.replica m.inst cp0.ballot (rowOf m.replica))
        exact ⟨j1, by omega, by omega⟩
  · -- a NACK counted
    rw [hc] at hc0; cases hc0
    have hnew : CopyOk c G m.replica m.inst a
        { cp0 with lb := some { lb0 with nacks := lb0.nacks + 1 } } := by
      refine { k0 with leader0 := leader0_lb (cp := cp0) k0 hl rfl, preparing := fun lb hl' hp hnc ho => ?_ }
      cases hl'; exact k0.preparing lb0 hl hp hnc ho
    refine ⟨G, oneCopy_inv (G' := G) I hst hinf hze hm' hzpa (fun q' i' => rfl) rfl rfl
      hc0' rfl id (Or.inr rfl) (Or.inr rfl) (fun _ _ _ => rfl) (ExtA.refl _ _ _)
      (I.inst _ _).ainv (Evolve.refl (I.inst _ _).ainv) hnew (fun lb hl' hp hnc ho => ?_)
      (fun d y hy => absurd hy (hnosent d y))⟩
    cases hl'
    dsimp only at hp hnc ho ⊢
    obtain ⟨k1, k2⟩ := I.prepMult a _ _ cp0 lb0 hc0' hl hp hnc ho
    refine ⟨fun Y => ?_, fun h1 => ?_⟩
    · have k := k1 Y
      change (infR c Y).countP _ + (infR c a).countP _ ≤ 1 at k
      have := hdec rfl Y (isPrepareAt m.replica m.inst cp0.ballot)
      have := hdec rfl a (isOKReplyAt m.replica m.inst cp0.ballot Y)
      omega
    · obtain ⟨j1, j2, j3⟩ := k2 h1
      change (infR c _).countP _ = 0 at j2
      change (infR c a).countP _ = 0 at j3
      have := hdec rfl (rowOf m.replica) (isPrepareAt m.replica m.inst cp0.ballot)
      have := hdec rfl a (isOKReplyAt m.replica m.inst cp0.ballot (rowOf m.replica))
      exact ⟨j1, by omega, by omega⟩
  · -- G22: the reply's committed value
    rw [hc] at hc0; cases hc0
    have hok' : m.ok = TRUE := hMsg.2.2.resolve_right hok
    obtain ⟨-, Y, -, -, hown, -⟩ := hMsg.2.1 hok'
    rw [hb] at hown
    have hch := hMsg.1 hms
    refine ⟨G, oneCopy_inv (G' := G) I hst hinf hze hm' hzpa (fun q' i' => rfl) rfl rfl
      hc0' rfl (fun _ => com_facts.1) (Or.inl com_facts.2.2.1) (Or.inl (own_pos hown))
      (fun _ _ _ => rfl) (ExtA.refl _ _ _)
      (I.inst _ _).ainv (Evolve.refl (I.inst _ _).ainv) ?_ (fun lb hl' => nomatch hl') ?_⟩
    · refine ⟨k0.nonneg, k0.ballotForm, Int.le_refl _, Or.inr (Or.inr (Or.inr com_facts.1)),
        fun hs => ?_, fun hs => absurd hs com_facts.2.2.2.1, fun _ => hch, fun hs => absurd hs com_facts.2.1,
        fun hs => absurd hs com_facts.2.2.2.2.1, fun _ _ hs => absurd hs com_facts.2.2.2.2.2,
        fun hs => ?_, fun lb hl' => (nomatch hl'), fun _ _ => Or.inr (Or.inl com_facts.1)⟩
      · rcases hs with hs | hs
        · exact absurd hs com_facts.2.2.1
        · exact absurd hs com_facts.2.1
      · rcases hs with hs | hs
        · exact absurd hs com_facts.2.2.1
        · exact absurd hs com_facts.2.1
    · intro d y hy
      obtain ⟨rfl, -⟩ := bcast_sent hid hbc d y hy
      exact ⟨hch, Or.inr rfl, fun x hx => (by cases hx), fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  · -- the main path
    rw [hc] at hc0; cases hc0
    have hok' : m.ok = TRUE := hMsg.2.2.resolve_right hok
    obtain ⟨⟨B, hB, hle⟩, Y, hYid, hYa, hown, hrep⟩ := hMsg.2.1 hok'
    rw [hb] at hown hle
    have hnc' : ¬ isCommitted cp0.status := hnc
    obtain ⟨hI, hnr, hnp, hp0, hp1⟩ := k0.preparing lb0 hl hp hnc' hown
    have hr := hrep hms (by rw [hb]; exact hnp)
    rw [hb] at hr
    have hb0 := own_pos hown
    have hA := (I.inst m.replica m.inst).ainv
    have hbal : balOf c m.replica m.inst a = some (sint.Z cp0.ballot) := by
      simp only [balOf, hc0', Option.map_some]
    unfold prMain at hpm
    dsimp only at hpm
    split at hpm
    · -- the leader's pre-accepted reply
      rename_i hcond
      have hYL : Y = rowOf m.replica := hr.isL.1 hcond.2.2
      obtain ⟨r, hu, hRI⟩ := riOk_lret hA hb0 hI hr hYL hcond.1
      rw [hu] at hpm
      cases hpm
      have hmL : isOKReplyAt m.replica m.inst cp0.ballot (rowOf m.replica)
          (.prepareReply m) = true := by
        simp only [isOKReplyAt, hb, hok', hYid, ← hYL, beq_self_eq_true, Bool.and_self]
      have hpos : 0 < (infR c a).countP
          (isOKReplyAt m.replica m.inst cp0.ballot (rowOf m.replica)) :=
        List.countP_pos_iff.2 ⟨_, hm', hmL⟩
      obtain ⟨k1, k2⟩ := I.prepMult a _ _ cp0 lb0 hc0' hl hp hnc' hown
      have h00 : sint.Z lb0.prepareOKs = 0 := by
        refine Classical.byContradiction fun hne => ?_
        have := (k2 (by omega)).2.2
        change (infR c a).countP _ = 0 at this
        omega
      have h1 : sint.Z (lb0.prepareOKs + 1) = 1 := by rw [cnt_succ hp0 (by omega), h00]; rfl
      have hnew : CopyOk c G m.replica m.inst a
          { cp0 with lb := some { lb0 with prepareOKs := lb0.prepareOKs + 1,
                                           recoveryInst := some (setLr r) } } := by
        refine { k0 with leader0 := leader0_lb (cp := cp0) k0 hl rfl, preparing := fun lb hl' _ _ _ => ?_ }
        cases hl'
        exact ⟨hRI, hnr, hnp, by dsimp only; omega, by dsimp only; omega⟩
      refine ⟨G, oneCopy_inv (G' := G) I hst hinf hze hm' hzpa (fun q' i' => rfl) rfl rfl
        hc0' rfl id (Or.inr rfl) (Or.inr rfl) (fun _ _ _ => rfl) (ExtA.refl _ _ _) hA
        (Evolve.refl hA) hnew (fun lb hl' _ _ _ => ?_) (fun d y hy => absurd hy (hnosent d y))⟩
      cases hl'
      have kL := k1 (rowOf m.replica)
      change (infR c _).countP _ + (infR c a).countP _ ≤ 1 at kL
      refine ⟨fun Y' => ?_, fun _ => ⟨fun e => hYa (hYL.trans e.symm), ?_, ?_⟩⟩
      · have k := k1 Y'
        change (infR c Y').countP _ + (infR c a).countP _ ≤ 1 at k
        have := hdec rfl Y' (isPrepareAt m.replica m.inst cp0.ballot)
        have := hdec rfl a (isOKReplyAt m.replica m.inst cp0.ballot Y')
        dsimp only; omega
      · have := hdec rfl (rowOf m.replica) (isPrepareAt m.replica m.inst cp0.ballot)
        dsimp only; omega
      · have e := hcnt a (isOKReplyAt m.replica m.inst cp0.ballot (rowOf m.replica))
        rw [if_pos ⟨rfl, hmL⟩] at e
        simp only [sentR, List.filterMap_nil, List.countP_nil] at e
        dsimp only; omega
    · split at hpm
      · -- too few replies: impossible
        rename_i _ hslt
        have := (slt_iff _ _).1 hslt
        rw [cnt_succ hp0 (by omega)] at this
        have : sint.Z NHALF = 1 := by decide
        omega
      · -- the decision
        rename_i hncond _
        have hnot : ¬ (Y = rowOf m.replica ∧ (m.status = St.PREACCEPTED ∨
            m.status = St.PREACCEPTED_EQ) ∧ belowB (upd1 lb0.recoveryInst m) = true) :=
          fun ⟨h1, h2, h3⟩ => hncond ⟨h2, h3, hr.isL.2 h1⟩
        have hRY : a ≠ Y := fun e => hYa e.symm
        unfold prDecide at hpm
        dsimp only at hpm
        split at hpm
        · rename_i ir hu
          split at hpm
          · -- Accept of the candidate
            rename_i hacc
            split at hpm
            · rename_i outs hbc
              cases hpm
              have hacc' : ir.status = St.ACCEPTED ∨ (ir.leaderResponded = false ∧
                  sge ir.preAcceptCount NHALF = true ∧ ir.status = St.PREACCEPTED_EQ) := by
                rcases hacc with h' | ⟨h1, h2, h3⟩
                · exact Or.inl h'
                · exact Or.inr ⟨by simpa using h1, h2, h3⟩
              exact accept_branch I hst hinf hm' hc0' hnc' hown rfl hbc rfl rfl rfl
                (fun lb hl' => by cases hl'; rfl)
                (decide_accept_ainv hA hb0 hI hr hRY hbal hnp hnot hu hacc')
            · exact absurd hpm fail_ne_ok.2.2
          · split at hpm
            · exact absurd hpm fail_ne_ok.2.2
            · -- restart
              rename_i hnacc hntpa0
              have hna : ir.status ≠ St.ACCEPTED := fun h' => hnacc (Or.inl h')
              have hntpa : ¬ (ir.leaderResponded = false ∧
                  sge ir.preAcceptCount ((NHALF + 1) / 2) = true) :=
                fun ⟨h1, h2⟩ => hntpa0 ⟨by simp [h1], h2⟩
              exact restart_branch I hst hinf hm' hc0' hnc' hown hnp
                (fun b' u hb' hu' => by
                  obtain ⟨r', hr', hs', _⟩ := (memOk_upd (m := m) hI.core hI.mem).votes b' u hb' hu'
                  rw [hu] at hr'; cases hr'; exact hna hs')
                hpm (decide_restart_ainv hA hb0 hI hr hRY hnot hu hna hntpa)
        · -- a no-op
          rename_i hu
          split at hpm
          · rename_i outs hbc
            cases hpm
            exact accept_branch I hst hinf hm' hc0' hnc' hown rfl hbc rfl rfl rfl
              (fun lb hl' => by cases hl'; rfl)
              (decide_noop_ainv hA hb0 hI hr hRY hbal hnp hnot hu _)
          · exact absurd hpm fail_ne_ok.2.2

end Perennial.gryff.pureA.A1b
