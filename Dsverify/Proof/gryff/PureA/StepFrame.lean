/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/StepFrame.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A1 (sub-unit A1d), internal: the frame of a step that changes one instance `(q0, i0)` at one
replica `a` (`inv_frame`: `CInv` is kept given the facts about that instance), and helpers shared by
`StepAccept.lean`, `StepAcceptReply.lean`, `StepCommit.lean` (namespace `A1d` to keep the names
apart from the sibling step files).
-/
module

public import Dsverify.Proof.gryff.PureA.Exec

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.A1d

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn Perennial.gryff.pureA

/-! ## Words, ids, ballots -/

theorem crt_setCrt' (s : RState) (q x p : w32) :
    ((s.setCrt q x).crt p = x ∨ (s.setCrt q x).crt p = s.crt p) ∧
    (q ≠ p → (s.setCrt q x).crt p = s.crt p) := by
  simp only [RState.crt, RState.setCrt, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases e : q = p
  · subst e
    refine ⟨?_, fun h => absurd rfl h⟩
    simp only [ite_true]; split
    · simp
    · right; rename_i h; simp [List.getElem?_eq_none (Nat.le_of_not_lt h)]
  · have : q.toNat ≠ p.toNat := fun h => e (BitVec.eq_of_toNat_eq h)
    simp [e, this]

theorem Z_succ32' {x : w32} (h1 : sint.Z x < 2 ^ 31 - 1) : sint.Z (x + 1) = sint.Z x + 1 := by
  simp only [sint.Z] at *
  rw [BitVec.toInt_add]
  have := BitVec.toInt_le (x := x); have := BitVec.le_toInt (x := x)
  simp [Int.bmod]; omega

theorem rid32_rowOf {q : w32} (h : rowOk q = true) : rid32 (rowOf q) = q := by
  simp only [rowOk, decide_eq_true_eq] at h
  unfold rowOf rid32; simp only [h, and_self, dite_true]
  apply BitVec.eq_of_toInt_eq
  simp only [sint.Z] at *
  word

theorem rid32_inj' {a b : Fin 3} (h : rid32 a = rid32 b) : a = b := by
  revert a b; decide

theorem dstOf_rid32' (R : Fin 3) : dstOf (rid32 R) = some R := by
  revert R; decide

theorem Own.pos {b : Int} {R : Fin 3} (h : Own b R) : 0 < b := by
  obtain ⟨k, hk, rfl⟩ := h; omega

theorem Own.uniq {b : Int} {R R' : Fin 3} (h : Own b R) (h' : Own b R') : R = R' := by
  obtain ⟨k, hk, rfl⟩ := h; obtain ⟨k', hk', e⟩ := h'
  have := R.isLt; have := R'.isLt
  apply Fin.ext; omega

theorem sendPeer_dst {s : RState} {R : Fin 3} {m : Msg} {x : Out}
    (h : sendPeer s (rid32 R) m = some x) : x = .send R m := by
  unfold sendPeer at h; split at h
  · cases h
  · unfold sendTo at h; rw [dstOf_rid32'] at h; cases h; rfl

/-- A copy past ballot 0 or accepted/committed (the ballot-0 PreAccept clause of `MsgOk`). -/
def PAcc (cp : Copy) : Prop :=
  0 < sint.Z cp.ballot ∨ cp.status = St.ACCEPTED ∨ isCommitted cp.status

/-- A Prepare, PrepareReply or PreAccept (counted by `CInv`). -/
def isPP : Msg → Bool
  | .prepare _ | .prepareReply _ | .preAccept _ => true
  | _ => false

/-! ## Ghost updates -/

/-- The history with instance `(q0, i0)`'s ghost replaced. -/
def ggSet (G : GG) (q0 i0 : w32) (g : Gh Val) : GG :=
  fun q i => if q = q0 ∧ i = i0 then g else G q i

theorem ggSet_at (G : GG) (q0 i0 : w32) (g : Gh Val) : ggSet G q0 i0 g q0 i0 = g := by
  simp [ggSet]

theorem ggSet_ne (G : GG) {q0 i0 q i : w32} (g : Gh Val) (h : ¬ (q = q0 ∧ i = i0)) :
    ggSet G q0 i0 g q i = G q i := by
  simp only [ggSet, h, ite_false]

/-- The history with a new vote `(b, v)` by `a`. -/
def addAcc (g : Gh Val) (a : Fin 3) (b : Int) (v : Val) : Gh Val :=
  { g with acc := fun a' b' u => g.acc a' b' u ∨ (a' = a ∧ b' = b ∧ u = v) }

theorem le_addAcc (g : Gh Val) (a : Fin 3) (b : Int) (v : Val) : g.Le (addAcc g a b v) :=
  ⟨fun _ _ _ h => Or.inl h, fun _ _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩

/-- `g'` adds nothing about acceptor `a'` (it may add other acceptors' votes). -/
structure Narrow (g g' : Gh Val) (a' : Fin 3) : Prop where
  acc : ∀ b u, g'.acc a' b u → g.acc a' b u
  prop : ∀ b u, g'.prop b u → g.prop b u
  rst : ∀ b, g'.rst b → g.rst b
  cre : ∀ v, g'.cre v → g.cre v
  eq : g'.eq a' → g.eq a'
  fast : ∀ v, g'.fast v → g.fast v

theorem Narrow.refl (g : Gh Val) (a' : Fin 3) : Narrow g g a' :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ h => h, fun _ h => h, fun h => h, fun _ h => h⟩

theorem narrow_addAcc (g : Gh Val) {a a' : Fin 3} (h : a' ≠ a) (b : Int) (v : Val) :
    Narrow g (addAcc g a b v) a' :=
  ⟨fun _ _ hu => hu.elim id (fun k => absurd k.1 h), fun _ _ h => h, fun _ h => h, fun _ h => h,
   fun h => h, fun _ h => h⟩

/-! ## Transport (`balOf_congr'`, `instOk_congr'`: copies of `Inv.lean`'s, which this file cannot
import) -/

theorem balOf_congr' {c c1 : Cfg gNet} {q i : w32} (h : ∀ a, cpOf c1 a q i = cpOf c a q i) :
    balOf c1 q i = balOf c q i := by
  funext a; simp only [balOf, h]

theorem instOk_congr' {c c1 : Cfg gNet} {G : GG} {q i : w32}
    (h : ∀ a, cpOf c1 a q i = cpOf c a q i) (I : InstOk c G q i) : InstOk c1 G q i := by
  have hb := balOf_congr' h
  exact
    { ainv := hb ▸ I.ainv
      copies := fun a cp hc =>
        { I.copies a cp ((h a).symm.trans hc) with
          preparing := by rw [hb]; exact (I.copies a cp ((h a).symm.trans hc)).preparing }
      noCopy := fun a hc => I.noCopy a ((h a).symm.trans hc)
      fastL := fun v hv => by rw [h]; exact I.fastL v hv
      leaderCopy := fun ⟨a, cp, hc⟩ => by
        rw [h]; exact I.leaderCopy ⟨a, cp, (h a).symm.trans hc⟩
      ownMono := fun b R hR hp => by rw [hb]; exact I.ownMono b R hR hp
      fresh := fun hn => I.fresh (fun a => (h a).symm.trans (hn a)) }

theorem copyOk_narrow {c c1 : Cfg gNet} {G G' : GG} {q i : w32} {a' : Fin 3} {cp : Copy}
    (E : Evolve (rowOf q) (G q i) (balOf c q i) (G' q i) (balOf c1 q i))
    (N : Narrow (G q i) (G' q i) a') (h : CopyOk c G q i a' cp) : CopyOk c1 G' q i a' cp where
  nonneg := h.nonneg
  ballotForm := h.ballotForm
  vbalLe := h.vbalLe
  stOk := h.stOk
  noVotes hs b u hu := h.noVotes hs b u (N.acc b u hu)
  accVote hs := ⟨E.le.acc _ _ _ (h.accVote hs).1, fun b u hu => (h.accVote hs).2 b u (N.acc b u hu)⟩
  committed hs := chosen_mono E.le (h.committed hs)
  rstVbal hs hv := ⟨(h.rstVbal hs hv).1, E.le.rst _ (h.rstVbal hs hv).2⟩
  eqCre hs hv ha := E.le.cre _ (h.eqCre hs hv ha)
  leader0 ha hb hs :=
    ⟨E.le.cre _ (h.leader0 ha hb hs).1, fun u hu => (h.leader0 ha hb hs).2.1 u (N.prop _ _ hu),
     fun v hv => (h.leader0 ha hb hs).2.2.1 v (N.fast v hv), (h.leader0 ha hb hs).2.2.2⟩
  ownFresh hs ho u hu := h.ownFresh hs ho u (N.prop _ _ hu)
  preparing lb hl hp hn ho :=
    ⟨riOk_evolve E (Own.pos ho) (h.preparing lb hl hp hn ho).1,
     fun hr => (h.preparing lb hl hp hn ho).2.1 (N.rst _ hr),
     fun u hu => (h.preparing lb hl hp hn ho).2.2.1 u (N.prop _ _ hu),
     (h.preparing lb hl hp hn ho).2.2.2⟩
  eqTrack ha he :=
    (h.eqTrack ha (N.eq he)).imp_right (Or.imp_right (Or.imp_right (rstBelow_mono E.le)))

theorem copyOk_G {c : Cfg gNet} {G G' : GG} {q i : w32} {a : Fin 3} {cp : Copy}
    (h : G' q i = G q i) (hc : CopyOk c G q i a cp) : CopyOk c G' q i a cp := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13⟩ := hc
  refine ⟨f1, f2, f3, f4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [h] <;> assumption

theorem instOk_G {c : Cfg gNet} {G G' : GG} {q i : w32} (h : G' q i = G q i)
    (I : InstOk c G q i) : InstOk c G' q i where
  ainv := by rw [h]; exact I.ainv
  copies a cp hc := copyOk_G h (I.copies a cp hc)
  noCopy a hc := by rw [h]; exact I.noCopy a hc
  fastL v hv := I.fastL v (by rw [h] at hv; exact hv)
  leaderCopy := I.leaderCopy
  ownMono b R hR hp := I.ownMono b R hR (by rw [h] at hp; exact hp)
  fresh hn := by rw [h]; exact I.fresh hn

theorem msgOk_evolve {c c1 : Cfg gNet} {G G' : GG} {d : Fin 3} {m : Msg}
    (E : ∀ q j, Evolve (rowOf q) (G q j) (balOf c q j) (G' q j) (balOf c1 q j))
    (hcre : ∀ q j v, (G' q j).cre v → (G q j).cre v)
    (hP : ∀ q j cp', cpOf c1 d q j = some cp' → (∀ cp, cpOf c d q j = some cp → PAcc cp) →
      PAcc cp')
    (hcnt : ∀ x, m = .preAccept x → (c.inflight d).count (Msg.preAccept x : gNet.M) = 1 →
      (c1.inflight d).count (Msg.preAccept x : gNet.M) = 1)
    (h : MsgOk c G d m) : MsgOk c1 G' d m := by
  cases m with
  | preAccept x =>
    unfold MsgOk at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun hb => ?_, fun hb => ?_⟩
    · obtain ⟨k1, k2, k3, k4, k5⟩ := h1 hb
      exact ⟨k1, k2, (E _ _).le.cre _ k3, fun cp hc => hP _ _ cp hc k4, hcnt x rfl k5⟩
    · obtain ⟨k1, k2, k3⟩ := h2 hb
      exact ⟨k1, (E _ _).le.rst _ k2, k3⟩
  | preAcceptReply x =>
    unfold MsgOk at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun hb => ?_, fun hb ho => ⟨(h2 hb ho).1, (E _ _).le.rst _ (h2 hb ho).2⟩⟩
    obtain ⟨k1, k2, k3⟩ := h1 hb
    refine ⟨k1, fun ho hc => ?_, fun ho => ?_⟩
    · obtain ⟨v, hv, e⟩ := hc
      obtain ⟨X, hX, hq⟩ := k2 ho ⟨v, hcre _ _ v hv, e⟩
      exact ⟨X, hX, (E _ _).le.eq _ hq⟩
    · obtain ⟨v, hv, e⟩ := k3 ho
      exact ⟨v, (E _ _).le.cre _ hv, e⟩
  | preAcceptOK x =>
    obtain ⟨X, hX, hq⟩ := h
    exact ⟨X, hX, (E _ _).le.eq _ hq⟩
  | accept x =>
    obtain ⟨h1, R, k1, k2, k3, k4⟩ := h
    exact ⟨(E _ _).le.prop _ _ h1, R, k1, k2, k3, (E _ _).le.acc _ _ _ k4⟩
  | acceptReply x =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun ho => ?_, h2⟩
    obtain ⟨Y, hY, v, k1, k2⟩ := h1 ho
    exact ⟨Y, hY, v, (E _ _).le.acc _ _ _ k1, (E _ _).le.acc _ _ _ k2⟩
  | commit x => exact chosen_mono (E _ _).le h
  | prepare x =>
    obtain ⟨h1, R, k1, k2, k3, B, hB, hle⟩ := h
    obtain ⟨B', hB', hle'⟩ := (E _ _).bal_mono R B hB
    exact ⟨h1, R, k1, k2, k3, B', hB', Int.le_trans hle hle'⟩
  | prepareReply x =>
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨fun hs => chosen_mono (E _ _).le (h1 hs), fun ho => ?_, h3⟩
    obtain ⟨⟨B, hB, hle⟩, Y, k1, k2, k3, k4⟩ := h2 ho
    obtain ⟨B', hB', hle'⟩ := (E _ _).bal_mono d B hB
    exact ⟨⟨B', hB', Int.le_trans hle hle'⟩, Y, k1, k2, k3,
      fun hn hnp => repOk_evolve (E _ _) (Own.pos k3)
        (k4 hn fun u hu => hnp u ((E _ _).le.prop _ _ hu))⟩
  | _ => trivial

/-! ## In-flight messages after a step -/

theorem mem_sentTo {o : List Out} {d : Fin 3} {m : Msg} (h : m ∈ sentTo gNet d o) :
    Out.send d m ∈ o := by
  unfold sentTo at h
  obtain ⟨y, hy, hy'⟩ := List.mem_filterMap.1 h
  cases y with
  | send d' m' =>
    simp only at hy'
    split at hy'
    · cases hy'; subst_vars; exact hy
    · cases hy'
  | ext x => cases hy'

theorem post_inflight {c c1 : Cfg gNet} {a : Fin 3} {e : Ev} {o : List Out}
    (hinf : c1.inflight = fun j =>
      (if j = a then consume (gNet.recv e) (c.inflight j) else c.inflight j) ++ sentTo gNet j o)
    (d : Fin 3) :
    ∃ l : List gNet.M, List.Sublist l (c.inflight d) ∧ c1.inflight d = l ++ sentTo gNet d o := by
  refine ⟨if d = a then consume (gNet.recv e) (c.inflight d) else c.inflight d, ?_, by rw [hinf]⟩
  split
  · unfold consume; split
    · exact List.erase_sublist
    · exact List.Sublist.refl _
  · exact List.Sublist.refl _

theorem countP_sub {l l' new : List Msg} {p : Msg → Bool} (hs : List.Sublist l l')
    (hn : ∀ m, m ∈ new → p m = false) : (l ++ new).countP p ≤ l'.countP p := by
  rw [List.countP_append]
  have : new.countP p = 0 := List.countP_eq_zero.2 fun m hm => by rw [hn m hm]; simp
  rw [this]; exact Nat.le_trans (Nat.le_of_eq (Nat.add_zero _)) hs.countP_le

theorem isPP_preAccept {y : Msg} (x : PreAcceptM) (hy : isPP y = false) :
    (y == Msg.preAccept x) = false := by
  cases y <;> simp_all [isPP]

theorem isPP_prepareAt {y : Msg} (q i b : w32) (hy : isPP y = false) : isPrepareAt q i b y = false := by
  cases y <;> simp_all [isPP, isPrepareAt]

theorem isPP_okReplyAt {y : Msg} (q i b : w32) (Y : Fin 3) (hy : isPP y = false) :
    isOKReplyAt q i b Y y = false := by
  cases y <;> simp_all [isPP, isOKReplyAt]

/-! ## The frame -/

/-- **A step changing instance `(q0, i0)` at replica `a` only** keeps `CInv`, given the instance's
facts after the step (`hI0`, `E0`), the new copy's prepare bookkeeping (`hT`), its PreAccept clause
(`hP0`), the `crt` changes and the sent messages (`hO`). -/
theorem inv_frame {c c1 : Cfg gNet} {G G' : GG} {a : Fin 3} {e : Ev} {s' : RState} {o : List Out}
    {q0 i0 : w32} (I : CInv c G)
    (hst : c1.st = fun j => if j = a then s' else c.st j)
    (hinf : c1.inflight = fun j =>
      (if j = a then consume (gNet.recv e) (c.inflight j) else c.inflight j) ++ sentTo gNet j o)
    (hid : s'.id = (c.st a).id)
    (hcp : ∀ q i, ¬ (q = q0 ∧ i = i0) → s'.inst q i = (c.st a).inst q i)
    (hG : ∀ q i, ¬ (q = q0 ∧ i = i0) → G' q i = G q i)
    (hcrtA : s'.crt (rid32 a) = (c.st a).crt (rid32 a))
    (hcrtLe : ∀ r : Fin 3, sint.Z (s'.crt (rid32 r)) ≤ sint.Z ((c.st r).crt (rid32 r)))
    (hbelow : rowOk q0 = true ∧ 0 ≤ sint.Z i0 ∧ sint.Z i0 < sint.Z ((c.st (rowOf q0)).crt q0))
    (E0 : Evolve (rowOf q0) (G q0 i0) (balOf c q0 i0) (G' q0 i0) (balOf c1 q0 i0))
    (hcre0 : ∀ v, (G' q0 i0).cre v → (G q0 i0).cre v)
    (hI0 : InstOk c1 G' q0 i0)
    (hP0 : ∀ cp', s'.inst q0 i0 = some cp' → (∀ cp, (c.st a).inst q0 i0 = some cp → PAcc cp) →
      PAcc cp')
    (hT : ∀ cp' lb', s'.inst q0 i0 = some cp' → cp'.lb = some lb' → lb'.preparing = true →
      ¬ isCommitted cp'.status → Own (sint.Z cp'.ballot) a →
      ∃ cp lb, (c.st a).inst q0 i0 = some cp ∧ cp.lb = some lb ∧ lb.preparing = true ∧
        ¬ isCommitted cp.status ∧ cp.ballot = cp'.ballot ∧ lb.prepareOKs = lb'.prepareOKs)
    (hO : ∀ d m, Out.send d m ∈ o → isPP m = false ∧ MsgOk c1 G' d m ∧
      ∀ q j, msgInst m = some (q, j) → q = q0 ∧ j = i0)
    (hlen : s'.crtInstance.length = (c.st a).crtInstance.length)
    (hNN : ∀ cp, (c.st a).inst q0 i0 = some cp → cp.status ≠ St.NONE →
      ∃ cp', s'.inst q0 i0 = some cp' ∧ cp'.status ≠ St.NONE) :
    CInv c1 G' ∧ ∀ q i, Evolve (rowOf q) (G q i) (balOf c q i) (G' q i) (balOf c1 q i) := by
  have hstA : c1.st a = s' := by rw [hst]; exact if_pos rfl
  have hstN : ∀ j : Fin 3, j ≠ a → c1.st j = c.st j := fun j h => by rw [hst]; exact if_neg h
  have hcpO : ∀ (j : Fin 3) q i, ¬ (j = a ∧ q = q0 ∧ i = i0) → cpOf c1 j q i = cpOf c j q i := by
    intro j q i hn
    by_cases h : j = a
    · subst h; simp only [cpOf, hstA]; exact hcp q i (fun hh => hn ⟨rfl, hh⟩)
    · simp only [cpOf, hstN j h]
  have hcpA : ∀ q i, cpOf c1 a q i = s'.inst q i := fun q i => by simp only [cpOf, hstA]
  have hbal : ∀ q i, ¬ (q = q0 ∧ i = i0) → balOf c1 q i = balOf c q i := fun q i hn =>
    balOf_congr' (fun j => hcpO j q i (fun hh => hn hh.2))
  have E : ∀ q i, Evolve (rowOf q) (G q i) (balOf c q i) (G' q i) (balOf c1 q i) := by
    intro q i
    by_cases hn : q = q0 ∧ i = i0
    · obtain ⟨rfl, rfl⟩ := hn; exact E0
    · rw [hG q i hn, hbal q i hn]; exact Evolve.refl (I.inst q i).ainv
  have hcre : ∀ q i v, (G' q i).cre v → (G q i).cre v := by
    intro q i v h
    by_cases hn : q = q0 ∧ i = i0
    · obtain ⟨rfl, rfl⟩ := hn; exact hcre0 v h
    · rw [hG q i hn] at h; exact h
  have hown : ∀ r : Fin 3, (c1.st r).crt (rid32 r) = (c.st r).crt (rid32 r) := by
    intro r
    by_cases h : r = a
    · subst h; rw [hstA]; exact hcrtA
    · rw [hstN r h]
  have hownq : ∀ q, rowOk q = true → (c1.st (rowOf q)).crt q = (c.st (rowOf q)).crt q := by
    intro q hq; have := hown (rowOf q); rwa [rid32_rowOf hq] at this
  have hmem : ∀ d m, m ∈ c1.inflight d → m ∈ c.inflight d ∨ Out.send d m ∈ o := by
    intro d m hm
    obtain ⟨l, hs, hl⟩ := post_inflight hinf d
    rw [hl] at hm
    rcases List.mem_append.1 hm with h | h
    · exact Or.inl (hs.subset h)
    · exact Or.inr (mem_sentTo h)
  have hcnt : ∀ d (p : Msg → Bool), (∀ m, isPP m = false → p m = false) →
      (c1.inflight d).countP p ≤ (c.inflight d).countP p := by
    intro d p hp
    obtain ⟨l, hs, hl⟩ := post_inflight hinf d
    rw [hl]
    exact countP_sub hs (fun m hm => hp m (hO d m (mem_sentTo hm)).1)
  refine ⟨{ ids := ?_, inst := ?_, msgs := ?_, crtOwn := ?_, copyBelow := ?_, msgBelow := ?_,
            crtLen := ?_, leaderHas := ?_, prepMult := ?_ }, E⟩
  · intro j; by_cases h : j = a
    · subst h; rw [hstA, hid]; exact I.ids _
    · rw [hstN j h]; exact I.ids j
  · intro q i
    by_cases hn : q = q0 ∧ i = i0
    · obtain ⟨rfl, rfl⟩ := hn; exact hI0
    · exact instOk_G (hG q i hn) (instOk_congr' (fun j => hcpO j q i (fun hh => hn hh.2)) (I.inst q i))
  · intro d m hm
    rcases hmem d m hm with h | h
    · refine msgOk_evolve E hcre (fun q j cp' h1 h2 => ?_) (fun x hx h3 => ?_) (I.msgs d m h)
      · by_cases hd : d = a ∧ q = q0 ∧ j = i0
        · obtain ⟨rfl, rfl, rfl⟩ := hd; rw [hcpA] at h1; exact hP0 cp' h1 h2
        · rw [hcpO _ _ _ hd] at h1; exact h2 cp' h1
      · subst hx
        have h1 := hcnt d (fun y => y == (Msg.preAccept x : gNet.M)) (fun y hy => isPP_preAccept x hy)
        have h2 : 0 < (c1.inflight d).count (Msg.preAccept x : gNet.M) := List.count_pos_iff.2 hm
        have e1 : (c1.inflight d).count (Msg.preAccept x : gNet.M) =
            (c1.inflight d).countP (fun y => y == (Msg.preAccept x : gNet.M)) := rfl
        have e2 : (c.inflight d).count (Msg.preAccept x : gNet.M) =
            (c.inflight d).countP (fun y => y == (Msg.preAccept x : gNet.M)) := rfl
        omega
    · exact (hO d m h).2.1
  · intro j q
    rw [hown q]
    by_cases h : j = a
    · subst h; rw [hstA]; exact hcrtLe q
    · rw [hstN j h]; exact I.crtOwn j q
  · intro j q i cp hc
    by_cases hd : j = a ∧ q = q0 ∧ i = i0
    · obtain ⟨rfl, rfl, rfl⟩ := hd
      rw [hownq _ hbelow.1]; exact hbelow
    · rw [hcpO _ _ _ hd] at hc
      obtain ⟨k1, k2, k3⟩ := I.copyBelow j q i cp hc
      rw [hownq _ k1]; exact ⟨k1, k2, k3⟩
  · intro d m q j hm hj
    rcases hmem d m hm with h | h
    · obtain ⟨k1, k2, k3⟩ := I.msgBelow d m q j h hj
      rw [hownq _ k1]; exact ⟨k1, k2, k3⟩
    · obtain ⟨rfl, rfl⟩ := (hO d m h).2.2 q j hj
      rw [hownq _ hbelow.1]; exact hbelow
  · intro j; by_cases h : j = a
    · subst h; rw [hstA, hlen]; exact I.crtLen _
    · rw [hstN j h]; exact I.crtLen j
  · intro q j h0 h1
    rw [hown q] at h1
    obtain ⟨cp, hc, hne⟩ := I.leaderHas q j h0 h1
    by_cases hd : q = a ∧ rid32 q = q0 ∧ j = i0
    · obtain ⟨rfl, e1, rfl⟩ := hd
      rw [hcpA, e1]; exact hNN cp (by rw [← e1]; exact hc) hne
    · rw [hcpO _ _ _ hd]; exact ⟨cp, hc, hne⟩
  · intro R q i cp lb hc h1 h2 h3 h4
    have hPm : ∀ m, isPP m = false → isPrepareAt q i cp.ballot m = false :=
      fun m hm => isPP_prepareAt q i cp.ballot hm
    have hRm : ∀ Y m, isPP m = false → isOKReplyAt q i cp.ballot Y m = false :=
      fun Y m hm => isPP_okReplyAt q i cp.ballot Y hm
    obtain ⟨cp0, lb0, hc0, hl0, hp0, hn0, hb0, hk0⟩ : ∃ cp0 lb0, cpOf c R q i = some cp0 ∧
        cp0.lb = some lb0 ∧ lb0.preparing = true ∧ ¬ isCommitted cp0.status ∧
        cp0.ballot = cp.ballot ∧ lb0.prepareOKs = lb.prepareOKs := by
      by_cases hd : R = a ∧ q = q0 ∧ i = i0
      · obtain ⟨rfl, rfl, rfl⟩ := hd; rw [hcpA] at hc; exact hT cp lb hc h1 h2 h3 h4
      · rw [hcpO _ _ _ hd] at hc; exact ⟨cp, lb, hc, h1, h2, h3, rfl, rfl⟩
    obtain ⟨k1, k2⟩ := I.prepMult R q i cp0 lb0 hc0 hl0 hp0 hn0 (by rw [hb0]; exact h4)
    rw [hb0] at k1 k2
    refine ⟨fun Y => Nat.le_trans (Nat.add_le_add (hcnt Y _ hPm) (hcnt R _ (hRm Y))) (k1 Y),
      fun ho => ?_⟩
    obtain ⟨k3, k4, k5⟩ := k2 (by rw [hk0]; exact ho)
    exact ⟨k3, Nat.le_zero.1 (k4 ▸ hcnt _ _ hPm), Nat.le_zero.1 (k5 ▸ hcnt R _ (hRm _))⟩

/-! ## Helpers for the step files -/

theorem cpOf_postA {c c1 : Cfg gNet} {a : Fin 3} {s' : RState}
    (hst : c1.st = fun j => if j = a then s' else c.st j) (q i : w32) :
    cpOf c1 a q i = s'.inst q i := by
  have : c1.st a = s' := by rw [hst]; exact if_pos rfl
  simp only [cpOf, this]

theorem cpOf_postN {c c1 : Cfg gNet} {a j : Fin 3} {s' : RState}
    (hst : c1.st = fun j => if j = a then s' else c.st j) (h : j ≠ a) (q i : w32) :
    cpOf c1 j q i = cpOf c j q i := by
  have : c1.st j = c.st j := by rw [hst]; exact if_neg h
  simp only [cpOf, this]

theorem balOf_some {c : Cfg gNet} {q i : w32} {a : Fin 3} {cp : Copy} (h : cpOf c a q i = some cp) :
    balOf c q i a = some (sint.Z cp.ballot) := by
  simp only [balOf, h, Option.map_some]

theorem balOf_some_inv {c : Cfg gNet} {q i : w32} {a : Fin 3} {B : Int}
    (h : balOf c q i a = some B) : ∃ cp, cpOf c a q i = some cp ∧ sint.Z cp.ballot = B := by
  simp only [balOf] at h
  cases e : cpOf c a q i with
  | none => rw [e] at h; cases h
  | some cp => rw [e] at h; cases h; exact ⟨cp, rfl, rfl⟩

theorem setInst_self (t : RState) (q i : w32) (cp : Copy) : (t.setInst q i cp).inst q i = some cp := by
  simp [setInst_inst]

theorem setInst_other (t : RState) {q i q' i' : w32} (cp : Copy) (h : ¬ (q' = q ∧ i' = i)) :
    (t.setInst q i cp).inst q' i' = t.inst q' i' := by
  rw [setInst_inst, if_neg h]

/-- `t` is `s`, or `s` with `crt[q]` raised to `j + 1` (when `j ≥ crt[q]`). -/
def CrtB (s t : RState) (q j : w32) : Prop :=
  t = s ∨ (sge j (s.crt q) = true ∧ t = s.setCrt q (j + 1))

theorem crtB_core {s t : RState} {q0 i0 : w32} (h : CrtB s t q0 i0) (O : Fin 3 → w32)
    (hO : ∀ r, sint.Z (s.crt (rid32 r)) ≤ sint.Z (O r))
    (hbelow : rowOk q0 = true ∧ 0 ≤ sint.Z i0 ∧ sint.Z i0 < sint.Z (O (rowOf q0)))
    (a : Fin 3) (hOa : O a = s.crt (rid32 a)) :
    t.id = s.id ∧ t.inst = s.inst ∧ t.crt (rid32 a) = s.crt (rid32 a) ∧
      (∀ r : Fin 3, sint.Z (t.crt (rid32 r)) ≤ sint.Z (O r)) ∧
      t.crtInstance.length = s.crtInstance.length := by
  rcases h with rfl | ⟨hge, rfl⟩
  · exact ⟨rfl, rfl, rfl, hO, rfl⟩
  refine ⟨rfl, rfl, ?_, fun r => ?_, List.length_set ..⟩
  · refine (crt_setCrt' _ _ _ _).2 (fun e => ?_)
    have : rowOf q0 = a := rid32_inj' ((rid32_rowOf hbelow.1).trans e)
    rw [this, hOa, ← e] at hbelow
    simp only [sge, sle, decide_eq_true_eq] at hge
    omega
  · by_cases e : q0 = rid32 r
    · have hr : rowOf q0 = r := rid32_inj' ((rid32_rowOf hbelow.1).trans e)
      rcases (crt_setCrt' s q0 (i0 + 1) (rid32 r)).1 with h1 | h1
      · rw [h1]
        rw [hr] at hbelow
        have hlt : sint.Z (O r) < 2 ^ 31 := by
          simp only [sint.Z]; have := BitVec.toInt_lt (x := O r); omega
        rw [Z_succ32' (by omega)]; omega
      · rw [h1]; exact hO r
    · rw [(crt_setCrt' _ _ _ _).2 e]; exact hO r

theorem crtB_facts {c : Cfg gNet} {G : GG} (I : CInv c G) {a : Fin 3} {t : RState} {q0 i0 : w32}
    (h : CrtB (c.st a) t q0 i0)
    (hbelow : rowOk q0 = true ∧ 0 ≤ sint.Z i0 ∧ sint.Z i0 < sint.Z ((c.st (rowOf q0)).crt q0)) :
    t.id = (c.st a).id ∧ t.inst = (c.st a).inst ∧ t.crt (rid32 a) = (c.st a).crt (rid32 a) ∧
      (∀ r : Fin 3, sint.Z (t.crt (rid32 r)) ≤ sint.Z ((c.st r).crt (rid32 r))) ∧
      t.crtInstance.length = (c.st a).crtInstance.length := by
  have hb : rowOk q0 = true ∧ 0 ≤ sint.Z i0 ∧
      sint.Z i0 < sint.Z ((fun r : Fin 3 => (c.st r).crt (rid32 r)) (rowOf q0)) := by
    simp only [rid32_rowOf hbelow.1]; exact hbelow
  exact crtB_core h (fun r : Fin 3 => (c.st r).crt (rid32 r)) (fun r => I.crtOwn a r) hb a rfl

/-- A step leaving every copy alone (`G` unchanged). -/
theorem inv_frame_same {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {e : Ev} {s' : RState}
    {o : List Out} {q0 i0 : w32} (I : CInv c G)
    (hst : c1.st = fun j => if j = a then s' else c.st j)
    (hinf : c1.inflight = fun j =>
      (if j = a then consume (gNet.recv e) (c.inflight j) else c.inflight j) ++ sentTo gNet j o)
    (hid : s'.id = (c.st a).id) (hinst : s'.inst = (c.st a).inst)
    (hcrtA : s'.crt (rid32 a) = (c.st a).crt (rid32 a))
    (hcrtLe : ∀ r : Fin 3, sint.Z (s'.crt (rid32 r)) ≤ sint.Z ((c.st r).crt (rid32 r)))
    (hbelow : rowOk q0 = true ∧ 0 ≤ sint.Z i0 ∧ sint.Z i0 < sint.Z ((c.st (rowOf q0)).crt q0))
    (hO : ∀ d m, Out.send d m ∈ o → isPP m = false ∧ MsgOk c1 G d m ∧
      ∀ q j, msgInst m = some (q, j) → q = q0 ∧ j = i0)
    (hlen : s'.crtInstance.length = (c.st a).crtInstance.length) :
    CInv c1 G ∧ ∀ q i, Evolve (rowOf q) (G q i) (balOf c q i) (G q i) (balOf c1 q i) := by
  have hcpS : ∀ j q i, cpOf c1 j q i = cpOf c j q i := fun j q i => by
    by_cases h : j = a
    · subst h; rw [cpOf_postA hst, hinst]; rfl
    · exact cpOf_postN hst h q i
  have hbal := balOf_congr' (fun j => hcpS j q0 i0)
  refine inv_frame I hst hinf hid (fun q i _ => by rw [hinst]) (fun _ _ _ => rfl) hcrtA hcrtLe
    hbelow ?_ (fun _ h => h) (instOk_congr' (fun j => hcpS j q0 i0) (I.inst q0 i0)) ?_ ?_ hO hlen
    (fun cp h1 h2 => ⟨cp, by rw [hinst]; exact h1, h2⟩)
  · rw [hbal]; exact Evolve.refl (I.inst q0 i0).ainv
  · intro cp' h1 h2; rw [hinst] at h1; exact h2 cp' h1
  · intro cp' lb' h1 h2 h3 h4 h5; rw [hinst] at h1; exact ⟨cp', lb', h1, h2, h3, h4, rfl, rfl⟩

/-- The votes of a copy that is not committed are at most its ballot. -/
theorem votes_le {c : Cfg gNet} {G : GG} {q i : w32} {a : Fin 3} {cp : Copy}
    (h : CopyOk c G q i a cp) (hn : ¬ isCommitted cp.status) :
    ∀ b u, (G q i).acc a b u → b ≤ sint.Z cp.ballot := by
  intro b u hu
  rcases h.stOk with hs | hs | hs | hs
  · exact absurd hu (h.noVotes (Or.inl hs) b u)
  · exact absurd hu (h.noVotes (Or.inr hs) b u)
  · exact Int.le_trans ((h.accVote hs).2 b u hu) h.vbalLe
  · exact absurd hs hn

theorem acc_ne : St.ACCEPTED ≠ St.NONE ∧ St.ACCEPTED ≠ St.PREACCEPTED ∧
    St.ACCEPTED ≠ St.PREACCEPTED_EQ ∧ St.ACCEPTED ≠ St.COMMITTED ∧ St.ACCEPTED ≠ St.EXECUTED := by
  decide

theorem acc_notPre {x : w8} (h : x = St.ACCEPTED) : ¬ (x = St.NONE ∨ isPre x) := by
  subst h; rintro (h | h | h)
  · exact acc_ne.1 h
  · exact acc_ne.2.1 h
  · exact acc_ne.2.2.1 h

theorem acc_notCommitted {x : w8} (h : x = St.ACCEPTED) : ¬ isCommitted x := by
  subst h; rintro (h | h)
  · exact acc_ne.2.2.2.1 h
  · exact acc_ne.2.2.2.2 h

theorem com_ne : St.COMMITTED ≠ St.NONE ∧ St.COMMITTED ≠ St.PREACCEPTED ∧
    St.COMMITTED ≠ St.PREACCEPTED_EQ ∧ St.COMMITTED ≠ St.ACCEPTED := by
  decide

theorem com_notPre {x : w8} (h : x = St.COMMITTED) : ¬ (x = St.NONE ∨ isPre x) := by
  subst h; rintro (h | h | h)
  · exact com_ne.1 h
  · exact com_ne.2.1 h
  · exact com_ne.2.2.1 h

theorem false_ne_true : FALSE ≠ TRUE := by decide

end Perennial.gryff.pureA.A1d
