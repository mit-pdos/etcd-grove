/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/StepPrepare.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A1b, internal: preservation of the agreement invariant by `stepPrepare` (`handlePrepare`).
-/
module

public import Dsverify.Proof.gryff.PureA.Exec

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.A1b

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn Perennial.gryff.pureA

/-- The paths of `stepPrepare`. -/
theorem stepPrepare_cases {s s' : RState} {m : PrepareM} {o : List Out}
    (h : stepPrepare s m = .ok (s', o)) :
    inBox m.replica m.inst = true ∧ ∃ cp' r x, s' = s.setInst m.replica m.inst cp' ∧
      sendPeer s m.leaderId (.prepareReply r) = some x ∧ o = [x] ∧
      r.acceptorId = s.id ∧ r.replica = m.replica ∧ r.inst = m.inst ∧
      ((s.inst m.replica m.inst = none ∧
        cp' = { cmds := [], ballot := m.ballot, status := St.NONE, seq := 0, deps := nildeps,
                base := vt0, lb := none, slot := m.inst, leader := m.replica, vbal := -1 } ∧
        r.ok = TRUE ∧ r.ballot = m.ballot ∧ r.status = St.NONE ∧ r.vbal = -1) ∨
       (∃ c, s.inst m.replica m.inst = some c ∧ slt m.ballot c.ballot = true ∧ cp' = c ∧
        r.ok = FALSE ∧ r.status = c.status ∧ r.cmds = c.cmds ∧ r.seq = c.seq ∧ r.deps = c.deps ∧
        r.base = c.base) ∨
       (∃ c, s.inst m.replica m.inst = some c ∧ slt m.ballot c.ballot = false ∧
        cp' = { c with ballot := m.ballot } ∧ r.ok = TRUE ∧ r.ballot = m.ballot ∧
        r.status = c.status ∧ r.vbal = c.vbal ∧ r.cmds = c.cmds ∧ r.seq = c.seq ∧
        r.deps = c.deps ∧ r.base = c.base)) := by
  unfold stepPrepare at h
  peel h
  · rename_i hb _ hn _ _ hs
    cases h
    exact ⟨by simpa using hb, _, _, _, rfl, hs, rfl, rfl, rfl, rfl, Or.inl ⟨hn, rfl, rfl, rfl, rfl, rfl⟩⟩
  · rename_i hb _ c hn _ _ hs hl
    cases h
    simp only [hl, ite_true] at hs ⊢
    exact ⟨by simpa using hb, _, _, _, rfl, hs, rfl, rfl, rfl, rfl,
      Or.inr (Or.inl ⟨c, hn, hl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)⟩
  · rename_i hb _ c hn _ _ hs hl
    cases h
    simp only [hl, Bool.false_eq_true, ite_false] at hs ⊢
    exact ⟨by simpa using hb, _, _, _, rfl, hs, rfl, rfl, rfl, rfl,
      Or.inr (Or.inr ⟨c, hn, by simpa using hl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)⟩

/-! ## Small facts -/

theorem rid32_inj {a b : Fin 3} (h : rid32 a = rid32 b) : a = b := by
  revert a b; decide

theorem dstOf_rid32 (R : Fin 3) : dstOf (rid32 R) = some R := by
  revert R; decide

theorem rid32_rowOf {q : w32} (h : rowOk q = true) : rid32 (rowOf q) = q := by
  unfold rowOk at h
  have h' := of_decide_eq_true h
  unfold rowOf rid32
  rw [dite_eq_left_of_eq_true (eq_true h')]
  simp only [sint.Z] at h'
  apply BitVec.eq_of_toNat_eq
  have e := BitVec.toInt_eq_toNat_cond q
  split at e
  · simp only [sint.Z, BitVec.toNat_ofNat, e]; omega
  · omega

theorem rid32_eq_iff {q : w32} (h : rowOk q = true) (a : Fin 3) : rid32 a = q ↔ a = rowOf q := by
  constructor
  · intro e; rw [← rid32_rowOf h] at e; exact rid32_inj e
  · intro e; subst e; exact rid32_rowOf h

theorem own_uniq {b : Int} {R R' : Fin 3} (h : Own b R) (h' : Own b R') : R = R' := by
  obtain ⟨k, hk, rfl⟩ := h
  obtain ⟨k', hk', e⟩ := h'
  have := R.isLt; have := R'.isLt
  exact Fin.ext (by omega)

theorem own_pos {b : Int} {R : Fin 3} (h : Own b R) : 0 < b := by
  obtain ⟨k, hk, rfl⟩ := h; omega

theorem sendPeer_rid {s : RState} {a R : Fin 3} {msg : Msg} {x : Out} (hid : s.id = rid32 a)
    (h : sendPeer s (rid32 R) msg = some x) : x = .send R msg ∧ R ≠ a := by
  unfold sendPeer at h
  split at h
  · cases h
  · rename_i hne
    unfold sendTo at h; rw [dstOf_rid32] at h; cases h
    exact ⟨rfl, fun e => hne (by rw [hid, e])⟩

/-- `sentTo gNet` over `Fin 3`. -/
def sentR (j : Fin 3) (o : List Out) : List Msg :=
  o.filterMap (fun x => match x with | .send d m => if d = j then some m else none | .ext _ => none)

theorem sentTo_nil' {N : kahn.Net} (j : Fin N.n) : kahn.sentTo N j [] = [] := rfl
theorem sentTo_cons' {N : kahn.Net} (j : Fin N.n) (x : kahn.Out N.n N.M N.X)
    (o : List (kahn.Out N.n N.M N.X)) :
    kahn.sentTo N j (x :: o) = (match x with | .send d m => if d = j then [m] else [] | .ext _ => [])
      ++ kahn.sentTo N j o := by
  cases x with
  | send d m => simp only [kahn.sentTo, List.filterMap_cons]; split <;> simp_all
  | ext x => simp [kahn.sentTo]
theorem sentR_cons (j : Fin 3) (x : Out) (o : List Out) :
    sentR j (x :: o) = (match x with | .send d m => if d = j then [m] else [] | .ext _ => [])
      ++ sentR j o := by
  cases x with
  | send d m => simp only [sentR, List.filterMap_cons]; split <;> simp_all
  | ext x => simp [sentR]
theorem sentTo_eq (j : Fin 3) (o : List Out) : kahn.sentTo (N := gNet) j o = sentR j o := by
  induction o with
  | nil => exact sentTo_nil' (N := gNet) j
  | cons x o ih =>
    refine (sentTo_cons' (N := gNet) j x o).trans ?_
    rw [sentR_cons]
    cases x with
    | send d m => exact congrArg (_ ++ ·) ih
    | ext => exact congrArg (_ ++ ·) ih

theorem sentR_single (R j : Fin 3) (msg : Msg) :
    sentR j [.send R msg] = if R = j then [msg] else [] := by
  by_cases h : R = j <;> simp [sentR, h]

theorem setInst_inst' (s : RState) (q i : w32) (c : Copy) (q' i' : w32) :
    (s.setInst q i c).inst q' i' = if q' = q ∧ i' = i then some c else s.inst q' i' := rfl

/-! ## The history at one instance -/

/-- `G` with `g` at `(q, i)`. -/
def GG.set (G : GG) (q i : w32) (g : Gh Val) : GG :=
  fun q' i' => if q' = q ∧ i' = i then g else G q' i'

/-- `g'` extends `g` by votes of `R` and proposals/restarts at ballots `R` owns, up to `B`. -/
structure ExtA (g g' : Gh Val) (R : Fin 3) (B : Int) : Prop where
  le : g.Le g'
  acc : ∀ a b' u, g'.acc a b' u → g.acc a b' u ∨ a = R
  prop : ∀ b' u, g'.prop b' u → g.prop b' u ∨ (Own b' R ∧ b' ≤ B)
  rst : ∀ b', g'.rst b' → g.rst b' ∨ (Own b' R ∧ b' ≤ B)
  cre : ∀ v, g'.cre v → g.cre v
  eq : ∀ a, g'.eq a → g.eq a
  fast : ∀ v, g'.fast v → g.fast v

theorem ExtA.refl (g : Gh Val) (R : Fin 3) (B : Int) : ExtA g g R B :=
  ⟨Gh.Le.refl g, fun _ _ _ h => Or.inl h, fun _ _ h => Or.inl h, fun _ h => Or.inl h,
   fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem ExtA.addProp (g : Gh Val) {R : Fin 3} {b : Int} (v : Val) (hb : Own b R) :
    ExtA g (g.addProp b v R) R b :=
  ⟨g.le_addProp b v R, fun _ _ _ h => h.imp_right fun ⟨h1, _, _⟩ => h1,
   fun _ _ h => h.imp_right fun ⟨h1, _⟩ => by subst h1; exact ⟨hb, Int.le_refl _⟩,
   fun _ h => Or.inl h,
   fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem ExtA.addRst (g : Gh Val) {R : Fin 3} {b : Int} (hb : Own b R) :
    ExtA g (g.addRst b) R b :=
  ⟨g.le_addRst b, fun _ _ _ h => Or.inl h, fun _ _ h => Or.inl h,
   fun _ h => h.imp_right fun h1 => by subst h1; exact ⟨hb, Int.le_refl _⟩,
   fun _ h => h, fun _ h => h, fun _ h => h⟩

/-- Only ballots grow (same history). -/
theorem evolve_bal {L : Fin 3} {g : Gh Val} {bal bal' : Fin 3 → Option Int} (I : AInv g bal L)
    (hm : ∀ a B, bal a = some B → ∃ B', bal' a = some B' ∧ B ≤ B') : Evolve L g bal g bal' where
  le := Gh.Le.refl g
  bal_mono := hm
  acc_new _ _ _ h hn := absurd h hn
  eq_new _ h hn := absurd h hn
  fast_new _ h hn := absurd h hn
  fast_cre := I.fast_cre
  fast_eq := I.fast_eq
  fast_noprop := I.fast_noprop

theorem ainv_evolve_same {L : Fin 3} {g : Gh Val} {bal bal' : Fin 3 → Option Int} (I : AInv g bal L)
    (E : Evolve L g bal g bal') : AInv g bal' L :=
  { I with prop_safe := fun b v h => safeAt_evolve E (I.prop_safe b v h)
           rst_safe := fun b h => safeAll_evolve E (I.rst_safe b h) }

/-- A copy of a replica other than `R` under an extension by `R`. -/
theorem copyOk_ext {c c1 : Cfg gNet} {G G' : GG} {q i : w32} {a R : Fin 3} {B : Int} {cp : Copy}
    (X : ExtA (G q i) (G' q i) R B) (haR : a ≠ R)
    (E : Evolve (rowOf q) (G q i) (balOf c q i) (G' q i) (balOf c1 q i))
    (h : CopyOk c G q i a cp) : CopyOk c1 G' q i a cp := by
  have hacc : ∀ b' u, (G' q i).acc a b' u → (G q i).acc a b' u := fun b' u hu =>
    (X.acc a b' u hu).resolve_right haR
  have hown : ∀ b', Own b' a → ¬ Own b' R := fun b' h1 h2 => haR (own_uniq h1 h2)
  refine ⟨h.nonneg, h.ballotForm, h.vbalLe, h.stOk, fun hs b' u hu => h.noVotes hs b' u (hacc _ _ hu),
    fun hs => ?_, fun hs => chosen_mono X.le (h.committed hs),
    fun hs hv => (h.rstVbal hs hv).imp_right (X.le.rst _), fun h1 h2 h3 => X.le.cre _ (h.eqCre h1 h2 h3),
    fun h1 h2 h3 => ?_, fun hs ho u hu => ?_, fun lb hl hp hc ho => ?_, fun h1 h2 => ?_⟩
  · obtain ⟨k1, k2⟩ := h.accVote hs
    exact ⟨X.le.acc _ _ _ k1, fun b' u hu => k2 b' u (hacc _ _ hu)⟩
  · obtain ⟨k1, k2, k3, k4⟩ := h.leader0 h1 h2 h3
    refine ⟨X.le.cre _ k1, fun u hu => ?_, fun v hv => k3 v (X.fast v hv), k4⟩
    rcases X.prop _ _ hu with hu | ⟨hu, _⟩
    · exact k2 u hu
    · have := own_pos hu; omega
  · rcases X.prop _ _ hu with hu | ⟨hu, _⟩
    · exact h.ownFresh hs ho u hu
    · exact hown _ ho hu
  · obtain ⟨k1, k2, k3, k4, k5⟩ := h.preparing lb hl hp hc ho
    refine ⟨riOk_evolve E (own_pos ho) k1, fun hr => ?_, fun u hu => ?_, k4, k5⟩
    · rcases X.rst _ hr with hr | ⟨hr, _⟩
      · exact k2 hr
      · exact hown _ ho hr
    · rcases X.prop _ _ hu with hu | ⟨hu, _⟩
      · exact k3 u hu
      · exact hown _ ho hu
  · rcases h.eqTrack h1 (X.eq a h2) with k | k | k | k
    · exact Or.inl k
    · exact Or.inr (Or.inl k)
    · exact Or.inr (Or.inr (Or.inl k))
    · exact Or.inr (Or.inr (Or.inr (rstBelow_mono X.le k)))

/-- A copy under a change of ballots only. -/
theorem copyOk_bal {c c1 : Cfg gNet} {G : GG} {q i : w32} {a : Fin 3} {cp : Copy}
    (E : Evolve (rowOf q) (G q i) (balOf c q i) (G q i) (balOf c1 q i))
    (h : CopyOk c G q i a cp) : CopyOk c1 G q i a cp := by
  refine { h with preparing := fun lb hl hp hc ho => ?_ }
  obtain ⟨k1, k2⟩ := h.preparing lb hl hp hc ho
  exact ⟨riOk_evolve E (own_pos ho) k1, k2⟩

/-- Messages under an evolution of every instance. -/
theorem msgOk_evolve {c c1 : Cfg gNet} {G G' : GG} {d : Fin 3} {msg : Msg}
    (E : ∀ q j, Evolve (rowOf q) (G q j) (balOf c q j) (G' q j) (balOf c1 q j))
    (hcre : ∀ q j v, (G' q j).cre v → (G q j).cre v)
    (hpa : ∀ x, msg = .preAccept x → x.ballot = 0 →
      (∀ cp, cpOf c d x.replica x.inst = some cp →
        0 < sint.Z cp.ballot ∨ cp.status = St.ACCEPTED ∨ isCommitted cp.status) →
      (c.inflight d).count (Msg.preAccept x : gNet.M) = 1 →
      (∀ cp, cpOf c1 d x.replica x.inst = some cp →
        0 < sint.Z cp.ballot ∨ cp.status = St.ACCEPTED ∨ isCommitted cp.status) ∧
      (c1.inflight d).count (Msg.preAccept x : gNet.M) = 1)
    (h : MsgOk c G d msg) : MsgOk c1 G' d msg := by
  cases msg with
  | preAccept x =>
    have L := (E x.replica x.inst).le
    refine ⟨fun hb => ?_, fun hb => ?_⟩
    · obtain ⟨k1, k2, k3, k4, k5⟩ := h.1 hb
      obtain ⟨j1, j2⟩ := hpa x rfl hb k4 k5
      exact ⟨k1, k2, L.cre _ k3, j1, j2⟩
    · obtain ⟨k1, k2, k3⟩ := h.2 hb
      exact ⟨k1, L.rst _ k2, k3⟩
  | preAcceptReply x =>
    have L := (E x.replica x.inst).le
    refine ⟨fun hb => ?_, fun hb ho => ⟨(h.2 hb ho).1, L.rst _ (h.2 hb ho).2⟩⟩
    obtain ⟨k1, k2, k3⟩ := h.1 hb
    refine ⟨k1, fun hok hc => ?_, fun hok => ?_⟩
    · obtain ⟨v, hv, hv'⟩ := hc
      obtain ⟨X, hX, hX'⟩ := k2 hok ⟨v, hcre _ _ _ hv, hv'⟩
      exact ⟨X, hX, L.eq _ hX'⟩
    · obtain ⟨v, hv, hv'⟩ := k3 hok
      exact ⟨v, L.cre _ hv, hv'⟩
  | preAcceptOK x =>
    obtain ⟨X, hX, hX'⟩ := h
    exact ⟨X, hX, (E _ _).le.eq _ hX'⟩
  | accept x =>
    obtain ⟨h1, R, h2, h3, h4, h5⟩ := h
    exact ⟨(E _ _).le.prop _ _ h1, R, h2, h3, h4, (E _ _).le.acc _ _ _ h5⟩
  | acceptReply x =>
    refine ⟨fun hok => ?_, h.2⟩
    obtain ⟨Y, hY, v, hv, hv'⟩ := h.1 hok
    exact ⟨Y, hY, v, (E _ _).le.acc _ _ _ hv, (E _ _).le.acc _ _ _ hv'⟩
  | commit x => exact chosen_mono (E _ _).le h
  | prepare x =>
    obtain ⟨k1, R, k2, k3, k4, B, hB, hle⟩ := h
    obtain ⟨B', hB', hle'⟩ := (E _ _).bal_mono R B hB
    exact ⟨k1, R, k2, k3, k4, B', hB', by omega⟩
  | prepareReply x =>
    have Ex := E x.replica x.inst
    refine ⟨fun hc => chosen_mono Ex.le (h.1 hc), fun hok => ?_, h.2.2⟩
    obtain ⟨⟨B, hB, hle⟩, Y, k1, k2, k3, k4⟩ := h.2.1 hok
    obtain ⟨B', hB', hle'⟩ := Ex.bal_mono d B hB
    exact ⟨⟨B', hB', by omega⟩, Y, k1, k2, k3, fun hnc hnp =>
      repOk_evolve Ex (own_pos k3) (k4 hnc fun u hu => hnp u (Ex.le.prop _ _ hu))⟩
  | _ => trivial

/-! ## Transport (as `Inv.lean`'s, which this module cannot import) -/

theorem balOf_congr {c c1 : Cfg gNet} {q i : w32} (h : ∀ a, cpOf c1 a q i = cpOf c a q i) :
    balOf c1 q i = balOf c q i := by
  funext a; simp only [balOf, h]

theorem instOk_congr {c c1 : Cfg gNet} {G : GG} {q i : w32} (h : ∀ a, cpOf c1 a q i = cpOf c a q i)
    (I : InstOk c G q i) : InstOk c1 G q i := by
  have hb := balOf_congr h
  exact
    { ainv := hb ▸ I.ainv
      copies := fun a cp hc => { I.copies a cp ((h a).symm.trans hc) with
        preparing := by rw [hb]; exact (I.copies a cp ((h a).symm.trans hc)).preparing }
      noCopy := fun a hc => I.noCopy a ((h a).symm.trans hc)
      fastL := fun v hv => by rw [h]; exact I.fastL v hv
      leaderCopy := fun ⟨a, cp, hc⟩ => by
        rw [h]; exact I.leaderCopy ⟨a, cp, (h a).symm.trans hc⟩
      ownMono := fun b R hR hp => by rw [hb]; exact I.ownMono b R hR hp
      fresh := fun hn => I.fresh (fun a => (h a).symm.trans (hn a)) }

/-! ## A step's configuration -/

/-- In-flight messages at `Msg`. -/
def infR (c : Cfg gNet) (j : Fin 3) : List Msg := c.inflight j

theorem inflight_self {c c1 : Cfg gNet} {a : Fin 3} {e : Ev} {z : Msg} {o : List Out}
    (hinf : c1.inflight = fun j =>
      (if j = a then consume (gNet.recv e) (c.inflight j) else c.inflight j) ++
        sentTo gNet j o) (hz : gNet.recv e = some z) :
    infR c1 a = (infR c a).erase z ++ sentR a o := by
  unfold infR; rw [hinf, ← sentTo_eq]
  simp only [ite_true]; rw [hz]; rfl

theorem inflight_other {c c1 : Cfg gNet} {a : Fin 3} {e : Ev} {o : List Out}
    (hinf : c1.inflight = fun j =>
      (if j = a then consume (gNet.recv e) (c.inflight j) else c.inflight j) ++
        sentTo gNet j o) {j : Fin 3} (h : j ≠ a) :
    infR c1 j = infR c j ++ sentR j o := by
  unfold infR; rw [hinf, ← sentTo_eq]
  simp only [h, ite_false]; rfl

theorem mem_step {c c1 : Cfg gNet} {a : Fin 3} {e : Ev} {z : Msg} {o : List Out}
    (hinf : c1.inflight = fun j =>
      (if j = a then consume (gNet.recv e) (c.inflight j) else c.inflight j) ++
        sentTo gNet j o) (hze : gNet.recv e = some z) {j : Fin 3} {y : Msg} (h : y ∈ infR c1 j) :
    y ∈ infR c j ∨ y ∈ sentR j o := by
  by_cases hj : j = a
  · subst hj
    rw [inflight_self hinf hze] at h
    rcases List.mem_append.1 h with h | h
    · exact Or.inl (List.mem_of_mem_erase h)
    · exact Or.inr h
  · rw [inflight_other hinf hj] at h
    exact List.mem_append.1 h

theorem countP_erase_mem {l : List Msg} {z : Msg} (hz : z ∈ l) (p : Msg → Bool) :
    (l.erase z).countP p + (if p z then 1 else 0) = l.countP p := by
  rw [(List.perm_cons_erase hz).countP_eq p, List.countP_cons]

theorem countP_step {c c1 : Cfg gNet} {a : Fin 3} {e : Ev} {z : Msg} {o : List Out}
    (hinf : c1.inflight = fun j =>
      (if j = a then consume (gNet.recv e) (c.inflight j) else c.inflight j) ++
        sentTo gNet j o) (hze : gNet.recv e = some z) (hz : z ∈ infR c a) (j : Fin 3)
    (p : Msg → Bool) :
    (infR c1 j).countP p + (if j = a ∧ p z = true then 1 else 0) =
      (infR c j).countP p + (sentR j o).countP p := by
  by_cases h : j = a
  · subst h; rw [inflight_self hinf hze, List.countP_append]; simp only [true_and]
    have := countP_erase_mem hz p
    split <;> simp_all <;> omega
  · rw [inflight_other hinf h, List.countP_append]; simp only [h, false_and, ite_false]; omega

theorem st_step {c c1 : Cfg gNet} {a : Fin 3} {s' : RState}
    (hst : c1.st = fun j => if j = a then s' else c.st j) (j : Fin 3) :
    c1.st j = if j = a then s' else c.st j := by rw [hst]

/-! ## Statuses -/

theorem st_facts :
    St.NONE ≠ St.ACCEPTED ∧ St.NONE ≠ St.PREACCEPTED ∧ St.NONE ≠ St.PREACCEPTED_EQ ∧
    St.NONE ≠ St.COMMITTED ∧ St.NONE ≠ St.EXECUTED ∧
    St.ACCEPTED ≠ St.PREACCEPTED ∧ St.ACCEPTED ≠ St.PREACCEPTED_EQ ∧
    St.ACCEPTED ≠ St.COMMITTED ∧ St.ACCEPTED ≠ St.EXECUTED ∧
    St.PREACCEPTED ≠ St.PREACCEPTED_EQ ∧ St.PREACCEPTED ≠ St.COMMITTED ∧
    St.PREACCEPTED ≠ St.EXECUTED ∧ St.PREACCEPTED_EQ ≠ St.COMMITTED ∧
    St.PREACCEPTED_EQ ≠ St.EXECUTED ∧ St.COMMITTED ≠ St.EXECUTED ∧ (FALSE : w8) ≠ TRUE := by
  decide

theorem none_not : ¬ isPre St.NONE ∧ ¬ isCommitted St.NONE := by
  unfold isPre isCommitted; decide

theorem acc_not : ¬ isPre St.ACCEPTED ∧ ¬ isCommitted St.ACCEPTED := by
  unfold isPre isCommitted; decide

theorem rstBelow_le {g : Gh Val} {b b' : Int} (h : RstBelow g b) (hle : b ≤ b') : RstBelow g b' := by
  obtain ⟨x, h1, h2, h3⟩ := h; exact ⟨x, h1, by omega, h3⟩

theorem z_m1 : sint.Z (-1 : w32) = -1 := by decide
theorem z_zero {x : w32} (h : x = 0) : sint.Z x = 0 := by subst h; decide

/-! ## `handlePrepare` -/

/-- **`stepPrepare` keeps the invariant** (same history). -/
theorem prepare_inv {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {m : PrepareM} {s' : RState}
    {o : List Out} (I : CInv c G)
    (hst : c1.st = fun j => if j = a then s' else c.st j)
    (hinf : c1.inflight = fun j =>
      (if j = a then consume (gNet.recv (.msg (.prepare m))) (c.inflight j) else c.inflight j) ++
        sentTo gNet j o)
    (hm : Msg.prepare m ∈ c.inflight a) (h : stepPrepare (c.st a) m = .ok (s', o)) :
    ∃ G', CInv c1 G' ∧ ∀ q i, Evolve (rowOf q) (G q i) (balOf c q i) (G' q i) (balOf c1 q i) := by
  obtain ⟨-, cp', r, x, hs', hx, ho, hr1, hr2, hr3, hcase⟩ := stepPrepare_cases h
  obtain ⟨hb0, R, hown, hlid, hRa, B, hB, hbB⟩ := I.msgs a _ hm
  obtain ⟨hrow, hi0, hicrt⟩ := I.msgBelow a _ m.replica m.inst hm rfl
  rw [hlid] at hx
  obtain ⟨rfl, -⟩ := sendPeer_rid (I.ids a) hx
  have hze : gNet.recv (.msg (.prepare m)) = some (.prepare m) := rfl
  have hm' : Msg.prepare m ∈ infR c a := hm
  -- the states
  have hsta : c1.st a = (c.st a).setInst m.replica m.inst cp' := by
    rw [hst, hs']; exact if_pos rfl
  have hsto : ∀ j : Fin 3, j ≠ a → c1.st j = c.st j := by
    intro j hj; rw [hst]; exact if_neg hj
  have hcpa : ∀ q' i', cpOf c1 a q' i' =
      if q' = m.replica ∧ i' = m.inst then some cp' else cpOf c a q' i' := by
    intro q' i'; simp only [cpOf, hsta]; rfl
  have hcpo : ∀ j : Fin 3, j ≠ a → ∀ q' i', cpOf c1 j q' i' = cpOf c j q' i' := by
    intro j hj q' i'; simp only [cpOf, hsto j hj]
  have hid : ∀ j : Fin 3, (c1.st j).id = rid32 j := by
    intro j; by_cases hj : j = a
    · subst hj; rw [hsta]; exact I.ids _
    · rw [hsto j hj]; exact I.ids j
  have hcrt : ∀ (j : Fin 3) q', (c1.st j).crt q' = (c.st j).crt q' := by
    intro j q'; by_cases hj : j = a
    · subst hj; rw [hsta]; rfl
    · rw [hsto j hj]
  -- the copy's ballot grows
  have hbmono : ∀ B0, balOf c m.replica m.inst a = some B0 → B0 ≤ sint.Z cp'.ballot := by
    intro B0 h0
    simp only [balOf, cpOf] at h0
    rcases hcase with ⟨hn, -⟩ | ⟨c0, hc0, -, rfl, -⟩ | ⟨c0, hc0, hl, rfl, -⟩
    · rw [hn] at h0; cases h0
    · rw [hc0] at h0; cases h0; exact Int.le_refl _
    · rw [hc0] at h0; cases h0
      have : ¬ sint.Z m.ballot < sint.Z c0.ballot := fun h' => by
        rw [(slt_iff _ _).2 h'] at hl; cases hl
      simp only; omega
  have hcpb : sint.Z m.ballot ≤ sint.Z cp'.ballot := by
    rcases hcase with ⟨-, rfl, -⟩ | ⟨c0, -, hl, he, -⟩ | ⟨c0, -, -, rfl, -⟩
    · exact Int.le_refl _
    · subst he; have := (slt_iff m.ballot cp'.ballot).1 hl; omega
    · exact Int.le_refl _
  have hmono : ∀ q' i' j B0, balOf c q' i' j = some B0 →
      ∃ B', balOf c1 q' i' j = some B' ∧ B0 ≤ B' := by
    intro q' i' j B0 h0
    by_cases hj : j = a
    · subst hj
      by_cases hq : q' = m.replica ∧ i' = m.inst
      · obtain ⟨rfl, rfl⟩ := hq
        exact ⟨_, by simp only [balOf, hcpa, and_self, ite_true, Option.map_some], hbmono B0 h0⟩
      · exact ⟨B0, by simp only [balOf, hcpa, hq, ite_false]; exact h0, Int.le_refl _⟩
    · exact ⟨B0, by simp only [balOf, hcpo j hj]; exact h0, Int.le_refl _⟩
  have E : ∀ q' i', Evolve (rowOf q') (G q' i') (balOf c q' i') (G q' i') (balOf c1 q' i') :=
    fun q' i' => evolve_bal (I.inst q' i').ainv (hmono q' i')
  have hnotown : ¬ Own (sint.Z m.ballot) a := fun h1 => hRa (own_uniq hown h1)
  have hcpos : 0 < sint.Z cp'.ballot := by omega
  -- the new copy
  have hnew : CopyOk c1 G m.replica m.inst a cp' := by
    rcases hcase with ⟨hn, rfl, -⟩ | ⟨c0, hc0, -, rfl, -⟩ | ⟨c0, hc0, hl, rfl, -⟩
    · obtain ⟨hnv, hne⟩ := (I.inst m.replica m.inst).noCopy a hn
      refine ⟨(by simp only; omega), Or.inr ⟨R, hown⟩, (by simp only [z_m1]; omega), Or.inl rfl,
        fun _ => hnv, fun hs => absurd hs st_facts.1, fun hs => absurd hs none_not.2,
        fun hs => absurd hs none_not.1, fun hs => absurd hs st_facts.2.2.1, fun _ hb => ?_,
        fun _ ho => absurd ho hnotown, fun lb hl => (nomatch hl), fun _ he => absurd he hne⟩
      have := z_zero hb; simp only at this; omega
    · exact copyOk_bal (E _ _) ((I.inst _ _).copies a _ hc0)
    · have k := (I.inst _ _).copies a _ hc0
      have : ¬ sint.Z m.ballot < sint.Z c0.ballot := fun h' => by
        rw [(slt_iff _ _).2 h'] at hl; cases hl
      have hv := k.vbalLe
      refine ⟨(by simp only; omega), Or.inr ⟨R, hown⟩, (by simp only; omega),
        k.stOk, k.noVotes, k.accVote, k.committed, k.rstVbal, k.eqCre, fun _ hb => ?_,
        fun _ ho => absurd ho hnotown, fun _ _ _ _ ho => absurd ho hnotown, fun h1 h2 => ?_⟩
      · have := z_zero hb; simp only at this; omega
      · rcases k.eqTrack h1 h2 with k' | k' | k' | k'
        · exact Or.inl k'
        · exact Or.inr (Or.inl k')
        · exact Or.inr (Or.inr (Or.inl k'))
        · exact Or.inr (Or.inr (Or.inr (rstBelow_le k' (by simp only; omega))))
  -- the leader's copy
  obtain ⟨cpR, hcR⟩ : ∃ cpR, cpOf c R m.replica m.inst = some cpR := by
    simp only [balOf] at hB
    cases h' : cpOf c R m.replica m.inst with
    | none => rw [h'] at hB; cases hB
    | some cpR => exact ⟨cpR, rfl⟩
  obtain ⟨cpL, hcL, hLn⟩ := (I.inst _ _).leaderCopy ⟨R, cpR, hcR⟩
  have hbalR : balOf c1 m.replica m.inst R = some B := by
    simp only [balOf, hcpo R hRa]; exact hB
  have hbala : balOf c1 m.replica m.inst a = some (sint.Z cp'.ballot) := by
    simp only [balOf, hcpa, and_self, ite_true, Option.map_some]
  have hisL : r.acceptorId = r.replica ↔ a = rowOf m.replica := by
    rw [hr1, hr2, I.ids a]; exact rid32_eq_iff hrow a
  -- the reply
  have hrep : MsgOk c1 G R (.prepareReply r) := by
    simp only [MsgOk]
    rw [hr2, hr3]
    rcases hcase with ⟨hn, rfl, hok, hrb, hrs, hrv⟩ |
      ⟨c0, hc0, hl, rfl, hok, hrs, hrc, hrq, hrd, hrba⟩ |
      ⟨c0, hc0, hl, rfl, hok, hrb, hrs, hrv, hrc, hrq, hrd, hrba⟩
    · obtain ⟨hnv, hne⟩ := (I.inst m.replica m.inst).noCopy a hn
      refine ⟨fun hc => absurd (hrs ▸ hc) none_not.2, fun _ => ⟨⟨B, hbalR, by rw [hrb]; exact hbB⟩,
        a, by rw [hr1, I.ids a], fun e => hRa e.symm, by rw [hrb]; exact hown, fun _ _ => ?_⟩,
        Or.inl hok⟩
      rw [hrb]
      refine ⟨⟨_, hbala, hcpb⟩, fun b' u _ hu => absurd hu (hnv b' u),
        fun hs => absurd (hrs.symm.trans hs) st_facts.1, fun _ he => absurd he hne,
        fun hY => ?_, fun hs => absurd (hrs.symm.trans hs) st_facts.2.2.1, Or.inl hrs, hisL⟩
      subst hY; have := hcL.symm.trans hn; cases this
    · refine ⟨fun hc => ?_, fun hok' => absurd (hok.symm.trans hok') st_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
        Or.inr hok⟩
      have hv : r.valA = cp'.valA := by simp only [PrepareReplyM.valA, Copy.valA, hrc, hrq, hrd, hrba]
      rw [hv]; exact ((I.inst _ _).copies a _ hc0).committed (hrs ▸ hc)
    · have k := (I.inst _ _).copies a _ hc0
      have hv : r.valA = c0.valA := by simp only [PrepareReplyM.valA, Copy.valA, hrc, hrq, hrd, hrba]
      have : ¬ sint.Z m.ballot < sint.Z c0.ballot := fun h' => by
        rw [(slt_iff _ _).2 h'] at hl; cases hl
      have hvb := k.vbalLe
      refine ⟨fun hc => ?_, fun _ => ⟨⟨B, hbalR, by rw [hrb]; exact hbB⟩,
        a, by rw [hr1, I.ids a], fun e => hRa e.symm, by rw [hrb]; exact hown, fun hnc hnp => ?_⟩,
        Or.inl hok⟩
      · rw [hv]; exact k.committed (hrs ▸ hc)
      have hnc0 : ¬ isCommitted c0.status := hrs ▸ hnc
      rw [hrb] at hnp ⊢
      refine ⟨⟨_, hbala, Int.le_refl _⟩, fun b' u _ hu => ?_, fun hs => ?_, fun hY he => ?_,
        fun hY => ?_, fun h1 h2 h3 => ?_, ?_, hisL⟩
      · rcases k.stOk with h1 | h1 | h1 | h1
        · exact absurd hu (k.noVotes (Or.inl h1) b' u)
        · exact absurd hu (k.noVotes (Or.inr h1) b' u)
        · exact ⟨hrs.trans h1, hrv ▸ (k.accVote h1).2 b' u hu⟩
        · exact absurd h1 hnc0
      · rw [hrs] at hs
        obtain ⟨k1, _⟩ := k.accVote hs
        rw [hrv, hv]
        refine ⟨k1, ?_⟩
        rcases Int.lt_or_eq_of_le (show sint.Z c0.vbal ≤ sint.Z m.ballot by omega) with h' | h'
        · exact h'
        · exact absurd ((I.inst _ _).ainv.acc_prop _ _ _ (h' ▸ k1)) (hnp _)
      · rcases k.eqTrack hY he with k' | k' | k' | k'
        · exact Or.inl (hrs.trans k')
        · exact absurd k' hnc0
        · exact Or.inr (Or.inl ⟨hrs.trans k'.1, hrv.trans k'.2⟩)
        · exact Or.inr (Or.inr (rstBelow_le k' (by omega)))
      · subst hY
        have e : cpL = c0 := by
          have := hcL.symm.trans hc0; cases this; rfl
        subst e
        refine ⟨hrs ▸ hLn, fun v hv' => ?_⟩
        obtain ⟨cpx, hx1, hx2⟩ := (I.inst _ _).fastL v hv'
        have := hx1.symm.trans hc0; cases this
        exact hnc0 hx2
      · rw [hv]; exact k.eqCre (hrs ▸ h1) (hrv ▸ h2) h3
      · rcases k.stOk with h1 | h1 | h1 | h1
        · exact Or.inl (hrs.trans h1)
        · rcases h1 with h1 | h1
          · exact Or.inr (Or.inl (hrs.trans h1))
          · exact Or.inr (Or.inr (Or.inl (hrs.trans h1)))
        · exact Or.inr (Or.inr (Or.inr (hrs.trans h1)))
        · exact absurd h1 hnc0
  -- the old copy's status (when there is one) is the new copy's
  have hstat : ∀ c0, cpOf c a m.replica m.inst = some c0 → cp'.status = c0.status := by
    intro c0 h0
    rcases hcase with ⟨hn, -⟩ | ⟨c1', hc1, -, he, -⟩ | ⟨c1', hc1, -, rfl, -⟩
    · have := h0.symm.trans hn; cases this
    · have := h0.symm.trans hc1; cases this; rw [he]
    · have := h0.symm.trans hc1; cases this; rfl
  have hcpq : ∀ j, cpOf c1 j m.replica m.inst = if j = a then some cp' else cpOf c j m.replica m.inst := by
    intro j; by_cases hj : j = a
    · subst hj; rw [hcpa]; simp
    · rw [hcpo j hj]; simp [hj]
  -- the inflight messages
  have hsent : ∀ j, sentR j o = if R = j then [Msg.prepareReply r] else [] := by
    intro j; rw [ho]; exact sentR_single R j _
  have hcnt := countP_step hinf hze hm'
  refine ⟨G, ⟨hid, fun q' i' => ?_, fun (d : Fin 3) (y : Msg) hy => ?_, fun j q' => ?_,
    fun j q' i' cp hc => ?_, fun (d : Fin 3) (y : Msg) q' j hy hj => ?_, fun (j : Fin 3) => ?_,
    fun (q0 : Fin 3) j0 h0 h1 => ?_, fun (R' : Fin 3) q' i' cp lb hc hl hp hnc ho => ?_⟩, E⟩
  · -- instances
    by_cases hq : q' = m.replica ∧ i' = m.inst
    · obtain ⟨rfl, rfl⟩ := hq
      have I0 := I.inst m.replica m.inst
      refine ⟨ainv_evolve_same I0.ainv (E _ _), fun j cp hc => ?_, fun j hc => ?_, fun v hv => ?_,
        fun _ => ?_, fun b' R' h1 h2 => ?_, fun hn => ?_⟩
      · rw [hcpq] at hc
        by_cases hj : j = a
        · subst hj; simp only [ite_true] at hc; cases hc; exact hnew
        · simp only [hj, ite_false] at hc; exact copyOk_bal (E _ _) (I0.copies j cp hc)
      · rw [hcpq] at hc
        by_cases hj : j = a
        · subst hj; simp at hc
        · simp only [hj, ite_false] at hc; exact I0.noCopy j hc
      · obtain ⟨cpx, hx1, hx2⟩ := I0.fastL v hv
        rw [hcpq]
        by_cases hj : rowOf m.replica = a
        · simp only [hj, ite_true]; rw [hj] at hx1
          exact ⟨cp', rfl, (hstat _ hx1) ▸ hx2⟩
        · simp only [hj, ite_false]; exact ⟨cpx, hx1, hx2⟩
      · rw [hcpq]
        by_cases hj : rowOf m.replica = a
        · simp only [hj, ite_true]; rw [hj] at hcL
          exact ⟨cp', rfl, (hstat _ hcL) ▸ hLn⟩
        · simp only [hj, ite_false]; exact ⟨cpL, hcL, hLn⟩
      · obtain ⟨B0, h0, hle⟩ := I0.ownMono b' R' h1 h2
        obtain ⟨B', h', hle'⟩ := hmono _ _ R' B0 h0
        exact ⟨B', h', by omega⟩
      · have := hn a; rw [hcpq] at this; simp at this
    · refine instOk_congr (fun j => ?_) (I.inst q' i')
      by_cases hj : j = a
      · subst hj; rw [hcpa]; simp [hq]
      · exact hcpo j hj q' i'
  · -- messages
    rcases mem_step hinf hze (y := y) hy with hy1 | hy1
    · refine msgOk_evolve E (fun _ _ _ h => h) (fun x hx hb0' hc0 hc1 => ?_) (I.msgs d y hy1)
      subst hx
      refine ⟨fun cp hc => ?_, ?_⟩
      · by_cases hq : d = a ∧ x.replica = m.replica ∧ x.inst = m.inst
        · obtain ⟨rfl, h1, h2⟩ := hq
          rw [hcpa, if_pos ⟨h1, h2⟩] at hc; cases hc; exact Or.inl hcpos
        · have : cpOf c1 d x.replica x.inst = cpOf c d x.replica x.inst := by
            by_cases hj : d = a
            · subst hj; rw [hcpa, if_neg (fun h' => hq ⟨rfl, h'⟩)]
            · exact hcpo d hj _ _
          rw [this] at hc; exact hc0 cp hc
      · have k := hcnt d (fun y => y == Msg.preAccept x)
        have e1 : (c1.inflight d).count (Msg.preAccept x : gNet.M) =
            (infR c1 d).countP (fun y => y == Msg.preAccept x) := rfl
        have e2 : (c.inflight d).count (Msg.preAccept x : gNet.M) =
            (infR c d).countP (fun y => y == Msg.preAccept x) := rfl
        rw [e1]; rw [e2] at hc1
        have z1 : (Msg.prepare m == Msg.preAccept x) = false := by simp
        have z2 : (sentR d o).countP (fun y => y == Msg.preAccept x) = 0 := by
          rw [hsent]; split <;> simp
        rw [z2] at k
        split at k
        · rename_i hh; rw [z1] at hh; exact absurd hh.2 (by simp)
        · omega
    · rw [hsent] at hy1
      split at hy1
      · rename_i hRd; subst hRd
        rw [List.mem_singleton.1 hy1]; exact hrep
      · exact absurd hy1 List.not_mem_nil
  · rw [hcrt, hcrt]; exact I.crtOwn j q'
  · rw [hcrt]
    by_cases hj : j = a ∧ q' = m.replica ∧ i' = m.inst
    · obtain ⟨rfl, rfl, rfl⟩ := hj; exact ⟨hrow, hi0, hicrt⟩
    · have : cpOf c1 j q' i' = cpOf c j q' i' := by
        by_cases hj' : j = a
        · subst hj'; rw [hcpa, if_neg (fun h' => hj ⟨rfl, h'⟩)]
        · exact hcpo j hj' _ _
      rw [this] at hc; exact I.copyBelow j q' i' cp hc
  · rw [hcrt]
    rcases mem_step hinf hze (y := y) hy with hy1 | hy1
    · exact I.msgBelow d y q' j hy1 hj
    · rw [hsent] at hy1
      split at hy1
      · rw [List.mem_singleton.1 hy1] at hj
        simp only [msgInst, hr2, hr3, Option.some.injEq, Prod.mk.injEq] at hj
        obtain ⟨rfl, rfl⟩ := hj; exact ⟨hrow, hi0, hicrt⟩
      · exact absurd hy1 List.not_mem_nil
  · by_cases hj : j = a
    · subst hj; rw [hsta]; exact I.crtLen _
    · rw [hsto j hj]; exact I.crtLen j
  · rw [hcrt] at h1
    obtain ⟨cp, hc, hn⟩ := I.leaderHas q0 j0 h0 h1
    by_cases hj : q0 = a ∧ rid32 q0 = m.replica ∧ j0 = m.inst
    · obtain ⟨h1', h2', h3'⟩ := hj; subst h1'; rw [hcpa, if_pos ⟨h2', h3'⟩]
      rw [h2', h3'] at hc
      exact ⟨cp', rfl, by rw [hstat _ hc]; exact hn⟩
    · have : cpOf c1 q0 (rid32 q0) j0 = cpOf c q0 (rid32 q0) j0 := by
        by_cases hj' : q0 = a
        · subst hj'; rw [hcpa, if_neg (fun h' => hj ⟨rfl, h'⟩)]
        · exact hcpo q0 hj' _ _
      rw [this]; exact ⟨cp, hc, hn⟩
  · -- multiplicities
    have hnr : ∀ (p : Msg → Bool) j, p (.prepareReply r) = false → (sentR j o).countP p = 0 := by
      intro p j hp; rw [hsent]; split <;> simp [hp]
    have hsr : ∀ (p : Msg → Bool) j, (sentR j o).countP p ≤
        (if R = j ∧ p (.prepareReply r) = true then 1 else 0) := by
      intro p j; rw [hsent]; split <;> split <;> simp_all
    have hmatch : ∀ q' i' B Y, isOKReplyAt q' i' B Y (.prepareReply r) = true →
        Y = a ∧ isPrepareAt q' i' B (.prepare m) = true := by
      intro q' i' B Y h'
      simp only [isOKReplyAt, Bool.and_eq_true, beq_iff_eq] at h'
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h'
      refine ⟨rid32_inj (by rw [← h5, hr1, I.ids a]), ?_⟩
      have hb : r.ballot = m.ballot := by
        rcases hcase with ⟨-, -, -, hb, -⟩ | ⟨_, -, -, -, hok, -⟩ | ⟨_, -, -, -, -, hb, -⟩
        · exact hb
        · rw [hok] at h4; exact absurd h4 (by decide)
        · exact hb
      simp only [isPrepareAt, Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨hr2 ▸ h1, hr3 ▸ h2⟩, hb ▸ h3⟩
    have hold : ∃ cp0, cpOf c R' q' i' = some cp0 ∧ cp0.ballot = cp.ballot ∧ cp0.lb = cp.lb ∧
        cp0.status = cp.status := by
      by_cases hA : R' = a ∧ q' = m.replica ∧ i' = m.inst
      · obtain ⟨rfl, rfl, rfl⟩ := hA
        rw [hcpa, if_pos ⟨rfl, rfl⟩] at hc; cases hc
        rcases hcase with ⟨_, rfl, -⟩ | ⟨c0, hc0, -, rfl, -⟩ | ⟨c0, hc0, -, rfl, -⟩
        · exact absurd hl (by simp)
        · exact ⟨_, hc0, rfl, rfl, rfl⟩
        · exact absurd ho hnotown
      · have : cpOf c1 R' q' i' = cpOf c R' q' i' := by
          by_cases hj' : R' = a
          · subst hj'; rw [hcpa, if_neg (fun h' => hA ⟨rfl, h'⟩)]
          · exact hcpo R' hj' _ _
        exact ⟨cp, by rwa [this] at hc, rfl, rfl, rfl⟩
    obtain ⟨cp0, hc0, eb, el, es⟩ := hold
    obtain ⟨k1, k2⟩ := I.prepMult R' q' i' cp0 lb hc0 (el ▸ hl) hp (es ▸ hnc) (eb ▸ ho)
    rw [eb] at k1 k2
    have hP : ∀ Y : Fin 3, (infR c1 Y).countP (isPrepareAt q' i' cp.ballot) +
        (if Y = a ∧ isPrepareAt q' i' cp.ballot (.prepare m) = true then 1 else 0) =
        (infR c Y).countP (isPrepareAt q' i' cp.ballot) := by
      intro Y; have e := hcnt Y (isPrepareAt q' i' cp.ballot)
      rw [hnr _ _ rfl] at e; omega
    have hO : ∀ Y : Fin 3, (infR c1 R').countP (isOKReplyAt q' i' cp.ballot Y) ≤
        (infR c R').countP (isOKReplyAt q' i' cp.ballot Y) +
        (if R = R' ∧ isOKReplyAt q' i' cp.ballot Y (.prepareReply r) = true then 1 else 0) := by
      intro Y; have e := hcnt R' (isOKReplyAt q' i' cp.ballot Y)
      have e' := hsr (isOKReplyAt q' i' cp.ballot Y) R'
      have : isOKReplyAt q' i' cp.ballot Y (.prepare m) = false := rfl
      simp only [this, Bool.false_eq_true, and_false, ite_false] at e
      omega
    refine ⟨fun Y => ?_, fun h1 => ?_⟩
    · have e1 := hP Y; have e2 := hO Y; have k := k1 Y
      change (infR c Y).countP _ + (infR c R').countP _ ≤ 1 at k
      change (infR c1 Y).countP _ + (infR c1 R').countP _ ≤ 1
      by_cases hmt : R = R' ∧ isOKReplyAt q' i' cp.ballot Y (.prepareReply r) = true
      · obtain ⟨hYa, hpp⟩ := hmatch _ _ _ _ hmt.2
        rw [if_pos hmt] at e2; rw [if_pos ⟨hYa, hpp⟩] at e1; omega
      · rw [if_neg hmt] at e2
        split at e1 <;> omega
    · obtain ⟨hRL, hP0, hO0⟩ := k2 h1
      change (infR c _).countP _ = 0 at hP0
      change (infR c R').countP _ = 0 at hO0
      refine ⟨hRL, ?_, ?_⟩
      · change (infR c1 _).countP _ = 0
        have := hP (rowOf q'); omega
      · change (infR c1 R').countP _ = 0
        have e2 := hO (rowOf q')
        by_cases hmt : R = R' ∧ isOKReplyAt q' i' cp.ballot (rowOf q') (.prepareReply r) = true
        · obtain ⟨hYa, hpp⟩ := hmatch _ _ _ _ hmt.2
          have : 0 < (infR c (rowOf q')).countP (isPrepareAt q' i' cp.ballot) :=
            List.countP_pos_iff.2 ⟨_, hYa ▸ hm', hpp⟩
          omega
        · rw [if_neg hmt] at e2; omega

end Perennial.gryff.pureA.A1b
