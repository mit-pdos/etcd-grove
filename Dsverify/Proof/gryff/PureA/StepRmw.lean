/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/StepRmw.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A1, internal (A1a): the step case `inv_rmw` of `inv_step` (`Inv.lean`): a client RMW
(`stepClientRMW` → `handlePropose` → `startPhase1`). The leader `a` creates instance
`(rid32 a, n)`, `n = crt[a]` (fresh: no copy, no message, no creation or proposal: `copyBelow`,
`msgBelow`, `InstOk.fresh`), with its PREACCEPTED ballot-0 copy, raises `crt[a]` to `n + 1`, and
sends the ballot-0 PreAccept to each peer. The history records the creation (`cre`) at `(q, n)`.
-/
module

public import Dsverify.Proof.gryff.PureA.StepHelp

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn

/-! ## The step, restated -/

theorem nb_true {b : Bool} (h : ¬ (!b) = true) : b = true := by cases b <;> simp_all

theorem bcastPreAccept_eq (s : RState) (r i b : w32) (cs : List Cmd) (sq : w32) (d : Deps)
    (bs : ValTag) : bcastPreAccept s r i b cs sq d bs =
      bcast s (.preAccept
        { leaderId := s.id, replica := r, inst := i, ballot := b, cmds := cs,
          seq := sq, deps := d, base := bs }) := rfl

theorem startPhase1_facts {t t' : RState} {r i : w32} {ps : List Proposal} {cs : List Cmd}
    {o : List Out} (h : startPhase1 t r i 0 ps cs = .ok (t', o)) :
    ∃ c', t'.id = t.id ∧ t'.crtInstance = t.crtInstance ∧
      (∀ q j, t'.inst q j = if q = r ∧ j = i then some c' else t.inst q j) ∧
      c'.status = St.PREACCEPTED ∧ c'.ballot = 0 ∧ c'.vbal = 0 ∧
      (∃ lb, c'.lb = some lb ∧ lb.preparing = false ∧ lb.preAcceptOKs = 0) ∧ inBox r i = true ∧
      ∃ tX : RState, tX.id = t.id ∧
        bcast tX (.preAccept
          { leaderId := tX.id, replica := r, inst := i, ballot := 0,
            cmds := c'.cmds, seq := c'.seq, deps := c'.deps, base := c'.base }) = some o := by
  unfold startPhase1 at h; peel h
  all_goals (
    cases h
    have hb := (asm : bcastPreAccept _ _ _ _ _ _ _ _ = some o)
    rw [bcastPreAccept_eq] at hb
    obtain ⟨u1, u2, u3⟩ := updateConflicts_inst (t.setInst r i _) cs r i _
    refine ⟨_, u2, u3, fun q j => by rw [u1]; rfl, rfl, rfl, rfl, ⟨_, rfl, rfl, rfl⟩, nb_true asm, _, u2, hb⟩)

theorem rmw_facts {s s' : RState} {rid cid : w32} {k : w64} {d : Dep} {oldV newV : w64}
    {o : List Out} (h : stepClientRMW s rid cid k d oldV newV = .ok (s', o)) :
    ∃ c', s'.id = s.id ∧ s'.crtInstance = (s.setCrt s.id (s.crt s.id + 1)).crtInstance ∧
      (∀ q j, s'.inst q j = if q = s.id ∧ j = s.crt s.id then some c' else s.inst q j) ∧
      c'.status = St.PREACCEPTED ∧ c'.ballot = 0 ∧ c'.vbal = 0 ∧
      (∃ lb, c'.lb = some lb ∧ lb.preparing = false ∧ lb.preAcceptOKs = 0) ∧ inBox s.id (s.crt s.id) = true ∧
      ∃ tX : RState, tX.id = s.id ∧
        bcast tX (.preAccept
          { leaderId := tX.id, replica := s.id, inst := s.crt s.id, ballot := 0,
            cmds := c'.cmds, seq := c'.seq, deps := c'.deps, base := c'.base }) = some o := by
  unfold stepClientRMW at h; peel h
  have h' := (handlePropose_ok h).2.2
  unfold handleProposeBody at h'
  exact startPhase1_facts h'


/-! ## The new history -/

/-- The history with the creation of `v` at `(q, n)`. -/
def addCre (G : GG) (q n : w32) (v : Val) : GG :=
  fun x y => if x = q ∧ y = n then { G x y with cre := fun w => w = v } else G x y

theorem addCre_other {G : GG} {q n x y : w32} {v : Val} (h : ¬ (x = q ∧ y = n)) :
    addCre G q n v x y = G x y := by
  simp only [addCre, if_neg h]

theorem addCre_at (G : GG) (q n : w32) (v : Val) :
    addCre G q n v q n = { G q n with cre := fun w => w = v } := by
  simp only [addCre, and_self, ite_true]

theorem addCre_eq (G : GG) (q n : w32) (v : Val) (x y : w32) :
    (addCre G q n v x y).eq = (G x y).eq := by
  unfold addCre; split <;> rfl

/-! ## The main case -/

theorem crt1_eq {s : RState} {q x p : w32} (hl : s.crtInstance.length = 3) (hq : q.toNat < 3) :
    (s.setCrt q x).crt p = if p = q then x else s.crt p := by
  rw [crt_setCrt _ _ _ _ (by rw [hl]; exact hq)]
  by_cases h : p = q
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]

set_option maxHeartbeats 1000000 in
theorem inv_rmw {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {rid cid : w32} {k : w64} {d : Dep}
    {oldV newV : w64} {s' : RState} {o : List Out} (I : CInv c G)
    (hp : Post c a (.rmw rid cid k d oldV newV) s' o c1)
    (h : stepR a (c.st a) (.rmw rid cid k d oldV newV) = .ok (s', o)) : StepInv c c1 G := by
  have h' : stepClientRMW (c.st a) rid cid k d oldV newV = .ok (s', o) := h
  obtain ⟨c', hs1, hs2, hs3, hcs, hcb, hcv, ⟨lb, hlb, hlbp, hlbo⟩, hbox, tX, htX, hb⟩ := rmw_facts h'
  have hid : (c.st a).id = rid32 a := I.ids a
  rw [hid] at hs1 hs2 hs3 hbox hb htX
  generalize hq : rid32 a = q at hs1 hs2 hs3 hbox hb htX
  generalize hn : (c.st a).crt q = n at hs2 hs3 hbox hb
  have hqa : rowOf q = a := by rw [← hq]; exact rowOf_rid32 a
  have hbox' := hbox
  simp only [inBox, decide_eq_true_eq] at hbox'
  have hz : sint.Z (n + 1) = sint.Z n + 1 := zsucc hbox'.2.2.1 hbox'.2.2.2
  have hqn : q.toNat < 3 := by rw [← hq]; have := a.isLt; simp [rid32]; omega
  have hrow : rowOk q = true := by simp only [rowOk, decide_eq_true_eq]; exact ⟨hbox'.1, hbox'.2.1⟩
  -- the instance is fresh
  have nocp : ∀ x, cpOf c x q n = none := by
    intro x
    cases e : cpOf c x q n with
    | none => rfl
    | some cp =>
      have := (I.copyBelow x q n cp e).2.2
      rw [hqa, hn] at this; omega
  have nomsg : ∀ (x : Fin 3) m, m ∈ c.inflight x → msgInst m ≠ some (q, n) := by
    intro x m hm e
    have := (I.msgBelow x m q n hm e).2.2
    rw [hqa, hn] at this; omega
  -- the configuration after
  obtain ⟨v, hv⟩ : ∃ v : Val, v = c'.valA := ⟨_, rfl⟩
  obtain ⟨G', hG'⟩ : ∃ G' : GG, G' = addCre G q n v := ⟨_, rfl⟩
  have hst1 : ∀ x : Fin 3, c1.st x = if x = a then s' else c.st x := fun x => by rw [hp.1]
  have hcp1 : ∀ (x : Fin 3) q' j, cpOf c1 x q' j =
      if x = a ∧ q' = q ∧ j = n then some c' else cpOf c x q' j := fun x q' j => by
    show (c1.st x).inst q' j = _
    rw [hst1 x]
    by_cases hx : x = a
    · subst hx; simp [cpOf, hs3]
    · simp [hx, cpOf]
  have hcrtI : ∀ x : Fin 3, (c1.st x).crtInstance =
      if x = a then ((c.st a).setCrt q (n + 1)).crtInstance else (c.st x).crtInstance := fun x => by
    rw [hst1 x]
    by_cases hx : x = a
    · subst hx; simp [hs2, ← hn]
    · simp [hx]
  have hcrt : ∀ (x : Fin 3) p, sint.Z ((c1.st x).crt p) =
      if x = a ∧ p = q then sint.Z n + 1 else sint.Z ((c.st x).crt p) := fun x p => by
    by_cases hx : x = a
    · subst hx
      have e : (c1.st x).crtInstance = ((c.st x).setCrt q (n + 1)).crtInstance := by
        rw [hcrtI x]; simp
      have e2 : (c1.st x).crt p = ((c.st x).setCrt q (n + 1)).crt p := by simp only [RState.crt, e]
      rw [e2, crt1_eq (I.crtLen x) hqn]
      simp only [true_and]
      split
      · exact hz
      · rfl
    · have e : (c1.st x).crtInstance = (c.st x).crtInstance := by rw [hcrtI x]; simp [hx]
      have e2 : (c1.st x).crt p = (c.st x).crt p := by simp only [RState.crt, e]
      rw [e2]; simp [hx]
  have hcrtle : ∀ (x : Fin 3) p, sint.Z ((c.st x).crt p) ≤ sint.Z ((c1.st x).crt p) := by
    intro x p; rw [hcrt]; split
    · rename_i e; obtain ⟨rfl, rfl⟩ := e; rw [hn]; omega
    · exact Int.le_refl _
  have hid1 : ∀ x : Fin 3, (c1.st x).id = (c.st x).id := fun x => by
    rw [hst1 x]
    by_cases hx : x = a
    · subst hx; simp [hs1, hid, hq]
    · simp [hx]
  let pa : PreAcceptM :=
    { leaderId := tX.id, replica := q, inst := n, ballot := 0,
      cmds := c'.cmds, seq := c'.seq, deps := c'.deps, base := c'.base }
  have hsent : ∀ x : Fin 3, sentTo gNet x o = if x = a then [] else [Msg.preAccept pa] :=
    bcast_sentTo (by rw [htX]; exact hq.symm) hb
  have hinf0 : ∀ x : Fin 3, c1.inflight x =
      c.inflight x ++ (if x = a then ([] : List gNet.M) else [Msg.preAccept pa]) := fun x => by
    rw [hp.2]
    show (if x = a then consume (gNet.recv (Ev.rmw rid cid k d oldV newV)) (c.inflight x)
      else c.inflight x) ++ sentTo gNet x o = _
    rw [hsent x]
    have : consume (gNet.recv (Ev.rmw rid cid k d oldV newV)) (c.inflight x) = c.inflight x := rfl
    rw [this, ite_self]; rfl
  have hinf : ∀ x : Fin 3, c1.inflight x =
      @HAppend.hAppend (List Msg) (List Msg) (List Msg) _ (c.inflight x)
        (if x = a then [] else [Msg.preAccept pa]) := fun x => hinf0 x
  have cntEq : ∀ (Y : Fin 3) (p : Msg → Bool), p (Msg.preAccept pa) = false →
      (c1.inflight Y).countP p = (c.inflight Y).countP p := by
    intro Y p hp0
    rw [hinf Y]; exact countP_app_ite hp0
  -- the new instance
  have I0 := I.inst q n
  have hbal0 : ∀ x, balOf c q n x = none := fun x => by simp only [balOf, nocp x]; rfl
  have hbal1 : ∀ x, balOf c1 q n x = if x = a then some 0 else none := fun x => by
    simp only [balOf, hcp1, nocp]
    by_cases hx : x = a
    · subst hx; simp [hcb]
    · simp [hx]
  have nacc := fun x => (I0.noCopy x (nocp x)).1
  have neq := fun x => (I0.noCopy x (nocp x)).2
  have ncre := (I0.fresh nocp).1
  have nprop := (I0.fresh nocp).2
  have nfast : ∀ w, ¬ (G q n).fast w := fun w hw => ncre w (I0.ainv.fast_cre w hw)
  have hGqn : G' q n = { G q n with cre := fun w => w = v } := by rw [hG']; exact addCre_at G q n v
  have E : Evolve (rowOf q) (G q n) (balOf c q n) (G' q n) (balOf c1 q n) := by
    rw [hGqn]
    exact
      { le := ⟨fun _ _ _ h => h, fun _ _ h => h, fun _ h => h, fun w h => absurd h (ncre w),
               fun _ h => h, fun _ h => h⟩
        bal_mono := fun x B h => by rw [hbal0] at h; cases h
        acc_new := fun _ _ _ h hn => absurd h hn
        eq_new := fun _ h hn => absurd h hn
        fast_new := fun _ h hn => absurd h hn
        fast_cre := fun w h => absurd h (nfast w)
        fast_eq := fun w h => absurd h (nfast w)
        fast_noprop := fun w h => absurd h (nfast w) }
  have A' : AInv (G' q n) (balOf c1 q n) (rowOf q) := by
    have A := I0.ainv
    refine { prop_uniq := ?_, acc_prop := ?_, prop_nonneg := ?_, prop_safe := ?_,
             rst_safe := ?_, cre_uniq := ?_, fast_cre := ?_, fast_eq := ?_, fast_noprop := ?_ }
    all_goals rw [hGqn]
    · exact A.prop_uniq
    · exact A.acc_prop
    · exact A.prop_nonneg
    · intro b u hpu; exact absurd hpu (nprop b u)
    · intro b hr; rw [← hGqn]; exact safeAll_evolve E (A.rst_safe b hr)
    · intro w w' h1 h2; exact h1.trans h2.symm
    · intro w h; exact absurd h (nfast w)
    · intro w h; exact absurd h (nfast w)
    · intro w h; exact absurd h (nfast w)
  have newOk : CopyOk c1 G' q n a c' :=
    { nonneg := by rw [hcb]; decide
      ballotForm := Or.inl hcb
      vbalLe := by rw [hcb, hcv]; decide
      stOk := Or.inr (Or.inl (Or.inl hcs))
      noVotes := fun _ => by rw [hGqn]; exact nacc a
      accVote := fun h => absurd (hcs.symm.trans h) (by decide)
      committed := fun h => by
        rcases h with h | h <;> exact absurd (hcs.symm.trans h) (by decide)
      rstVbal := fun _ h => absurd hcv h
      eqCre := fun h => absurd (hcs.symm.trans h) (by decide)
      leader0 := fun _ _ _ => by
        rw [hGqn]; exact ⟨hv.symm, fun u => nprop 0 u, nfast,
          fun lb' h1 => by rw [hlb] at h1; cases h1; exact hlbo⟩
      ownFresh := fun _ ho => absurd (own_pos ho) (by rw [hcb]; decide)
      preparing := fun lb' h1 h2 => by rw [hlb] at h1; cases h1; rw [hlbp] at h2; cases h2
      eqTrack := fun ha => absurd hqa.symm ha }
  have hGo : ∀ x y, ¬ (x = q ∧ y = n) → G' x y = G x y := fun x y h => by rw [hG']; exact addCre_other h
  refine ⟨G', { ids := ?_, inst := ?_, msgs := ?_, crtOwn := ?_, copyBelow := ?_,
                msgBelow := ?_, crtLen := ?_, leaderHas := ?_, prepMult := ?_ }, fun x y => ?_⟩
  · intro x; rw [hid1 x]; exact I.ids x
  · intro q' j
    by_cases e : q' = q ∧ j = n
    · obtain ⟨rfl, rfl⟩ := e
      refine { ainv := A', copies := ?_, noCopy := ?_, fastL := ?_, leaderCopy := ?_,
               ownMono := ?_, fresh := ?_ }
      · intro x cp hc
        rw [hcp1] at hc; split at hc
        · rename_i e; obtain ⟨rfl, -⟩ := e; cases hc; exact newOk
        · rw [nocp] at hc; cases hc
      · intro x hc
        rw [hcp1] at hc; split at hc
        · cases hc
        · rw [hGqn]; exact I0.noCopy x (nocp x)
      · intro w hw; rw [hGqn] at hw; exact absurd hw (nfast w)
      · intro _
        refine ⟨c', ?_, by rw [hcs]; decide⟩
        rw [hcp1, if_pos ⟨hqa, rfl, rfl⟩]
      · intro b R hR hx
        rw [hGqn] at hx
        rcases hx with hx | ⟨u, hx⟩
        · obtain ⟨B, hB, -⟩ := I0.ownMono b R hR (Or.inl hx)
          rw [hbal0] at hB; cases hB
        · exact absurd hx (nprop b u)
      · intro hn'; have := hn' a; rw [hcp1, if_pos ⟨rfl, rfl, rfl⟩] at this; cases this
    · refine instOk_G (G := G) (hGo q' j e) (instOk_congr (fun x => ?_) (I.inst q' j))
      rw [hcp1, if_neg (fun h => e ⟨h.2.1, h.2.2⟩)]
  · intro x m hm
    rw [hinf x] at hm
    rcases List.mem_append.1 hm with hm | hm
    · have hmi := nomsg x m hm
      refine msgOk_G (fun x y e => hGo x y (fun h => hmi (by rw [e, h.1, h.2])))
        (by rw [hG']; exact addCre_eq G q n v) (msgOk_congr (fun x' y' e x'' => ?_) (fun pm hpm h1 => ?_) (I.msgs x m hm))
      · rw [hcp1, if_neg (fun h => hmi (by rw [e, h.2.1, h.2.2]))]
      · subst hpm
        have hne : pm ≠ pa := fun h => hmi (by subst h; rfl)
        have e1 : (c1.inflight x).count (Msg.preAccept pm : gNet.M) =
            (c1.inflight x).countP (fun y => y == (Msg.preAccept pm : gNet.M)) := rfl
        have e2 : (c.inflight x).count (Msg.preAccept pm : gNet.M) =
            (c.inflight x).countP (fun y => y == (Msg.preAccept pm : gNet.M)) := rfl
        rw [e1, cntEq x _ (by simp [Ne.symm hne]), ← e2, h1]
    · split at hm
      · cases hm
      · rename_i hxa
        have hm' : m = Msg.preAccept pa := List.mem_singleton.1 hm
        subst hm'
        refine ⟨fun _ => ⟨by rw [hqa]; exact hxa, by show tX.id = rid32 (rowOf q); rw [hqa, htX, hq], ?_, ?_, ?_⟩,
          fun h0 => absurd rfl h0⟩
        · show (G' q n).cre _; rw [hGqn]; exact hv.symm
        · intro cp hc
          change cpOf c1 x q n = some cp at hc
          rw [hcp1 x q n, if_neg (fun h => hxa h.1), nocp x] at hc; cases hc
        · have h0 : (c.inflight x).countP (fun y => y == Msg.preAccept pa) = 0 :=
            List.countP_eq_zero.2 (fun y hy => by
              have := nomsg x y hy
              cases y with
              | preAccept z =>
                intro hz
                have hz' : z = pa := by simpa using hz
                subst hz'; exact this rfl
              | _ => intro hz; simp at hz)
          have : (c1.inflight x).countP (fun y => y == Msg.preAccept pa) = 1 := by
            rw [hinf x, if_neg hxa]
            exact (countP_app_one (by simp)).trans (by rw [h0])
          exact this
  · intro x y
    rw [hcrt, hcrt]
    by_cases hy : y = a
    · subst hy
      simp only [hq, true_and, ite_true]
      split
      · exact Int.le_refl _
      · have := I.crtOwn x y; rw [hq, hn] at this; omega
    · have hne : rid32 y ≠ q := fun e => hy (rid32_inj (e.trans hq.symm))
      simp only [hne, and_false, ite_false]
      exact I.crtOwn x y
  · intro x q' j cp hc
    rw [hcp1] at hc; split at hc
    · rename_i e; obtain ⟨-, rfl, rfl⟩ := e
      refine ⟨hrow, hbox'.2.2.1, ?_⟩
      rw [hcrt, hqa, if_pos ⟨rfl, rfl⟩]; omega
    · obtain ⟨k1, k2, k3⟩ := I.copyBelow x q' j cp hc
      exact ⟨k1, k2, Int.lt_of_lt_of_le k3 (hcrtle _ _)⟩
  · intro x m q' j hm hj
    rw [hinf x] at hm
    rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨k1, k2, k3⟩ := I.msgBelow x m q' j hm hj
      exact ⟨k1, k2, Int.lt_of_lt_of_le k3 (hcrtle _ _)⟩
    · split at hm
      · cases hm
      · have hm' : m = Msg.preAccept pa := List.mem_singleton.1 hm
        subst hm'
        simp only [msgInst, Option.some.injEq, Prod.mk.injEq] at hj
        have e1 : q' = q := hj.1.symm
        have e2 : j = n := hj.2.symm
        rw [e1, e2]
        refine ⟨hrow, hbox'.2.2.1, ?_⟩
        rw [hcrt, hqa, if_pos ⟨rfl, rfl⟩]; omega
  · intro x
    rw [hcrtI x]; split
    · simp only [RState.setCrt, List.length_set]; exact I.crtLen a
    · exact I.crtLen x
  · intro y j h0 h1
    rw [hcrt] at h1
    by_cases hy : y = a
    · subst hy
      rw [if_pos ⟨rfl, hq⟩] at h1
      rw [hq, hcp1]
      by_cases hj : j = n
      · rw [if_pos ⟨rfl, rfl, hj⟩]; exact ⟨c', rfl, by rw [hcs]; decide⟩
      · rw [if_neg (fun h => hj h.2.2)]
        have hj' : sint.Z j < sint.Z n := by
          have : sint.Z j ≠ sint.Z n := fun e => hj (BitVec.eq_of_toInt_eq e)
          omega
        have := I.leaderHas y j h0 (by rw [hq, hn]; exact hj')
        rw [hq] at this; exact this
    · have hne : ¬ (y = a ∧ rid32 y = q) := fun h => hy h.1
      rw [if_neg hne] at h1
      rw [hcp1, if_neg (fun h => hy h.1)]
      exact I.leaderHas y j h0 h1
  · intro R q' i' cp lb' hc h1 h2 h3 h4
    rw [hcp1] at hc; split at hc
    · cases hc; rw [hlb] at h1; cases h1; rw [hlbp] at h2; cases h2
    · obtain ⟨k1, k2⟩ := I.prepMult R q' i' cp lb' hc h1 h2 h3 h4
      have hP : isPrepareAt q' i' cp.ballot (Msg.preAccept pa) = false := rfl
      have hR : ∀ Y, isOKReplyAt q' i' cp.ballot Y (Msg.preAccept pa) = false := fun _ => rfl
      refine ⟨fun Y => ?_, fun ho => ?_⟩
      · rw [cntEq _ _ hP, cntEq _ _ (hR Y)]; exact k1 Y
      · obtain ⟨k3, k4, k5⟩ := k2 ho
        exact ⟨k3, by rw [cntEq _ _ hP]; exact k4, by rw [cntEq _ _ (hR _)]; exact k5⟩
  · by_cases e : x = q ∧ y = n
    · obtain ⟨rfl, rfl⟩ := e; exact E
    · rw [hGo x y e]
      have : balOf c1 x y = balOf c x y := by
        funext z
        have hne : ¬ (z = a ∧ x = q ∧ y = n) := fun h => e ⟨h.2.1, h.2.2⟩
        simp only [balOf]; rw [hcp1, if_neg hne]
      rw [this]; exact Evolve.refl (I.inst x y).ainv

end Perennial.gryff.pureA
