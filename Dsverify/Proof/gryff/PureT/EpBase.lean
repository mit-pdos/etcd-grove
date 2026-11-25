/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureT/EpBase.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A2 (totality): the EPaxos updates of a replica's state (`setInst`, `setCrt`,
`updateConflicts`, `updateCommitted`, `updateAttributes`, the broadcasts) against the invariant.
`Good st r s'`: the replica's new state `s'` keeps `Mono`, `SI` and its own `crtInstance[r]`.
-/
module

public import Dsverify.Proof.gryff.PureT.StepCoord

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure.tot

open model kahn

theorem getD_set_of_lt {α : Type} (l : List α) {n : Nat} (m : Nat) (d x : α) (hn : n < l.length) :
    (l.set n x).getD m d = if m = n then x else l.getD m d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : n = m
  · subst h; simp [hn]
  · simp [h, Ne.symm h]

theorem Pf_le {st : Fin 3 → RState} (hI : InvS st) (q : Fin 3) : Pf st q ≤ 24 := by
  have := (hI q).budget; have := (hI q).nreq; simp only [Pf]; omega

theorem InstB.lt24 {st : Fin 3 → RState} (hI : InvS st) {q i : w32} (h : InstB (Pf st) q i) :
    i.toNat < 24 := by
  obtain ⟨q', -, h⟩ := h; have := Pf_le hI q'; omega

theorem InstB.inBox {st : Fin 3 → RState} (hI : InvS st) {q i : w32} (h : InstB (Pf st) q i) :
    inBox q i = true := by
  have h24 := h.lt24 hI
  obtain ⟨q', rfl, -⟩ := h
  have hq := rid32_toInt q'
  have hi := toInt_small (x := i) (by omega)
  unfold model.inBox
  simp only [SLOTS, sint.Z]
  apply decide_eq_true
  have := q'.isLt
  omega

/-! ## `setInst`, `setCrt` -/

section
variable (s : RState) (q i : w32) (c : Copy)
@[simp] theorem setInst_inst (q' i' : w32) :
    (s.setInst q i c).inst q' i' = if q' = q ∧ i' = i then some c else s.inst q' i' := rfl
@[simp] theorem setInst_id : (s.setInst q i c).id = s.id := rfl
@[simp] theorem setInst_crtInstance : (s.setInst q i c).crtInstance = s.crtInstance := rfl
@[simp] theorem setInst_committedUpTo : (s.setInst q i c).committedUpTo = s.committedUpTo := rfl
@[simp] theorem setInst_conf : (s.setInst q i c).conf = s.conf := rfl
@[simp] theorem setInst_proposeQ : (s.setInst q i c).proposeQ = s.proposeQ := rfl
@[simp] theorem setInst_crt (x : w32) : (s.setInst q i c).crt x = s.crt x := rfl
@[simp] theorem setInst_tag : (s.setInst q i c).tag = s.tag := rfl
@[simp] theorem setInst_val : (s.setInst q i c).val = s.val := rfl
@[simp] theorem setInst_storeVT : (s.setInst q i c).storeVT = s.storeVT := rfl
@[simp] theorem setCrt_id (x : w32) : (s.setCrt q x).id = s.id := rfl
@[simp] theorem setCrt_inst (x : w32) : (s.setCrt q x).inst = s.inst := rfl
@[simp] theorem setCrt_tag (x : w32) : (s.setCrt q x).tag = s.tag := rfl
@[simp] theorem setCrt_storeVT (x : w32) : (s.setCrt q x).storeVT = s.storeVT := rfl
@[simp] theorem setCrt_committedUpTo (x : w32) : (s.setCrt q x).committedUpTo = s.committedUpTo := rfl
end

/-- A copy's replacement keeps what messages rely on. -/
def CopyMono (old : Option Copy) (c : Copy) : Prop :=
  ∀ c0, old = some c0 →
    ((c0.lb ≠ none ∨ committedSt c0.status) → (c.lb ≠ none ∨ committedSt c.status)) ∧
    (c0.status = St.EXECUTED → c.status = St.EXECUTED ∧ c.cmds = c0.cmds)

/-- Replica `r`'s new state keeps the invariant (and its own `crtInstance[r]`). -/
structure Good (st : Fin 3 → RState) (r : Fin 3) (s' : RState) : Prop where
  mono : Mono r (st r) s'
  si : SI (Pf st) r s'
  crt : s'.crt (rid32 r) = (st r).crt (rid32 r)

theorem Good.refl {st : Fin 3 → RState} {r : Fin 3} (hI : InvS st) : Good st r (st r) :=
  ⟨Mono.refl _ _, hI r, rfl⟩

theorem Good.post {st : Fin 3 → RState} {r : Fin 3} {s' : RState} {o : List Out}
    (h : Good st r s') (ho : ∀ x ∈ o, OutOk (Pf st) (upd st r s') x) : Post st r (s', o) :=
  Post.of h.mono h.crt h.si ho

theorem Good.setInst {st : Fin 3 → RState} {r : Fin 3} {s : RState} (h : Good st r s)
    {q i : w32} {c : Copy} (hb : InstB (Pf st) q i) (hc : CopyOK q i c)
    (ho : q = rid32 r → OwnOK c) (hm : CopyMono (s.inst q i) c) : Good st r (s.setInst q i c) := by
  refine ⟨h.mono.trans ?_, ?_, h.crt⟩
  · refine ⟨rfl, fun _ h => h, Nat.le_refl _, ?_, fun _ _ _ h => h⟩
    intro q' i' c0 h0
    by_cases he : q' = q ∧ i' = i
    · obtain ⟨rfl, rfl⟩ := he
      exact ⟨c, by simp, hm c0 h0⟩
    · exact ⟨c0, by simp [he, h0], fun x => x, fun x => ⟨x, rfl⟩⟩
  · have hs := h.si
    exact {
      id := hs.id, lcrt := hs.lcrt, lcut := hs.lcut, lconf := hs.lconf, nreq := hs.nreq,
      budget := hs.budget, crt := hs.crt
      inst := by
        intro q' i' c' hc'
        simp only [setInst_inst] at hc'
        split at hc'
        · next he => obtain ⟨rfl, rfl⟩ := he; cases hc'; exact ⟨hb, hc⟩
        · exact hs.inst q' i' c' hc'
      own := by
        intro i' hi'
        simp only [setInst_inst]
        split
        · rfl
        · exact hs.own i' hi'
      ownOK := by
        intro i' c' hc'
        simp only [setInst_inst] at hc'
        split at hc'
        · next he => obtain ⟨he1, rfl⟩ := he; cases hc'; exact ho he1.symm
        · exact hs.ownOK i' c' hc'
      cut := hs.cut
      conf := by
        intro q' hi hh
        simp only [setInst_inst]
        split
        · rfl
        · exact hs.conf q' hi hh
      propQ := hs.propQ, usedPos := hs.usedPos, coord := hs.coord }

theorem crt_setCrt {s : RState} (hl : s.crtInstance.length = 3) (q q' : Fin 3) (x : w32) :
    (s.setCrt (rid32 q') x).crt (rid32 q) = if q = q' then x else s.crt (rid32 q) := by
  simp only [RState.crt, RState.setCrt, rid32_toNat]
  rw [getD_set_of_lt _ _ _ _ (by rw [hl]; exact q'.isLt)]
  by_cases h : q = q'
  · subst h; simp
  · simp [h, Fin.val_ne_of_ne h]

theorem Good.setCrt {st : Fin 3 → RState} {r : Fin 3} {s : RState} (h : Good st r s)
    {q' : Fin 3} (hq : q' ≠ r) {x : w32} (hx : x.toNat ≤ Pf st q') :
    Good st r (s.setCrt (rid32 q') x) := by
  have hl := h.si.lcrt
  have hown : (s.setCrt (rid32 q') x).crt (rid32 r) = s.crt (rid32 r) := by
    rw [crt_setCrt hl, if_neg (Ne.symm hq)]
  refine ⟨h.mono.trans ?_, ?_, hown.trans h.crt⟩
  · exact ⟨rfl, fun _ h => h, by rw [hown]; exact Nat.le_refl _,
      fun _ _ c h => ⟨c, h, fun x => x, fun x => ⟨x, rfl⟩⟩,
      fun _ _ _ h => h⟩
  · have hs := h.si
    exact {
      id := hs.id, lcrt := by simp [RState.setCrt, hl], lcut := hs.lcut, lconf := hs.lconf,
      nreq := hs.nreq, budget := by rw [hown]; exact hs.budget
      crt := by
        intro q; rw [crt_setCrt hl]; split
        · next he => subst he; exact hx
        · exact hs.crt q
      inst := hs.inst, own := fun i hi => hs.own i (by rw [← hown]; exact hi), ownOK := hs.ownOK
      cut := hs.cut, conf := hs.conf, propQ := hs.propQ, usedPos := hs.usedPos, coord := hs.coord }

/-- The code's `if instance >= crtInstance[replica] { crtInstance[replica] = instance + 1 }` for an
instance some replica created (at the leader's own row it never fires). -/
theorem Good.raiseCrt {st : Fin 3 → RState} {r : Fin 3} (hI : InvS st) {s : RState}
    (h : Good st r s) {q i : w32} (hb : InstB (Pf st) q i) :
    Good st r (if sge i (s.crt q) = true then s.setCrt q (i + 1) else s) := by
  split
  · next hge =>
    obtain ⟨q', rfl, hlt⟩ := hb
    have h24 := Pf_le hI q'
    have hi1 : (i + 1).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    by_cases hq : q' = r
    · exfalso
      subst hq
      have hc : (s.crt (rid32 q')).toNat = Pf st q' := by rw [h.crt]; rfl
      have hcl : (s.crt (rid32 q')).toNat ≤ 24 := by omega
      have e1 := toInt_small (x := i) (by omega)
      have e2 := toInt_small (x := s.crt (rid32 q')) (by omega)
      simp only [sge, sle, decide_eq_true_eq, sint.Z] at hge
      omega
    · exact h.setCrt hq (by rw [hi1]; omega)
  · exact h

/-! ## `updateConflicts` -/

/-- One iteration of `updateConflicts`' loop. -/
def ucStep (s : RState) (q i seq : w32) : RState :=
  { s with
    conf := s.conf.set q.toNat (some (match s.confAt q.toNat with
        | some hi => if slt hi i then i else hi
        | none => i))
    maxSeqK0 := some (match s.maxSeqK0 with
        | some ms => if slt ms seq then seq else ms
        | none => seq) }

theorem uc_nil (s : RState) (q i seq : w32) : updateConflicts s [] q i seq = s := rfl

theorem uc_cons (s : RState) (c : Cmd) (cs : List Cmd) (q i seq : w32) :
    updateConflicts s (c :: cs) q i seq = updateConflicts (ucStep s q i seq) cs q i seq := by
  simp only [updateConflicts, List.forIn_cons]; rfl

theorem ucStep_conf (s : RState) (q i seq : w32) (n : Nat) (hi : w32)
    (h : (ucStep s q i seq).conf.getD n none = some hi) :
    s.conf.getD n none = some hi ∨ (n = q.toNat ∧ hi = i) := by
  simp only [ucStep] at h
  by_cases hlt : q.toNat < s.conf.length
  · rw [getD_set_of_lt _ _ _ _ hlt] at h
    split at h
    · next hn =>
      subst hn
      cases h
      cases hc : s.confAt q.toNat with
      | none => right; simp [hc]
      | some hh =>
        simp only [hc]
        split
        · right; simp
        · left; simpa [RState.confAt] using hc
    · left; exact h
  · have : s.conf.set q.toNat (some (match s.confAt q.toNat with
        | some hi => if slt hi i = true then i else hi
        | none => i)) = s.conf := List.set_eq_of_length_le (by omega)
    rw [this] at h
    left; exact h

theorem updateConflicts_eq (s : RState) (cmds : List Cmd) (q i seq : w32) :
    ∃ cf ms, updateConflicts s cmds q i seq = { s with conf := cf, maxSeqK0 := ms } ∧
      cf.length = s.conf.length ∧
      ∀ n hi, cf.getD n none = some hi → s.conf.getD n none = some hi ∨ (n = q.toNat ∧ hi = i) := by
  induction cmds generalizing s with
  | nil => exact ⟨s.conf, s.maxSeqK0, rfl, rfl, fun n hi h => Or.inl h⟩
  | cons c cs ih =>
    obtain ⟨cf, ms, he, hl, hcf⟩ := ih (ucStep s q i seq)
    refine ⟨cf, ms, by rw [uc_cons, he]; rfl, by rw [hl]; simp [ucStep], ?_⟩
    intro n hi hn
    rcases hcf n hi hn with h1 | h1
    · exact ucStep_conf s q i seq n hi h1
    · exact Or.inr h1

theorem Good.updConf {st : Fin 3 → RState} {r : Fin 3} {s : RState} (h : Good st r s)
    (cmds : List Cmd) {q' : Fin 3} {i : w32} (hi : (s.inst (rid32 q') i).isSome) (seq : w32) :
    Good st r (updateConflicts s cmds (rid32 q') i seq) := by
  obtain ⟨cf, ms, he, hl, hcf⟩ := updateConflicts_eq s cmds (rid32 q') i seq
  rw [he]
  refine ⟨h.mono.trans ⟨rfl, fun _ h => h, Nat.le_refl _,
    fun _ _ c h => ⟨c, h, fun x => x, fun x => ⟨x, rfl⟩⟩, fun _ _ _ h => h⟩, ?_, h.crt⟩
  have hs := h.si
  exact {
    id := hs.id, lcrt := hs.lcrt, lcut := hs.lcut, lconf := by simp [hl, hs.lconf], nreq := hs.nreq,
    budget := hs.budget, crt := hs.crt, inst := hs.inst, own := hs.own, ownOK := hs.ownOK,
    cut := hs.cut
    conf := by
      intro q hh hc
      simp only [RState.confAt] at hc
      rcases hcf q.val hh hc with h1 | ⟨h2, h3⟩
      · exact hs.conf q hh (by simp only [RState.confAt]; exact h1)
      · subst h3
        rw [rid32_toNat] at h2
        have : q = q' := Fin.ext h2
        subst this; exact hi
    propQ := hs.propQ, usedPos := hs.usedPos, coord := hs.coord }

@[simp] theorem updConf_id (s : RState) (cmds : List Cmd) (q i seq : w32) :
    (updateConflicts s cmds q i seq).id = s.id := by
  obtain ⟨cf, ms, he, -⟩ := updateConflicts_eq s cmds q i seq; rw [he]
@[simp] theorem updConf_inst (s : RState) (cmds : List Cmd) (q i seq : w32) :
    (updateConflicts s cmds q i seq).inst = s.inst := by
  obtain ⟨cf, ms, he, -⟩ := updateConflicts_eq s cmds q i seq; rw [he]
@[simp] theorem updConf_proposeQ (s : RState) (cmds : List Cmd) (q i seq : w32) :
    (updateConflicts s cmds q i seq).proposeQ = s.proposeQ := by
  obtain ⟨cf, ms, he, -⟩ := updateConflicts_eq s cmds q i seq; rw [he]

/-! ## `updateAttributes`, `updateCommitted` -/

theorem updAttr_ok (s : RState)
    (hconf : ∀ q : Nat, q < 3 → ∀ hi, s.confAt q = some hi →
      inBox (BitVec.ofNat 32 q) hi = true ∧ (s.inst (BitVec.ofNat 32 q) hi).isSome)
    (cmds : List Cmd) (seq : w32) (deps : Deps) (rep : w32) :
    OkO (updateAttributes s cmds seq deps rep) (fun _ => True) := by
  simp only [updateAttributes]
  apply OkO.bind
  refine (OkO.loop _ _ _ (fun _ _ => True) trivial ?_).mono (fun _ _ => ?_)
  · intro pre q post b hl _
    have hq : q < 3 := by
      have : q ∈ [0, 1, 2] := by rw [hl]; simp
      simp at this; omega
    split
    · exact OkO.some trivial
    · apply OkO.bind
      refine (OkO.loop _ _ _ (fun _ _ => True) trivial ?_).mono (fun _ _ => OkO.some trivial)
      intro pre' c post' b' _ _
      split
      · next hi hc =>
        split
        · obtain ⟨h1, h2⟩ := hconf q hq hi hc
          obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 h2
          simp only [h1, if_true, hw]
          split <;> exact OkO.some trivial
        · exact OkO.some trivial
      · exact OkO.some trivial
  · apply OkO.bind
    refine (OkO.loop _ _ _ (fun _ _ => True) trivial ?_).mono (fun _ _ => OkO.some trivial)
    intro pre' c post' b' _ _
    split
    · split <;> exact OkO.some trivial
    · exact OkO.some trivial

theorem confOk {st : Fin 3 → RState} (hI : InvS st) {r : Fin 3} {s : RState} (h : SI (Pf st) r s) :
    ∀ q : Nat, q < 3 → ∀ hi, s.confAt q = some hi →
      inBox (BitVec.ofNat 32 q) hi = true ∧ (s.inst (BitVec.ofNat 32 q) hi).isSome := by
  intro q hq hi hc
  have h1 := h.conf ⟨q, hq⟩ hi hc
  obtain ⟨c, hc'⟩ := Option.isSome_iff_exists.1 h1
  exact ⟨(h.inst _ _ c hc').1.inBox hI, h1⟩

theorem advanceCut_ok (s : RState) (q : w32) (hq : ∃ q' : Fin 3, q = rid32 q')
    (hc : ∀ j : w32, (s.inst q j).isSome → j.toNat < 24) :
    ∀ f (k : w32), (k = -1 ∨ k.toNat < 24) →
      24 - (if k = -1 then 0 else k.toNat + 1) < f →
      ∃ k', advanceCut s q f k = some k' ∧ (k' = -1 ∨ k'.toNat < 24) := by
  intro f
  induction f with
  | zero => intro k _ h; omega
  | succ f ih =>
    intro k hk hf
    have hj : (k + 1).toNat = if k = -1 then 0 else k.toNat + 1 := by
      split
      · next h => subst h; rfl
      · rcases hk with hk | hk
        · contradiction
        · rw [BitVec.toNat_add]; simp; omega
    have hb : inBox q (k + 1) = true := by
      obtain ⟨q', rfl⟩ := hq
      have hq2 := rid32_toInt q'
      have hj24 : (k + 1).toNat ≤ 24 := by
        rw [hj]; split
        · omega
        · rcases hk with hk | hk
          · contradiction
          · omega
      have hi := toInt_small (x := k + 1) (by omega)
      unfold inBox
      simp only [SLOTS, sint.Z]
      apply decide_eq_true
      have := q'.isLt
      omega
    simp only [advanceCut, hb, Bool.not_true, Bool.false_eq_true, if_false]
    split
    · next c hcs =>
      split
      · have hlt := hc (k + 1) (by rw [hcs]; rfl)
        have hne : k + 1 ≠ -1 := by
          intro h; rw [h] at hlt; simp at hlt
        apply ih (k + 1) (Or.inr hlt)
        rw [if_neg hne]; rw [hj] at hlt ⊢
        generalize (if k = -1 then 0 else k.toNat + 1) = a at hf hlt ⊢
        omega
      · exact ⟨k, rfl, hk⟩
    · exact ⟨k, rfl, hk⟩

theorem Good.updCommitted {st : Fin 3 → RState} (hI : InvS st) {r : Fin 3} {s : RState}
    (h : Good st r s) (q' : Fin 3) : OkO (updateCommitted s (rid32 q')) (Good st r) := by
  have hc : ∀ j : w32, (s.inst (rid32 q') j).isSome → j.toNat < 24 := by
    intro j hj
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hj
    exact (h.si.inst _ _ c hc).1.lt24 hI
  obtain ⟨k', hk', hk'b⟩ := advanceCut_ok s (rid32 q') ⟨q', rfl⟩ hc (SLOTS.toNat + 1)
    (s.cut (rid32 q')) (h.si.cut q') (by simp only [SLOTS]; split <;> omega)
  simp only [updateCommitted, hk']
  refine OkO.some ⟨h.mono.trans ⟨rfl, fun _ h => h, Nat.le_refl _,
    fun _ _ c h => ⟨c, h, fun x => x, fun x => ⟨x, rfl⟩⟩, fun _ _ _ h => h⟩, ?_, h.crt⟩
  have hs := h.si
  have hl := hs.lcut
  exact {
    id := hs.id, lcrt := hs.lcrt, lcut := by simp [Deps.setAt, hl], lconf := hs.lconf,
    nreq := hs.nreq, budget := hs.budget, crt := hs.crt, inst := hs.inst, own := hs.own,
    ownOK := hs.ownOK
    cut := by
      intro q
      simp only [RState.cut, Deps.at, Deps.setAt, rid32_toNat]
      rw [getD_set_of_lt _ _ _ _ (by rw [hl]; have := q'.isLt; omega)]
      split
      · exact hk'b
      · have := hs.cut q; simpa [RState.cut, Deps.at, rid32_toNat] using this
    conf := hs.conf, propQ := hs.propQ, usedPos := hs.usedPos, coord := hs.coord }

theorem Good.propAppend {st : Fin 3 → RState} {r : Fin 3} {s : RState} (h : Good st r s)
    (ps : List Proposal) (hp : ∀ p ∈ ps, p.cmd.ok = true) :
    Good st r { s with proposeQ := s.proposeQ ++ ps } := by
  refine ⟨h.mono.trans ⟨rfl, fun _ h => h, Nat.le_refl _,
    fun _ _ c h => ⟨c, h, fun x => x, fun x => ⟨x, rfl⟩⟩, fun _ _ _ h => h⟩, ?_, h.crt⟩
  have hs := h.si
  exact {
    id := hs.id, lcrt := hs.lcrt, lcut := hs.lcut, lconf := hs.lconf, nreq := hs.nreq,
    budget := hs.budget, crt := hs.crt, inst := hs.inst, own := hs.own, ownOK := hs.ownOK,
    cut := hs.cut, conf := hs.conf
    propQ := by
      intro p hp'; simp only [List.mem_append] at hp'
      rcases hp' with hp' | hp'
      · exact hs.propQ p hp'
      · exact hp p hp'
    usedPos := hs.usedPos, coord := hs.coord }

/-- The leader's own copy of an instance it created exists. -/
theorem own_some {st : Fin 3 → RState} {r : Fin 3} {s : RState} (h : Good st r s) {i : w32}
    (hb : InstB (Pf st) (rid32 r) i) : (s.inst (rid32 r) i).isSome := by
  obtain ⟨q', hq, hlt⟩ := hb
  have := rid32_inj hq; subst this
  apply h.si.own
  rw [h.crt]; exact hlt

/-- Any copy at replica `r` (with the given state) is of an instance some replica created. -/
theorem Good.copy {st : Fin 3 → RState} {r : Fin 3} {s : RState} (h : Good st r s) {q i : w32}
    {c : Copy} (hc : s.inst q i = some c) : InstB (Pf st) q i ∧ CopyOK q i c :=
  h.si.inst q i c hc

end Perennial.gryff.pure.tot
