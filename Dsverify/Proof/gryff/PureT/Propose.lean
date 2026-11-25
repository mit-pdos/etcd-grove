/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureT/Propose.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A2 (totality): a client's RMW (`HandleRMW` → `handlePropose` → `startPhase1`): the leader
creates instance `crtInstance[r]` (the budget bounds it), its batch from `ProposeChan`.
-/
module

public import Dsverify.Proof.gryff.PureT.EpExec
public import Dsverify.Proof.gryff.PureP.PropQ

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure.tot

open model kahn

theorem Post.trans {st : Fin 3 → RState} {r : Fin 3} {S : RState} (hM : Mono r (st r) S)
    {res : RState × List Out} (h : Post (upd st r S) r res) : Post st r res := by
  have he : upd (upd st r S) r res.1 = upd st r res.1 := by
    funext j; simp only [upd]; split <;> rfl
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨hM.trans (by simpa [upd_self] using h1), ?_, ?_⟩
  · rw [← he]; exact h2
  · rw [← he]; exact h3

theorem startPhase1_upd {st : Fin 3 → RState} {r : Fin 3} {S : RState}
    (hP : ∀ q, Pf (upd st r S) q ≤ 24) (hid : S.id = rid32 r)
    (hconf : ∀ q : Nat, q < 3 → ∀ hi, S.confAt q = some hi →
      inBox (BitVec.ofNat 32 q) hi = true ∧ (S.inst (BitVec.ofNat 32 q) hi).isSome)
    {q i : w32} {q' : Fin 3} (hq : q = rid32 q') (hb : InstB (Pf (upd st r S)) q i) (b : w32)
    (proposals : List Proposal) {cmds : List Cmd} (hcm : cmdsOk cmds = true) (hne : cmds ≠ [])
    (hG : ∀ c : Copy, c.cmds = cmds → c.status = St.PREACCEPTED → c.slot = i → c.leader = q →
      (∃ lb, c.lb = some lb ∧ lb.clientProposals = proposals ∧ lb.recoveryInst = none) →
      Good (upd st r S) r (S.setInst q i c)) :
    Ok (startPhase1 S q i b proposals cmds) (Post (upd st r S) r) :=
  startPhase1_ok hP hid hconf hq hb b proposals hcm hne hG

/-- The leader's state after `handlePropose`'s first lines (`crtInstance[r]` incremented, the
batch taken from `ProposeChan`) with its new instance's copy: the invariant, with the bound of row
`r` one larger. -/
theorem propose_si (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st) (S1 : RState)
    (h1 : S1.id = (st r).id) (h2 : S1.inst = (st r).inst) (h3 : S1.crtInstance = (st r).crtInstance)
    (h4 : S1.committedUpTo = (st r).committedUpTo) (h5 : S1.conf = (st r).conf)
    (h6 : S1.proposeQ = (st r).proposeQ) (h7 : S1.nReqs = (st r).nReqs + 1) {cid rid : w32}
    (h8 : S1.used = (cid, rid) :: (st r).used) (h9 : S1.maxN = (st r).maxN)
    (h10 : S1.ongoingReqs = (st r).ongoingReqs) (h11 : S1.wops = (st r).wops)
    (h12 : S1.rops = (st r).rops) (hn : (st r).nReqs < 24) (hcpos : 0 ≤ cid.toInt)
    (n : Nat) (P : Fin 3 → Nat)
    (hPr : P r = ((st r).crt (rid32 r)).toNat + 1) (hPq : ∀ q, q ≠ r → P q = Pf st q)
    (c : Copy) (hcm : cmdsOk c.cmds = true) (hne : c.cmds ≠ []) (hst : c.status = St.PREACCEPTED)
    (hsl : c.slot = S1.crt S1.id) (hle : c.leader = S1.id) (lb : LB)
    (hlb : c.lb = some lb) (hprops : lb.clientProposals ≠ [])
    (hpok : ∀ p ∈ lb.clientProposals, p.cmd.ok = true) (hri : lb.recoveryInst = none) :
    SI P r ((({ S1.setCrt S1.id (S1.crt S1.id + 1) with
      proposeQ := (S1.setCrt S1.id (S1.crt S1.id + 1)).proposeQ.drop n }).setInst
        S1.id (S1.crt S1.id) c)) := by
  have hs := hI r
  have hid0 := hs.id
  have hl := hs.lcrt
  have e0 : S1.id = rid32 r := h1.trans hid0
  have e1 : S1.crt S1.id = (st r).crt (rid32 r) := by simp only [RState.crt, h1, h3, hid0]
  rw [e1] at hsl ⊢
  rw [e0] at hle ⊢
  have hPle : ∀ q, Pf st q ≤ P q := by
    intro q; by_cases hq : q = r
    · subst hq; rw [hPr]; simp only [Pf]; omega
    · rw [hPq q hq]; exact Nat.le_refl _
  have hN : ((st r).crt (rid32 r)).toNat + 1 ≤ 24 := by have := hs.budget; omega
  have hinc : ((st r).crt (rid32 r) + 1).toNat = ((st r).crt (rid32 r)).toNat + 1 := by
    rw [BitVec.toNat_add]; simp; omega
  have hcrt : ∀ q : Fin 3, ((({ S1.setCrt (rid32 r) ((st r).crt (rid32 r) + 1) with
      proposeQ := (S1.setCrt (rid32 r) ((st r).crt (rid32 r) + 1)).proposeQ.drop n }).setInst
        (rid32 r) ((st r).crt (rid32 r)) c)).crt (rid32 q) =
        if q = r then (st r).crt (rid32 r) + 1 else (st r).crt (rid32 q) := by
    intro q
    simp only [setInst_crt]
    show (S1.setCrt (rid32 r) ((st r).crt (rid32 r) + 1)).crt (rid32 q) = _
    rw [crt_setCrt (by rw [h3]; exact hl)]
    split
    · rfl
    · simp only [RState.crt, RState.setCrt, h3]
  have hnone : (st r).inst (rid32 r) ((st r).crt (rid32 r)) = none := by
    cases hc : (st r).inst (rid32 r) ((st r).crt (rid32 r)) with
    | none => rfl
    | some c0 =>
      obtain ⟨⟨q', hq', hlt⟩, -⟩ := hs.inst _ _ c0 hc
      have := rid32_inj hq'; subst this
      simp only [Pf] at hlt; omega
  refine {
    id := by simp [RState.setCrt, e0]
    lcrt := by simp [RState.setCrt, h3, hl]
    lcut := by simp [RState.setCrt, h4, hs.lcut]
    lconf := by simp [RState.setCrt, h5, hs.lconf]
    nreq := by simp [RState.setInst, RState.setCrt, h7]; omega
    budget := by
      rw [hcrt, if_pos rfl, hinc]; simp [RState.setInst, RState.setCrt, h7, h9]
      have := hs.budget; omega
    crt := by
      intro q; rw [hcrt]; split
      · next hq => subst hq; rw [hinc, hPr]; exact Nat.le_refl _
      · next hq => rw [hPq q hq]; exact hs.crt q
    inst := ?_
    own := ?_
    ownOK := ?_
    cut := by
      intro q; have := hs.cut q
      simpa [RState.cut, RState.setCrt, h4] using this
    conf := ?_
    propQ := by
      intro p hp
      simp only [setInst_proposeQ, RState.setCrt, h6] at hp
      exact hs.propQ p (List.mem_of_mem_drop hp)
    usedPos := by
      intro p hp
      simp only [RState.setInst, RState.setCrt, h8, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hcpos
      · exact hs.usedPos p hp
    coord := by
      simp only [RState.setInst, RState.setCrt, h8, h9, h10, h11, h12]
      exact hs.coord.mono_used (fun p hp => List.mem_cons_of_mem _ hp) }
  · intro q i c' hc'
    simp only [setInst_inst] at hc'
    split at hc'
    · next he =>
      obtain ⟨rfl, rfl⟩ := he; cases hc'
      refine ⟨⟨r, rfl, by rw [hPr]; omega⟩, hcm, fun _ => hne, hle, hsl, ?_, ?_⟩
      · rw [hst]; exact stOk_of (by decide)
      · intro lb' h; rw [hlb] at h; simp only [Option.some.injEq] at h; subst h
        exact ⟨hpok, fun ir h => by rw [hri] at h; cases h⟩
    · simp only [RState.setCrt, h2] at hc'
      obtain ⟨hb, hcok⟩ := hs.inst q i c' hc'
      exact ⟨hb.mono hPle, hcok⟩
  · intro i hi
    rw [hcrt, if_pos rfl, hinc] at hi
    simp only [setInst_inst]
    split
    · rfl
    · next he =>
      simp only [RState.setCrt, h2]
      apply hs.own
      have hne' : i ≠ (st r).crt (rid32 r) := fun h => he (by simp [h])
      have : i.toNat ≠ ((st r).crt (rid32 r)).toNat := fun h => hne' (BitVec.eq_of_toNat_eq h)
      omega
  · intro i c' hc'
    simp only [setInst_inst] at hc'
    split at hc'
    · cases hc'
      refine ⟨(by rw [hst]; decide), (fun h => by rw [hlb] at h; cases h), ?_⟩
      intro lb' h; rw [hlb] at h; simp only [Option.some.injEq] at h; subst h; exact hprops
    · simp only [RState.setCrt, h2] at hc'
      exact hs.ownOK i c' hc'
  · intro q hi hc'
    simp only [RState.confAt, setInst_conf, RState.setCrt, h5] at hc'
    have := hs.conf q hi hc'
    simp only [setInst_inst]
    split
    · rfl
    · simpa [RState.setCrt, h2] using this

theorem Mono.setInst_none {r : Fin 3} {s : RState} {q i : w32} {c : Copy}
    (h : s.inst q i = none) : Mono r s (s.setInst q i c) := by
  refine ⟨rfl, fun _ h => h, Nat.le_refl _, ?_, fun _ _ _ h => h⟩
  intro q' i' c0 h0
  by_cases he : q' = q ∧ i' = i
  · obtain ⟨rfl, rfl⟩ := he; rw [h] at h0; cases h0
  · exact ⟨c0, by simp [he, h0], fun x => x, fun x => ⟨x, rfl⟩⟩

theorem stepClientRMW_ok (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st) (rid cid : w32)
    (k : w64) (d : Dep) (oldV newV : w64) (hk : k = 0) (hd : slt d.key 0 = true)
    (hc : sge cid 0 = true) (hn : (st r).nReqs < 24) (hu : (cid, rid) ∉ (st r).used)
    (hpq : (st r).proposeQ.length ≤ (st r).nReqs) :
    Ok (stepClientRMW (st r) rid cid k d oldV newV) (Post st r) := by
  have hn' : ¬ (24 ≤ (st r).nReqs) := by omega
  tsimp [stepClientRMW, hk, hd, hc, hn', hu, beq_self_eq_true, Bool.and_self]
  have hid0 := (hI r).id
  -- H2b-R2's guard: the slot `(r, crt[r])` is free (`hnone`, as in `hG` below)
  have hnone0 : (st r).inst (rid32 r) ((st r).crt (rid32 r)) = none := by
    cases hc : (st r).inst (rid32 r) ((st r).crt (rid32 r)) with
    | none => rfl
    | some c0 =>
      obtain ⟨⟨q', hq', hlt⟩, -⟩ := (hI r).inst _ _ c0 hc
      have := rid32_inj hq'; subst this
      simp only [Pf] at hlt; omega
  have hsd : slotDecided (st r) (st r).id ((st r).crt (st r).id) = false := by
    unfold slotDecided; rw [hid0, hnone0]
  -- H2b-R3: `ProposeChan` holds at most `nReqs < 24` proposals (unit P, `pureP.runP_Q`)
  have hq : ¬ ((st r).proposeQ.length + 1 ≥ 2 ^ 63) := by omega
  unfold handlePropose
  simp only []
  simp only [hq, ite_false]
  rw [if_neg (fun h' => absurd (h'.symm.trans hsd) (by decide))]
  unfold handleProposeBody
  simp only []
  have hl := (hI r).lcrt
  have hb0 := (hI r).budget
  have hN : ((st r).crt (rid32 r)).toNat + 1 ≤ 24 := by omega
  have hinc : ((st r).crt (rid32 r) + 1).toNat = ((st r).crt (rid32 r)).toNat + 1 := by
    rw [BitVec.toNat_add]; simp; omega
  have hS3 : ∀ q : Fin 3, ((st r).crtInstance.set (rid32 r).toNat
      ((st r).crtInstance.getD (rid32 r).toNat 0 + 1)).getD (rid32 q).toNat 0 =
      if q = r then (st r).crt (rid32 r) + 1 else (st r).crt (rid32 q) := by
    intro q
    rw [getD_set_of_lt _ _ _ _ (by rw [hl, rid32_toNat]; exact r.isLt), rid32_toNat, rid32_toNat]
    by_cases hq : q = r
    · subst hq; simp [RState.crt, rid32_toNat]
    · simp [hq, Fin.val_ne_of_ne hq, RState.crt, rid32_toNat]
  refine Ok.mono (startPhase1_upd ?hP ?hid ?hconf (q' := r) ?hq ?hb _ _ ?hcm ?hne ?hG)
    (fun res h => Post.trans ?hM h)
  case hP =>
    intro q
    simp only [Pf, upd]
    split
    · next hq =>
      subst hq
      simp only [RState.crt, RState.setCrt, hid0]
      rw [hS3, if_pos rfl, hinc]; exact hN
    · exact Pf_le hI q
  case hid => simp [RState.setCrt, hid0]
  case hq => simp [RState.setCrt, hid0]
  case hconf =>
    have := confOk hI (hI r)
    simpa [RState.setCrt, RState.confAt] using this
  case hb =>
    refine ⟨r, by simp [RState.setCrt, hid0], ?_⟩
    simp only [Pf, upd, if_pos, RState.crt, RState.setCrt, hid0]
    rw [hS3, if_pos rfl, hinc]; simp [RState.crt, hid0]
  case hcm =>
    simp only [cmdsOk, List.all_eq_true, List.mem_map, List.mem_cons]
    rintro x ⟨p, hp, rfl⟩
    rcases hp with rfl | hp
    · rfl
    · exact (hI r).propQ p (List.mem_of_mem_take (by simpa [RState.setCrt] using hp))
  case hne => simp
  case hM =>
    refine ⟨by simp [RState.setCrt], fun p h => by simp [RState.setCrt, h], ?_,
      fun q i c h => ⟨c, by simpa [RState.setCrt] using h, fun x => x, fun x => ⟨x, rfl⟩⟩,
      fun _ _ _ h => by simpa [RState.setCrt] using h⟩
    simp only [RState.crt, RState.setCrt, hid0]
    rw [hS3, if_pos rfl, hinc]; simp [RState.crt]
  case hG =>
    intro c h1 h2 h3 h4 h5
    obtain ⟨lb, hlb, hp, hri⟩ := h5
    have hnone : (st r).inst (rid32 r) ((st r).crt (rid32 r)) = none := by
      cases hc : (st r).inst (rid32 r) ((st r).crt (rid32 r)) with
      | none => rfl
      | some c0 =>
        obtain ⟨⟨q', hq', hlt⟩, -⟩ := (hI r).inst _ _ c0 hc
        have := rid32_inj hq'; subst this
        simp only [Pf] at hlt; omega
    refine ⟨?_, ?_, ?_⟩
    · rw [upd_self]; apply Mono.setInst_none
      simp only [RState.setCrt, RState.crt, hid0]; simpa [RState.crt] using hnone
    · have hpok : ∀ p ∈ lb.clientProposals, p.cmd.ok = true := by
        rw [hp]; intro p hp'
        simp only [List.mem_cons] at hp'
        rcases hp' with rfl | hp'
        · rfl
        · exact (hI r).propQ p (List.mem_of_mem_take (by simpa [RState.setCrt] using hp'))
      refine propose_si st r hI { st r with nReqs := (st r).nReqs + 1, used := (cid, rid) :: (st r).used }
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hn
        (by simpa [sge, sle] using hc) _ _ ?_ ?_ c ?_ (by rw [h1]; simp) h2
        h3 h4 lb hlb (by rw [hp]; simp) hpok hri
      · simp only [Pf, upd_self, RState.crt, RState.setCrt, hid0]
        rw [hS3, if_pos rfl, hinc]; simp [RState.crt]
      · intro q hq; simp only [Pf, upd, hq, if_false]
      · rw [h1]
        simp only [cmdsOk, List.all_eq_true, List.mem_map]
        rintro x ⟨p, hp', rfl⟩
        rw [← hp] at hp'; exact hpok p hp'
    · rw [upd_self]; rfl

end Perennial.gryff.pure.tot
