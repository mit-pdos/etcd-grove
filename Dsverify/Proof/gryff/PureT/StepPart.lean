/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureT/StepPart.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A2 (totality): field-frame lemmas, and the participant's steps (`Read1`, `Read2`, `Write1`,
`Write2`, the forced-write ticker).
-/
module

public import Dsverify.Proof.gryff.PureT.Frame

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure.tot

open model kahn

/-- `s'` has `s`'s EPaxos fields. -/
structure EqE (s s' : RState) : Prop where
  id : s'.id = s.id
  crtInstance : s'.crtInstance = s.crtInstance
  committedUpTo : s'.committedUpTo = s.committedUpTo
  conf : s'.conf = s.conf
  inst : s'.inst = s.inst
  proposeQ : s'.proposeQ = s.proposeQ

/-- `s'` has `s`'s coordinator fields. -/
structure EqG (s s' : RState) : Prop where
  nReqs : s'.nReqs = s.nReqs
  used : s'.used = s.used
  maxN : s'.maxN = s.maxN
  ongoingReqs : s'.ongoingReqs = s.ongoingReqs
  wops : s'.wops = s.wops
  rops : s'.rops = s.rops

theorem SI.congr {P : Fin 3 → Nat} {r : Fin 3} {s s' : RState} (h : SI P r s) (he : EqE s s')
    (hg : EqG s s') : SI P r s' := by
  have hcrt : ∀ q, s'.crt q = s.crt q := fun q => by simp [RState.crt, he.crtInstance]
  have hcut : ∀ q, s'.cut q = s.cut q := fun q => by simp [RState.cut, he.committedUpTo]
  have hconf : ∀ q, s'.confAt q = s.confAt q := fun q => by simp [RState.confAt, he.conf]
  exact {
    id := he.id.trans h.id
    lcrt := he.crtInstance ▸ h.lcrt
    lcut := he.committedUpTo ▸ h.lcut
    lconf := he.conf ▸ h.lconf
    nreq := hg.nReqs ▸ h.nreq
    budget := by rw [hg.nReqs, hg.maxN, hcrt]; exact h.budget
    crt := fun q => by rw [hcrt]; exact h.crt q
    inst := fun q i c hc => h.inst q i c (by rw [← he.inst]; exact hc)
    own := fun i hi => by rw [he.inst]; exact h.own i (by rw [← hcrt]; exact hi)
    ownOK := fun i c hc => h.ownOK i c (by rw [← he.inst]; exact hc)
    cut := fun q => by rw [hcut]; exact h.cut q
    conf := fun q hi hh => by rw [he.inst]; exact h.conf q hi (by rw [← hconf]; exact hh)
    propQ := by rw [he.proposeQ]; exact h.propQ
    usedPos := by rw [hg.used]; exact h.usedPos
    coord := by rw [hg.ongoingReqs, hg.maxN, hg.wops, hg.rops, hg.used]; exact h.coord }

theorem Mono.of_eq {r : Fin 3} {s s' : RState} (he : EqE s s') (hg : EqG s s') : Mono r s s' where
  id := he.id
  used := fun p h => by rw [hg.used]; exact h
  crt := by simp [RState.crt, he.crtInstance]
  inst := fun q i c h => ⟨c, by rw [he.inst]; exact h, fun x => x, fun x => ⟨x, rfl⟩⟩
  wt := fun rid cid _ h => by rw [hg.wops]; exact h

theorem EqE.refl (s : RState) : EqE s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem EqG.refl (s : RState) : EqG s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem EqE.trans {s1 s2 s3 : RState} (a : EqE s1 s2) (b : EqE s2 s3) : EqE s1 s3 :=
  ⟨b.1.trans a.1, b.2.trans a.2, b.3.trans a.3, b.4.trans a.4, b.5.trans a.5, b.6.trans a.6⟩
theorem EqG.trans {s1 s2 s3 : RState} (a : EqG s1 s2) (b : EqG s2 s3) : EqG s1 s3 :=
  ⟨b.1.trans a.1, b.2.trans a.2, b.3.trans a.3, b.4.trans a.4, b.5.trans a.5, b.6.trans a.6⟩

theorem overwrite_eqE (s : RState) (v : w64) (t : model.Tag) : EqE s (s.overwrite v t) := by
  unfold RState.overwrite; split
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact EqE.refl s
theorem overwrite_eqG (s : RState) (v : w64) (t : model.Tag) : EqG s (s.overwrite v t) := by
  unfold RState.overwrite; split
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact EqG.refl s
theorem overwrite_id (s : RState) (v : w64) (t : model.Tag) : (s.overwrite v t).id = s.id :=
  (overwrite_eqE s v t).id

/-- The postcondition of a step that keeps the replica's own `crtInstance[r]`. -/
theorem Post.of {st : Fin 3 → RState} {r : Fin 3} {s' : RState} {o : List Out}
    (hM : Mono r (st r) s') (hc : s'.crt (rid32 r) = (st r).crt (rid32 r))
    (hSI : SI (Pf st) r s') (hO : ∀ x ∈ o, OutOk (Pf st) (upd st r s') x) :
    Post st r (s', o) := by
  have hP : Pf (upd st r s') = Pf st := by
    funext q; by_cases hq : q = r
    · subst hq; simp [Pf, upd_self, hc]
    · simp [Pf, upd_ne _ _ hq]
  refine ⟨hM, ?_, ?_⟩ <;> simp only [hP]
  · exact hSI
  · exact hO

/-- A step that changes no field of the invariant. -/
theorem Post.of_eq {st : Fin 3 → RState} {r : Fin 3} {s' : RState} {o : List Out}
    (hI : SI (Pf st) r (st r)) (he : EqE (st r) s') (hg : EqG (st r) s')
    (hO : ∀ x ∈ o, OutOk (Pf st) (upd st r s') x) : Post st r (s', o) :=
  Post.of (Mono.of_eq he hg) (by simp [RState.crt, he.crtInstance]) (hI.congr he hg) hO

/-- The configuration's invariant, as the step lemmas take it. -/
def InvS (st : Fin 3 → RState) : Prop := ∀ q, SI (Pf st) q (st q)

/-! ## The participant -/

theorem stepForceWrite_ok (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st) :
    Ok (stepForceWrite (st r)) (Post st r) :=
  Ok.ret (Post.of_eq (hI r) (EqE.refl _) (EqG.refl _) (by simp))

theorem stepRead1_ok (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st) (m : Read1ProxiedM)
    (hm : MInv (Pf st) st r (.read1 m)) : Ok (stepRead1 (st r) m) (Post st r) := by
  simp only [MInv] at hm
  obtain ⟨hk, hd, q, hq⟩ := hm
  have h1 : dep0.key = 0 := rfl
  have h0 : sge (0 : w64) 0 = true := by decide
  tsimp [stepRead1, hk, hd, hq, sendTo_rid, h1, h0]
  refine Ok.ret (Post.of_eq (hI r) ?_ ?_ ?_)
  · exact (overwrite_eqE _ _ _).trans (overwrite_eqE _ _ _)
  · exact (overwrite_eqG _ _ _).trans (overwrite_eqG _ _ _)
  · simp [OutOk, MInv]

theorem stepWrite1_ok (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st) (m : Write1ProxiedM)
    (hm : MInv (Pf st) st r (.write1 m)) : Ok (stepWrite1 (st r) m) (Post st r) := by
  simp only [MInv] at hm
  obtain ⟨hk, hd, hf, q, hq⟩ := hm
  have hd' : sge m.d.key 0 = false := by
    simp only [slt, sge, sle, decide_eq_true_eq, decide_eq_false_iff_not] at hd ⊢; omega
  have h1 : (!sgt (1 : w32) 0) = false := by decide
  tsimp [stepWrite1, hk, hd', hf, hq, sendTo_rid, h1]
  repeat' split
  all_goals first
    | exact Ok.ret (Post.of_eq (hI r) (EqE.refl _) (EqG.refl _) (by simp [OutOk, MInv]))
    | exact Ok.ret (Post.of_eq (hI r) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
        (by simp [OutOk, MInv]))

theorem stepWrite2_ok (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st) (m : Write2ProxiedM)
    (hm : MInv (Pf st) st r (.write2 m)) : Ok (stepWrite2 (st r) m) (Post st r) := by
  simp only [MInv] at hm
  obtain ⟨hk, q, hq, hw⟩ := hm
  tsimp [stepWrite2, hk, hq, sendTo_rid]
  have he : EqE (st r) { (st r).overwrite m.vt.v m.vt.t with
      ongoing := AMap.del ((st r).overwrite m.vt.v m.vt.t).ongoing m.clientId } :=
    (overwrite_eqE _ _ _).trans ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hg : EqG (st r) { (st r).overwrite m.vt.v m.vt.t with
      ongoing := AMap.del ((st r).overwrite m.vt.v m.vt.t).ongoing m.clientId } :=
    (overwrite_eqG _ _ _).trans ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine Ok.ret (Post.of_eq (hI r) he hg ?_)
  simp only [List.mem_singleton, forall_eq, OutOk, MInv]
  exact hw.mono (mono_upd (Mono.of_eq he hg))

end Perennial.gryff.pure.tot
