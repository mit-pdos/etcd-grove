/-
The kit's porcupine model, pure (notes/dsv-gryff.md; the analogue of paxos's
`examples/paxosnet/ModelSet.lean`): the int64 register with compare-and-swap whose writes and
compare-and-swaps of unknown outcome stay pending, as linkv's pending-writes store (`casB`, a
`linkv.PendSpec`), and `step` (kit.go) on the model's state, a list of configurations `Cfgs`
standing for those reachable from them (`cfgSet`), as `pSeq casB`'s step (`stepG_pSeq`).

* `applyG`, `isWriteG`: kit.go's `apply` and `isWrite`; `casB` the store.
* `AReach x r`: `r` is reachable from `x` by pending operations taking effect, one at a time, each
  removed from the pending list by its index (kit.go's `reach` with `without`); up to the order of
  the pending list (`peq`), it is the store's `PReach` (`areach_of_preach`, `preach_of_areach`).
* `stepG_pSeq`: with `Cfgs ≠ []`, an unknown write appends the input to every configuration's
  pending list, an unknown read changes nothing, and an answered operation's next configurations
  are those `step`'s loop collects (`cs'`, any list with exactly the members `knownCfgs` describes;
  `ModelProof.lean` shows the Go loop's list is one), the step failing when there are none.
-/
module

public import Dsverify.Code.gryff.examples.gryffnet
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.txnwork.PendModel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

namespace gryff.examples.gryffnet

open EtcdGrove EtcdGrove.linkv

section pure
variable [GooseExts]

instance In.decEq : DecidableEq In := fun a b =>
  decidable_of_iff (a.Op' = b.Op' ∧ a.A' = b.A' ∧ a.B' = b.B') (by
    cases a; cases b; simp)

instance Out.decEq : DecidableEq Out := fun a b =>
  decidable_of_iff (a.Unknown' = b.Unknown' ∧ a.V' = b.V') (by
    cases a; cases b; simp)

/-- A Write's and a CAS's output, `Out{}`. -/
def outDone : Out := ⟨false, W64 0⟩

/-- kit.go's `apply`: the register's step from value `v`, the next value and the output. -/
def applyG (v : w64) (i : In) : w64 × Out :=
  if i.Op' = W64 1 then (i.A', outDone)
  else if i.Op' = W64 2 then ((if v = i.A' then i.B' else v), outDone)
  else (v, ⟨false, v⟩)

/-- kit.go's `isWrite`. -/
def isWriteG (i : In) : Bool := decide (i.Op' = W64 1) || decide (i.Op' = W64 2)

/-- **The register** as linkv's pending-writes store: from `0`, `apply`'s step, Writes and CASes
pending when their outcome is unknown. -/
def casB : PendSpec w64 In Out where
  init := W64 0
  step i v := applyG v i
  isWrite := isWriteG

/-- A configuration (kit.go's `Cfg`: the value and the pending operations, in order). -/
abbrev GCfg := PCfg w64 In

/-- The configurations the model's list `cs` stands for: those reachable from one of them. -/
def cfgSet (cs : List GCfg) : PSet w64 In := fun c => ∃ x ∈ cs, PReach casB x c

/-- The same configuration up to the order of the pending list. -/
def peq (c d : GCfg) : Prop := c.st = d.st ∧ c.pend.Perm d.pend

/-- kit.go's `reach`: pending operations taking effect, each removed by its index (`without`). -/
inductive AReach : GCfg → GCfg → Prop where
  | refl (c : GCfg) : AReach c c
  | step {c d : GCfg} (k : Nat) (hk : k < c.pend.length) :
      AReach ⟨(applyG c.st c.pend[k]).1, c.pend.eraseIdx k⟩ d → AReach c d

/-- The configurations an answered operation `(i, o)` leads to from `cs` (kit.go's `step`, its
second loop): from a configuration reachable from one of `cs`'s, the operation with output `o`. -/
def knownCfgs (cs : List GCfg) (i : In) (o : Out) (y : GCfg) : Prop :=
  ∃ x ∈ cs, ∃ r, AReach x r ∧ applyG r.st i = (y.st, o) ∧ y.pend = r.pend

/-! ## Reachability -/

theorem perm_getElem_eraseIdx {α : Type} : ∀ (l : List α) (k : Nat) (hk : k < l.length),
    l.Perm (l[k] :: l.eraseIdx k)
  | _ :: _, 0, _ => by simp
  | a :: l, k + 1, hk => by
    have ih := perm_getElem_eraseIdx l k (by simp at hk; omega)
    simp only [List.getElem_cons_succ, List.eraseIdx_cons_succ]
    exact (ih.cons a).trans (List.Perm.swap _ _ _)

theorem eraseIdx_perm_erase (l : List In) (k : Nat) (hk : k < l.length) :
    (l.eraseIdx k).Perm (l.erase l[k]) := by
  have h1 := perm_getElem_eraseIdx l k hk
  have h2 := List.perm_cons_erase (List.getElem_mem hk)
  exact (h1.symm.trans h2).cons_inv

theorem preach_of_peq {c d : GCfg} (h : peq c d) : PReach casB c d := by
  obtain ⟨h1, h2⟩ := h
  have hs : PSilent casB c ⟨c.st, d.pend⟩ := .perm c d.pend h2.symm
  have : (⟨c.st, d.pend⟩ : GCfg) = d := by rw [h1]
  rw [this] at hs
  exact .single hs

theorem peq_refl (c : GCfg) : peq c c := ⟨rfl, .refl _⟩

theorem peq_trans {a b c : GCfg} (h1 : peq a b) (h2 : peq b c) : peq a c :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem preach_of_areach {x r : GCfg} (h : AReach x r) : PReach casB x r := by
  induction h with
  | refl => exact .refl _
  | @step c d k hk _ ih =>
    have hs : PSilent casB c ⟨(casB.step c.pend[k] c.st).1, c.pend.erase c.pend[k]⟩ :=
      .apply c c.pend[k] (List.getElem_mem hk)
    refine (PReach.single hs).trans ((preach_of_peq ?_).trans ih)
    exact ⟨rfl, (eraseIdx_perm_erase c.pend k hk).symm⟩

theorem areach_peq {x x' r' : GCfg} (hx : peq x x') (h : AReach x' r') :
    ∃ r, AReach x r ∧ peq r r' := by
  induction h generalizing x with
  | refl c => exact ⟨x, .refl _, hx⟩
  | @step c d k hk _ ih =>
    have ha : c.pend[k] ∈ x.pend := hx.2.symm.subset (List.getElem_mem hk)
    have hk0 : x.pend.idxOf c.pend[k] < x.pend.length := List.idxOf_lt_length_of_mem ha
    have hget : x.pend[x.pend.idxOf c.pend[k]] = c.pend[k] := List.getElem_idxOf hk0
    have hy : peq ⟨(applyG x.st x.pend[x.pend.idxOf c.pend[k]]).1,
        x.pend.eraseIdx (x.pend.idxOf c.pend[k])⟩ ⟨(applyG c.st c.pend[k]).1, c.pend.eraseIdx k⟩ := by
      refine ⟨by simp only [hget, hx.1], ?_⟩
      rw [← List.erase_eq_eraseIdx_of_idxOf rfl]
      exact (hx.2.erase _).trans (eraseIdx_perm_erase c.pend k hk).symm
    obtain ⟨r, hr, hpe⟩ := ih hy
    exact ⟨r, .step _ hk0 hr, hpe⟩

theorem areach_of_preach {x c : GCfg} (h : PReach casB x c) : ∃ r, AReach x r ∧ peq r c := by
  induction h with
  | refl c => exact ⟨c, .refl _, peq_refl c⟩
  | @step x x1 c hs _ ih =>
    obtain ⟨r1, hr1, hpe1⟩ := ih
    cases hs with
    | perm p hp =>
      obtain ⟨r, hr, hpe⟩ := areach_peq (x := x) (x' := ⟨x.st, p⟩) ⟨rfl, hp.symm⟩ hr1
      exact ⟨r, hr, peq_trans hpe hpe1⟩
    | apply i hi =>
      have hk0 : x.pend.idxOf i < x.pend.length := List.idxOf_lt_length_of_mem hi
      have hget : x.pend[x.pend.idxOf i] = i := List.getElem_idxOf hk0
      refine ⟨r1, .step _ hk0 ?_, hpe1⟩
      have he : x.pend.erase i = x.pend.eraseIdx (x.pend.idxOf i) :=
        List.erase_eq_eraseIdx_of_idxOf rfl
      rw [hget, ← he]
      exact hr1

theorem preach_append (i : In) {x c : GCfg} (h : PReach casB x c) :
    PReach casB ⟨x.st, x.pend ++ [i]⟩ ⟨c.st, c.pend ++ [i]⟩ := by
  induction h with
  | refl => exact .refl _
  | @step x x1 c hs _ ih =>
    refine .step ?_ ih
    cases hs with
    | perm p hp => exact .perm _ _ (hp.append_right [i])
    | apply j hj =>
      have := PSilent.apply (P := casB) ⟨x.st, x.pend ++ [i]⟩ j (List.mem_append_left _ hj)
      simpa [List.erase_append_left _ hj] using this

/-! ## The steps -/

theorem obs_false {i : In} (h : casB.isObs i = true) : False := by
  simp [casB] at h

/-- An unknown write: pending in every configuration. -/
theorem post_errW (cs : List GCfg) (i : In) (hw : isWriteG i = true) :
    ppost casB (cfgSet cs) i .err = cfgSet (cs.map fun x => ⟨x.st, x.pend ++ [i]⟩) := by
  funext c'
  apply propext
  constructor
  · rintro ⟨c0, c, c1, ⟨x, hx, h0⟩, h1, hst, h2⟩
    cases hst with
    | errW _ _ =>
      refine ⟨⟨x.st, x.pend ++ [i]⟩, List.mem_map.2 ⟨x, hx, rfl⟩, ?_⟩
      refine (preach_append i (h0.trans h1)).trans ((preach_of_peq (c := ⟨c.st, c.pend ++ [i]⟩)
        (d := ⟨c.st, i :: c.pend⟩) ⟨rfl, List.perm_append_singleton _ _⟩).trans h2)
    | errR h _ => simp [casB, hw] at h
  · rintro ⟨y, hy, hyc⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    refine ⟨x, x, ⟨x.st, i :: x.pend⟩, ⟨x, hx, .refl _⟩, .refl _, .errW x i hw rfl, ?_⟩
    exact (preach_of_peq (c := ⟨x.st, i :: x.pend⟩) (d := ⟨x.st, x.pend ++ [i]⟩)
      ⟨rfl, (List.perm_append_singleton _ _).symm⟩).trans hyc

/-- An unknown read: nothing changes. -/
theorem post_errR (cs : List GCfg) (i : In) (hw : isWriteG i = false) :
    ppost casB (cfgSet cs) i .err = cfgSet cs := by
  funext c'
  apply propext
  constructor
  · rintro ⟨c0, c, c1, ⟨x, hx, h0⟩, h1, hst, h2⟩
    cases hst with
    | errW h _ => simp [casB, hw] at h
    | errR _ _ => exact ⟨x, hx, (h0.trans h1).trans h2⟩
  · rintro ⟨x, hx, hxc⟩
    exact ⟨x, x, x, ⟨x, hx, .refl _⟩, .refl _, .errR x i hw rfl, hxc⟩

/-- An answered operation: the configurations `knownCfgs` describes. -/
theorem post_ok (cs cs' : List GCfg) (i : In) (o : Out)
    (hcs' : ∀ y, y ∈ cs' ↔ knownCfgs cs i o y) :
    ppost casB (cfgSet cs) i (.ok o) = cfgSet cs' := by
  funext c'
  apply propext
  constructor
  · rintro ⟨c0, c, c1, ⟨x, hx, h0⟩, h1, hst, h2⟩
    cases hst with
    | ok _ =>
      obtain ⟨r, hr, hpe⟩ := areach_of_preach (h0.trans h1)
      refine ⟨⟨(applyG r.st i).1, r.pend⟩, (hcs' _).2 ⟨x, hx, r, hr, ?_, rfl⟩, ?_⟩
      · show applyG r.st i = ((applyG r.st i).1, (casB.step i c.st).2)
        show applyG r.st i = ((applyG r.st i).1, (applyG c.st i).2)
        rw [hpe.1]
      · refine (preach_of_peq (c := ⟨(applyG r.st i).1, r.pend⟩)
          (d := ⟨(casB.step i c.st).1, c.pend⟩) ⟨?_, hpe.2⟩).trans h2
        show (applyG r.st i).1 = (applyG c.st i).1
        rw [hpe.1]
    | obs _ h _ => exact (obs_false h).elim
  · rintro ⟨y, hy, hyc⟩
    obtain ⟨x, hx, r, hr, ha, hp⟩ := (hcs' y).1 hy
    refine ⟨x, r, y, ⟨x, hx, .refl _⟩, preach_of_areach hr, ?_, hyc⟩
    have hs := PStep.ok (P := casB) r i rfl
    rw [show casB.step i r.st = (y.st, o) from ha] at hs
    have : (⟨y.st, r.pend⟩ : GCfg) = y := by rw [← hp]
    rw [this] at hs
    exact hs

theorem cfgSet_nonempty {cs : List GCfg} : (∃ c, cfgSet cs c) ↔ cs ≠ [] := by
  constructor
  · rintro ⟨c, x, hx, -⟩ h
    simp [h] at hx
  · intro h
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil cs h
    exact ⟨x, x, hx, .refl _⟩

/-- **`step` (kit.go) is `pSeq casB`'s step** on the sets the model's lists stand for: an answer
`o` (`.err` when unknown); `cs'` the answered operation's next list (`knownCfgs`). -/
theorem stepG_pSeq (cs : List GCfg) (hne : cs ≠ []) (i : In) (o : Out) (cs' : List GCfg)
    (hcs' : ∀ y, y ∈ cs' ↔ knownCfgs cs i o y) :
    (pSeq casB).step (cfgSet cs) (i, if o.Unknown' then .err else .ok o) =
      if o.Unknown' then
        some (cfgSet (if isWriteG i then cs.map (fun x => ⟨x.st, x.pend ++ [i]⟩) else cs))
      else if cs' ≠ [] then some (cfgSet cs') else none := by
  by_cases hu : o.Unknown' = true
  · simp only [hu, ↓reduceIte]
    cases hw : isWriteG i
    · simp only [Bool.false_eq_true, ↓reduceIte]
      simp only [pSeq]
      rw [post_errR cs i hw, if_pos (cfgSet_nonempty.2 hne)]
    · simp only [↓reduceIte]
      simp only [pSeq]
      rw [post_errW cs i hw, if_pos (cfgSet_nonempty.2 (by simpa using hne))]
  · simp only [hu, Bool.false_eq_true, ↓reduceIte]
    simp only [pSeq]
    rw [post_ok cs cs' i o hcs']
    by_cases hc : cs' = []
    · rw [if_neg (fun h => (cfgSet_nonempty.1 h) hc)]; simp [hc]
    · rw [if_pos (cfgSet_nonempty.2 hc), if_pos hc]

/-- The initial list stands for the store's initial set. -/
theorem cfgSet_init : cfgSet [⟨W64 0, []⟩] = pInit casB := by
  funext c
  apply propext
  constructor
  · rintro ⟨x, hx, h⟩
    simp only [List.mem_singleton] at hx
    subst hx
    obtain ⟨r, hr, hpe⟩ := areach_of_preach h
    cases hr with
    | refl =>
      obtain ⟨h1, h2⟩ := hpe
      have h3 := List.nil_perm.1 h2
      show c = ⟨casB.init, []⟩
      obtain ⟨st, pend⟩ := c
      simp only at h1 h3
      subst h1 h3
      rfl
    | step k hk _ => simp at hk
  · intro h
    exact ⟨_, List.mem_singleton_self _, by rw [h]; exact .refl _⟩

end pure

end gryff.examples.gryffnet

end Perennial
