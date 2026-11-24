/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureT/Frame.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A2 (totality): the invariant's frame. `SI` and `MInv` are monotone in the bounds and in the
other replicas' steps (`Mono`); a global step whose replica step satisfies `Post` keeps `InvC`;
the initial configuration satisfies it.
-/
module

public import Dsverify.Proof.gryff.PureT.Inv

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure.tot

open model kahn

theorem Mono.refl (r : Fin 3) (s : RState) : Mono r s s where
  id := rfl
  used := fun _ h => h
  crt := Nat.le_refl _
  inst := fun _ _ c h => ⟨c, h, fun x => x, fun x => ⟨x, rfl⟩⟩
  wt := fun _ _ _ h => h

theorem Mono.trans {r : Fin 3} {s1 s2 s3 : RState} (h1 : Mono r s1 s2) (h2 : Mono r s2 s3) :
    Mono r s1 s3 where
  id := h2.id.trans h1.id
  used := fun p h => h2.used p (h1.used p h)
  crt := Nat.le_trans h1.crt h2.crt
  inst := by
    intro q i c h
    obtain ⟨c2, h2', a2, b2⟩ := h1.inst q i c h
    obtain ⟨c3, h3', a3, b3⟩ := h2.inst q i c2 h2'
    refine ⟨c3, h3', fun x => a3 (a2 x), fun x => ?_⟩
    obtain ⟨e1, e2⟩ := b2 x
    obtain ⟨e3, e4⟩ := b3 e1
    exact ⟨e3, e4.trans e2⟩
  wt := fun rid cid hu h => h2.wt rid cid (h1.used _ hu) (h1.wt rid cid hu h)

theorem InstB.mono {P P' : Fin 3 → Nat} (hP : ∀ q, P q ≤ P' q) {q i : w32} (h : InstB P q i) :
    InstB P' q i := by
  obtain ⟨q', h1, h2⟩ := h; exact ⟨q', h1, Nat.lt_of_lt_of_le h2 (hP q')⟩

theorem SI.mono {P P' : Fin 3 → Nat} {r : Fin 3} {s : RState} (h : SI P r s)
    (hP : ∀ q, P q ≤ P' q) : SI P' r s where
  id := h.id
  lcrt := h.lcrt
  lcut := h.lcut
  lconf := h.lconf
  nreq := h.nreq
  budget := h.budget
  crt := fun q => Nat.le_trans (h.crt q) (hP q)
  inst := fun q i c hc => ⟨(h.inst q i c hc).1.mono hP, (h.inst q i c hc).2⟩
  own := h.own
  ownOK := h.ownOK
  cut := h.cut
  conf := h.conf
  propQ := h.propQ
  usedPos := h.usedPos
  coord := h.coord

section
variable {st st' : Fin 3 → RState} (hM : ∀ k, Mono k (st k) (st' k))
include hM

theorem PropC.mono {L : Fin 3} {q i : w32} (h : PropC st L q i) : PropC st' L q i := by
  obtain ⟨c, hc, h1⟩ := h
  obtain ⟨c', hc', a, _⟩ := (hM L).inst q i c hc
  exact ⟨c', hc', a h1⟩

theorem ExecC.mono {x : Fin 3} {q i : w32} (h : ExecC st x q i) : ExecC st' x q i := by
  obtain ⟨c, hc, h1, h2⟩ := h
  obtain ⟨c', hc', _, b⟩ := (hM x).inst q i c hc
  obtain ⟨b1, b2⟩ := b h1
  exact ⟨c', hc', b1, b2 ▸ h2⟩

theorem WK.mono {q : Fin 3} {rid cid : w32} (h : WK st q rid cid) : WK st' q rid cid :=
  ⟨h.1, (hM q).used _ h.2.1, (hM q).wt rid cid h.2.1 h.2.2⟩

theorem FromL.mono {r : Fin 3} {l q i : w32} (h : FromL st r l q i) : FromL st' r l q i := by
  obtain ⟨L, h1, h2, h3⟩ := h; exact ⟨L, h1, h2, h3.mono hM⟩

theorem MInv.mono {P P' : Fin 3 → Nat} (hP : ∀ q, P q ≤ P' q) {r : Fin 3} {m : Msg}
    (h : MInv P st r m) : MInv P' st' r m := by
  cases m <;> simp only [MInv] at h ⊢
  case write2 m => obtain ⟨a, q, b, c⟩ := h; exact ⟨a, q, b, c.mono hM⟩
  case write2Reply m => exact h.mono hM
  case preAccept m => exact ⟨h.1.mono hM, h.2.1.mono hP, h.2.2⟩
  case preAcceptReply m => exact ⟨h.1.mono hP, h.2.mono hM⟩
  case preAcceptOK m => exact ⟨h.1.mono hP, h.2.mono hM⟩
  case accept m => exact ⟨h.1.mono hM, h.2.1.mono hP, h.2.2⟩
  case acceptReply m => exact ⟨h.1.mono hP, h.2.mono hM⟩
  case commit m => exact ⟨h.1.mono hP, h.2⟩
  case prepare m => exact ⟨h.1.mono hM, h.2.mono hP⟩
  case prepareReply m => exact ⟨h.1.mono hP, h.2.1.mono hM, h.2.2⟩
  case executed m =>
    obtain ⟨a, b, x, c⟩ := h; exact ⟨a, b.mono hP, x, c.mono hM⟩
  case executeOverwrite m => exact ⟨h.1.mono hP, h.2.mono hM⟩
  all_goals exact h

end

theorem upd_self (st : Fin 3 → RState) (r : Fin 3) (s' : RState) : upd st r s' r = s' := by
  simp [upd]

theorem upd_ne (st : Fin 3 → RState) {r j : Fin 3} (s' : RState) (h : j ≠ r) :
    upd st r s' j = st j := by
  simp [upd, h]

theorem mono_upd {st : Fin 3 → RState} {r : Fin 3} {s' : RState} (h : Mono r (st r) s') :
    ∀ k, Mono k (st k) (upd st r s' k) := by
  intro k
  by_cases hk : k = r
  · subst hk; rw [upd_self]; exact h
  · rw [upd_ne _ _ hk]; exact Mono.refl _ _

theorem Pf_upd_le {st : Fin 3 → RState} {r : Fin 3} {s' : RState} (h : Mono r (st r) s') :
    ∀ q, Pf st q ≤ Pf (upd st r s') q := by
  intro q
  by_cases hq : q = r
  · subst hq; simp only [Pf, upd_self]; exact h.crt
  · simp only [Pf, upd_ne _ _ hq]; exact Nat.le_refl _

/-! ## A global step keeps the invariant -/

theorem sentTo_mem {j : Fin 3} {o : List Out} {m : Msg} (h : m ∈ sentTo gNet j o) :
    Out.send j m ∈ o := by
  simp only [sentTo] at h
  obtain ⟨x, hx, hm⟩ := List.mem_filterMap.1 h
  match x with
  | .send d m' =>
    by_cases hd : d = j
    · subst hd; simp at hm; cases hm; exact hx
    · simp [hd] at hm
  | .ext _ => simp at hm

theorem invC_step {c c' : Cfg gNet} {r : Fin 3} {e : Ev} {x : List Ext} (hI : InvC c)
    (hs : GStep c r e c' x)
    (hpost : ∀ s' o, stepR r (c.st r) e = .ok (s', o) → Post c.st r (s', o)) : InvC c' := by
  obtain ⟨s', o, hst, _, _, hc1, hc2⟩ := hs
  have hst' : stepR r (c.st r) e = .ok (s', o) := by
    simp only [gNet, gStep, StepRes.toOption] at hst
    revert hst; cases stepR r (c.st r) e <;> simp [Except.toOption]
    all_goals (intro a b; subst a; subst b; rfl)
  obtain ⟨hM, hSI, hO⟩ := hpost s' o hst'
  have hcst : c'.st = upd c.st r s' := by
    rw [hc1]; rfl
  have hP := Pf_upd_le hM
  have hMk := mono_upd hM
  refine ⟨?_, ?_⟩
  · intro j
    rw [hcst]
    by_cases hj : j = r
    · subst hj; simpa [upd] using hSI
    · have : upd c.st r s' j = c.st j := upd_ne _ _ hj
      rw [this]; exact (hI.1 j).mono hP
  · intro j m hm
    rw [hcst]
    rw [hc2] at hm
    simp only at hm
    rcases List.mem_append.1 hm with hm | hm
    · have hold : m ∈ c.inflight j := by
        split at hm
        · cases hrecv : gNet.recv e with
          | none => rw [hrecv] at hm; exact hm
          | some m0 => rw [hrecv] at hm; exact List.mem_of_mem_erase hm
        · exact hm
      exact (hI.2 j m hold).mono hMk hP
    · exact hO _ (sentTo_mem hm)

/-! ## The initial configuration -/

theorem invC_init : InvC (Cfg.init gNet) := by
  refine ⟨?_, ?_⟩
  · intro r
    have hst : (Cfg.init gNet).st r = RState.init r.val := rfl
    rw [hst]
    have hid : (RState.init r.val).id = rid32 r := rfl
    have hcrt : ∀ q : Fin 3, (RState.init r.val).crt (rid32 q) = 0 := by
      intro q; show ([0, 0, 0] : List w32).getD (rid32 q).toNat 0 = 0
      rw [rid32_toNat]; rcases q with ⟨_|_|_|q, hq⟩ <;> first | rfl | omega
    have hcut : ∀ q : Fin 3, (RState.init r.val).cut (rid32 q) = -1 := by
      intro q; show ([-1, -1, -1, -1, -1] : List w32).getD (rid32 q).toNat 0 = -1
      rw [rid32_toNat]; rcases q with ⟨_|_|_|q, hq⟩ <;> first | rfl | omega
    exact {
      id := hid
      lcrt := rfl
      lcut := rfl
      lconf := rfl
      nreq := by simp [RState.init]
      budget := by rw [hcrt r]; simp [RState.init]
      crt := fun q => by rw [hcrt q]; simp
      inst := fun q i c h => by simp [RState.init] at h
      own := fun i h => by rw [hcrt r] at h; simp at h
      ownOK := fun i c h => by simp [RState.init] at h
      cut := fun q => Or.inl (hcut q)
      conf := fun q hi h => by
        have : ([none, none, none] : List (Option w32)).getD q.val none = none := by
          rcases q with ⟨_|_|_|q, hq⟩ <;> first | rfl | omega
        exact absurd (this.symm.trans h) (by simp)
      propQ := fun p h => by simp [RState.init] at h
      usedPos := fun p h => by simp [RState.init] at h
      coord := {
        oreq := fun k o h => by simp [RState.init, AMap.get?, List.lookup] at h
        wops := fun e h => by simp [RState.init] at h
        wopsN := fun e h => by simp [RState.init] at h
        rops := fun id rop h => by simp [RState.init, AMap.get?, List.lookup] at h } }
  · intro r m h; simp [Cfg.init] at h

end Perennial.gryff.pure.tot
