/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/X/Facts.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit X: what the EPaxos handler's heap says about the model state

`epaxosOwnG_ok`: the executed instances are the search state's (`xs.1`), and the copies' leader
and slot are their nodes'. `instsG_*`: taking one instance out and putting it back after a
change of the search state or of the instance.
-/
module

public import Dsverify.Proof.gryff.X.Laws

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.X

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open Perennial.gryff.model (RState Copy Msg Ev Out committedCopy executedB inBox)
open Perennial.gryff.replica (XS Node stackOwn euOwn)
open Perennial.gryff.replica2 (Repl2Names)

/-- What the heap says about the model state and the search state. -/
def HeapOk (xs : XS) (s : RState) : Prop :=
  (∀ n, executedB s n = true ↔ n ∈ xs.1) ∧ LeaderOk s

theorem sint_ofInt_of {z : Int} (h0 : -2 ^ 31 ≤ z) (h1 : z < 2 ^ 31) :
    sint.Z (BitVec.ofInt 32 z) = z := by
  simp only [sint.Z]; rw [BitVec.toInt_ofInt]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A copy's per-node facts. -/
def NodeOk (xs : XS) (s : RState) (n : Node) : Prop :=
  ∃ c, s.inst (BitVec.ofInt 32 n.1) (BitVec.ofInt 32 n.2) = some c ∧
    (c.status = model.St.EXECUTED ↔ n ∈ xs.1) ∧ sint.Z c.leader = n.1 ∧ sint.Z c.slot = n.2

theorem HeapOk_of (xs : XS) (s : RState) (M : GMap Node Loc)
    (hM : ∀ n p, M.lookup n = some p → NodeOk xs s n)
    (hbox : ∀ q i : w32, inBox q i = true →
        (s.inst q i).isSome = (M.lookup (sint.Z q, sint.Z i)).isSome)
    (hout : ∀ q i : w32, inBox q i = false → s.inst q i = none)
    (hX : ∀ n, (n ∈ xs.1 ∨ xs.numF n ≠ 0 ∨ xs.lowF n ≠ 0) → (M.lookup n).isSome) :
    HeapOk xs s := by
  -- a node of a committed copy is in `M`
  have hcM : ∀ n c, committedCopy s n = some c → ∃ p, M.lookup n = some p := by
    intro n c hc
    have hb := committedCopy_box (show (committedCopy s n).isSome by rw [hc]; rfl)
    have hi := (committedCopy_inst hc).1
    obtain ⟨h0, h1, h2, h3⟩ := hb
    have e1 : sint.Z (BitVec.ofInt 32 n.1) = n.1 := sint_ofInt_of (by omega) (by omega)
    have e2 : sint.Z (BitVec.ofInt 32 n.2) = n.2 := sint_ofInt_of (by omega) (by omega)
    have hib : inBox (BitVec.ofInt 32 n.1) (BitVec.ofInt 32 n.2) = true := by
      simp only [inBox, e1, e2, model.SLOTS, decide_eq_true_eq]; omega
    have := hbox _ _ hib
    rw [hi, e1, e2] at this
    exact Option.isSome_iff_exists.1 this.symm
  refine ⟨fun n => ⟨fun he => ?_, fun hn => ?_⟩, fun n c hc => ?_⟩
  · unfold executedB at he
    split at he
    · rename_i c hc
      obtain ⟨p, hp⟩ := hcM n c hc
      obtain ⟨c', hc', hst, -⟩ := hM n p hp
      rw [(committedCopy_inst hc).1] at hc'; cases hc'
      exact hst.1 (by simpa using he)
    · simp at he
  · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 (hX n (.inl hn))
    obtain ⟨c, hc, hst, hl, hs⟩ := hM n p hp
    have hib : inBox (BitVec.ofInt 32 n.1) (BitVec.ofInt 32 n.2) = true := by
      cases hb : inBox (BitVec.ofInt 32 n.1) (BitVec.ofInt 32 n.2)
      · rw [hout _ _ hb] at hc; cases hc
      · rfl
    have hl' := c.leader.toInt_lt; have hl'' := c.leader.le_toInt
    have hs' := c.slot.toInt_lt; have hs'' := c.slot.le_toInt
    have e1 : sint.Z (BitVec.ofInt 32 n.1) = n.1 := sint_ofInt_of (by simp [sint.Z] at hl; omega)
      (by simp [sint.Z] at hl; omega)
    have e2 : sint.Z (BitVec.ofInt 32 n.2) = n.2 := sint_ofInt_of (by simp [sint.Z] at hs; omega)
      (by simp [sint.Z] at hs; omega)
    simp only [inBox, e1, e2, decide_eq_true_eq] at hib
    have hcc : committedCopy s n = some c := by
      unfold committedCopy
      rw [if_pos hib, hc]
      simp only [hst.2 hn, or_true, ite_true]
    simp only [executedB, hcc, hst.2 hn, beq_self_eq_true]
  · obtain ⟨p, hp⟩ := hcM n c hc
    obtain ⟨c', hc', -, hl, hs⟩ := hM n p hp
    rw [(committedCopy_inst hc).1] at hc'; cases hc'
    exact ⟨hl, hs⟩

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [π : NetProtoGS] [sem : go.Semantics]

/-- The facts of each element of a big separating conjunction. -/
theorem bigSepM_facts {V : Type} {Φ : Node → V → IProp GF} {m : GMap Node V}
    {ψ : Node → V → Prop} (h : ∀ n v, Φ n v ⊢ ⌜ψ n v⌝) :
    ([∗map] n ↦ v ∈ m, Φ n v) ⊢
      ([∗map] n ↦ v ∈ m, Φ n v) ∗ ⌜∀ n v, m.lookup n = some v → ψ n v⌝ := by
  have h1 : ([∗map] n ↦ v ∈ m, Φ n v) ⊢ [∗map] n ↦ v ∈ m, iprop(Φ n v ∗ ⌜ψ n v⌝) :=
    BigSepM.bigSepM_mono fun {n v} _ => by
      iintro H
      ihave %hp := h n v $$ H
      iframe; ipureintro; exact hp
  refine h1.trans ?_
  rw [BigSepM.bigSepM_sep_eq]
  refine sep_mono .rfl ?_
  refine BigSepM.bigSepM_pure_intro.trans (pure_mono fun hall n v hv => hall n v hv)

theorem copyRepG_ok (ρ : Repl2Names) (xs : XS) (s : RState) (n : Node) (p : Loc) :
    (∃ c, ⌜s.inst (BitVec.ofInt 32 n.1) (BitVec.ofInt 32 n.2) = some c⌝ ∗ copyRepG (GF := GF) ρ xs n p c)
      ⊢ ⌜NodeOk xs s n⌝ := by
  iintro ⟨%c, %hc, Hc⟩
  icases (copyRepG_open ..).1 $$ Hc with ⟨%iv, -, -, -, %Hf⟩
  ipureintro
  obtain ⟨-, -, -, -, -, hsl, hld, -, hl, hs, -, -, hx⟩ := Hf
  exact ⟨c, hc, hx, by rw [← hld]; exact hl, by rw [← hsl]; exact hs⟩

theorem epaxosOwnG_ok (ρ : Repl2Names) (h r : Loc) (xs : XS) (s : RState) :
    epaxosOwnG (GF := GF) ρ h r xs s ⊢ epaxosOwnG ρ h r xs s ∗ ⌜HeapOk xs s⌝ := by
  iintro H
  unfold epaxosOwnG
  icases H with ⟨%ispS, %crtS, %c1S, %isp, %msR, %pvtR, %cfs, %M, %cu, %pm, H1, H2, H3, H4, H5,
    H6, H7, H8, H9, H10, H11, H12, H13, H14, Hi, H16, H17, H18, H19, H20, %Hf⟩
  unfold instsG
  ihave ⟨Hi, %HM⟩ := bigSepM_facts (copyRepG_ok (GF := GF) ρ xs s) $$ Hi
  isplitl
  · iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm
    iframe; ipureintro; exact Hf
  ipureintro
  obtain ⟨-, -, -, -, -, -, hbox, hout, hX, -⟩ := Hf
  exact HeapOk_of xs s M HM hbox hout hX

theorem epaxosOwnG_open (ρ : Repl2Names) (h r : Loc) (xs : XS) (s : RState) :
    epaxosOwnG (GF := GF) ρ h r xs s ⊣⊢
    ∃ (ispS crtS c1S : GoSlice) (isp : List GoSlice) (msR pvtR : Loc) (cfs : List Loc)
      (M : GMap Node Loc) (cu : GoArray w32 5) (pm : GMap w64 src.gryffproto.ValTag),
    h.[src.gryff.EPaxosRMWHandler, go!"R"] ↦□ r ∗
    h.[src.gryff.EPaxosRMWHandler, go!"noConflicts"] ↦□ false ∗
    h.[src.gryff.EPaxosRMWHandler, go!"InstanceSpace"] ↦□ ispS ∗ ispS ↦*□ isp ∗
    h.[src.gryff.EPaxosRMWHandler, go!"crtInstance"] ↦□ crtS ∗
    h.[src.gryff.EPaxosRMWHandler, go!"conflicts1"] ↦□ c1S ∗ c1S ↦*□ cfs ∗
    h.[src.gryff.EPaxosRMWHandler, go!"maxSeqPerKey1"] ↦□ msR ∗
    h.[src.gryff.EPaxosRMWHandler, go!"PrevValTag"] ↦□ pvtR ∗
    h.[src.gryff.EPaxosRMWHandler, go!"CommittedUpTo"] ↦ cu ∗
    crtS ↦* s.crtInstance ∗
    ghostMapAuth ρ.ptrs 1 M ∗ ptrElems ρ s M ∗
    ([∗list] q ↦ sq ∈ isp, replica.rowOwn M q sq) ∗ instsG ρ xs s M ∗
    ([∗list] q ∈ List.finRange 3,
      monoNatAuthOwn (ρ.crt q) 1 (sint.Z (s.crt (replica2.rid32 q))).toNat) ∗
    ([∗list] q ↦ cr ∈ cfs, confRepG cr (s.confAt q)) ∗ confRepG msR s.maxSeqK0 ∗
    pvtR ↦$ pm ∗ epaxosRestG h ∗ ⌜epFacts xs s isp cfs M cu pm⌝ := by
  unfold epaxosOwnG; exact .rfl

theorem copyRepG_congr (ρ : Repl2Names) (xs xs' : XS) (n : Node) (p : Loc) (c : Copy)
    (h1 : xs'.numF n = xs.numF n) (h2 : xs'.lowF n = xs.lowF n) (h3 : n ∈ xs'.1 ↔ n ∈ xs.1) :
    copyRepG (GF := GF) ρ xs n p c ⊢ copyRepG ρ xs' n p c := by
  iintro H
  icases (copyRepG_open ..).1 $$ H with ⟨%iv, Hp, Hc, Hl, %Hf⟩
  iapply (copyRepG_open ..).2
  iexists iv; iframe
  ipureintro
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := Hf
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, by rw [h1]; exact a11, by rw [h2]; exact a12,
    by rw [h3]; exact a13⟩

/-- One instance of the instance space, and putting it back after changing the search state and
the model state elsewhere than at it. -/
theorem instsG_upd (ρ : Repl2Names) (xs : XS) (s : RState) (M : GMap Node Loc) (n : Node)
    (p : Loc) (hp : M.lookup n = some p) :
    instsG (GF := GF) ρ xs s M ⊢
      (∃ c, ⌜s.inst (BitVec.ofInt 32 n.1) (BitVec.ofInt 32 n.2) = some c⌝ ∗ copyRepG ρ xs n p c) ∗
      ∀ (xs' : XS) (s' : RState),
        ⌜∀ n', n' ≠ n → xs'.numF n' = xs.numF n' ∧ xs'.lowF n' = xs.lowF n' ∧
          (n' ∈ xs'.1 ↔ n' ∈ xs.1)⌝ -∗
        ⌜∀ n', n' ≠ n → NodeOk xs s n' →
          s'.inst (BitVec.ofInt 32 n'.1) (BitVec.ofInt 32 n'.2) =
            s.inst (BitVec.ofInt 32 n'.1) (BitVec.ofInt 32 n'.2)⌝ -∗
        (∃ c, ⌜s'.inst (BitVec.ofInt 32 n.1) (BitVec.ofInt 32 n.2) = some c⌝ ∗
          copyRepG ρ xs' n p c) -∗
        instsG ρ xs' s' M := by
  iintro H
  unfold instsG
  icases (BigSepM.bigSepM_delete (show get? M n = some p from hp)).1 $$ H with ⟨Hn, Hrest⟩
  iframe Hn
  iintro %xs' %s' %Hx %Hs Hn
  iapply (BigSepM.bigSepM_delete (show get? M n = some p from hp)).2
  iframe Hn
  iapply BigSepM.bigSepM_mono (fun {n' p'} hnp => ?_) $$ Hrest
  have hne : n' ≠ n := by
    intro e; subst e
    rw [LawfulPartialMap.get?_delete_eq rfl] at hnp; cases hnp
  iintro ⟨%c, %hc, Hc⟩
  ihave %Hok := copyRepG_ok ρ xs s n' p' $$ [Hc]
  · iexists c; iframe; ipureintro; exact hc
  obtain ⟨a1, a2, a3⟩ := Hx n' hne
  iexists c
  isplitr
  · ipureintro; rw [Hs n' hne Hok]; exact hc
  iapply copyRepG_congr ρ xs xs' n' p' c a1 a2 a3 $$ Hc

theorem execPrivG_open (ρ : Repl2Names) (h : Loc) (xs : XS) (S : List Node) :
    execPrivG (GF := GF) ρ h xs S ⊣⊢ ghostVar ρ.xs (1 : Qp).half xs ∗ stackOwn ρ.toR1 S ∗
      ∃ euS : GoSlice, h.[src.gryff.EPaxosRMWHandler, go!"ExecedUpTo"] ↦□ euS ∗
        euOwn euS xs.1 := by
  unfold execPrivG; exact .rfl

/-- The pointer of a committed or executed instance is persistent. -/
theorem ptrElems_committed (ρ : Repl2Names) (s : RState) (M : GMap Node Loc) (n : Node) (p : Loc)
    (hp : M.lookup n = some p) (hc : replica2.committedOrExecuted s n = true) :
    ptrElems (GF := GF) ρ s M ⊢ ptrElems ρ s M ∗ ghostMapElem ρ.ptrs n DFrac.discard p := by
  iintro H
  unfold ptrElems
  icases (BigSepM.bigSepM_lookup_acc (show get? M n = some p from hp)).1 $$ H with ⟨Hn, Hclose⟩
  rw [hc]
  simp only [ite_true]
  icases Hn with #Hn
  ihave H := Hclose $$ Hn
  iframe; iframe #

/-- A leader's bookkeeping with its execution and blocking times set. -/
def lbTimes (g : src.gryff.LeaderBookkeeping) (et bt : time.Time) : src.gryff.LeaderBookkeeping :=
  { g with executedTime' := et, blockStartTime' := bt }

/-- A leader's bookkeeping, nil or its struct (whose times hold any value). -/
theorem lbRepG_open_time (ρ : Repl2Names) (l : Loc) (lb : Option model.LB) :
    lbRepG (GF := GF) ρ l lb ⊢ (⌜l = Loc.null⌝ ∗ lbRepG ρ l lb) ∨
      ∃ g : src.gryff.LeaderBookkeeping, l ↦ g ∗
        (∀ et : time.Time, ∀ bt : time.Time, l ↦ lbTimes g et bt -∗ lbRepG ρ l lb) := by
  cases lb with
  | none =>
    unfold lbRepG
    iintro %H; ileft; ipureintro; exact ⟨H, H⟩
  | some b =>
    unfold lbRepG
    iintro ⟨%g, Hl, Hp, Hc, Hri, %Hf⟩
    iright
    iexists g; iframe Hl
    iintro %et %bt Hl
    iexists lbTimes g et bt; iframe; ipureintro; exact Hf

theorem ptrElems_congr (ρ : Repl2Names) (s s' : RState) (M : GMap Node Loc)
    (h : ∀ n, (committedCopy s' n).isSome = (committedCopy s n).isSome) :
    ptrElems (GF := GF) ρ s M ⊢ ptrElems ρ s' M := by
  unfold ptrElems replica2.committedOrExecuted
  simp only [h]
  exact .rfl

theorem cmdsRepG_open (sl : GoSlice) (cs : List model.Cmd) :
    cmdsRepG (GF := GF) sl cs ⊣⊢ ∃ gs : List src.state.Command, sl ↦*□ gs ∗
      ⌜gs.map replica2.cmdOf = cs ∧ model.cmdsOk cs⌝ := .rfl

theorem bagAtG_open {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V]
    {t : go.GoType} [IntoValTyped (GF := GF) V t] (ρ : Repl2Names) (T : Type) (l : Loc)
    (f : GoString) (nm : String) (P : V → IProp GF) :
    bagAtG (t := t) ρ T l f nm P ⊣⊢ ∃ ch : Loc, l.[T, f] ↦□ ch ∗ isChanBag (ρ.chans nm) ch P :=
  .rfl

theorem eoChanPG_open (Tok : Msg → IProp GF) (p : Loc) :
    eoChanPG Tok p ⊣⊢ ∃ m, (∃ (eo : src.gryff.ExecuteOverwrite) (t : src.gryffproto.Tag),
      p ↦ eo ∗ eo.T' ↦□ t ∗ ⌜eo.K' = W64 0 ∧ m = ⟨eo.V', replica2.tagOf t, eo.Leader', eo.Slot'⟩⌝) ∗
      Tok (.executeOverwrite m) := .rfl

theorem instsG_ok (ρ : Repl2Names) (xs : XS) (s : RState) (M : GMap Node Loc) :
    instsG (GF := GF) ρ xs s M ⊢ instsG ρ xs s M ∗ ⌜∀ n p, M.lookup n = some p → NodeOk xs s n⌝ := by
  unfold instsG
  exact bigSepM_facts (copyRepG_ok (GF := GF) ρ xs s)

end

end Perennial.gryff.X
