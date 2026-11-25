/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2/EpState.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2: the EPaxos handler's state, opened

`epaxosOwn` with its instance map named (`instsRep`), and the laws the handlers use to read,
update and create an instance (`insts_update`, `insts_insert`, `insts_congr`), to read and write a
row's pointer (`rows_ptr`, `rows_insert`), and the replica's heap's congruences.
-/
module

public import Dsverify.Proof.gryff.H2.Base

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB Proposal Msg Ev Out Cmd Deps)
open Perennial.gryff.replica (XS rowOwn nSlots)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]


/-- The instances of `epaxosOwn` (the pointer map `M`, each instance's copy). -/
def instsRep (ρ : Repl2Names) (xs : XS) (s : RState) (M : GMap replica.Node Loc) : IProp GF :=
  iprop([∗map] n ↦ p ∈ M, ∃ c, ⌜s.inst (BitVec.ofInt 32 n.1) (BitVec.ofInt 32 n.2) = some c⌝ ∗
    copyRep ρ xs n p c)

/-- The pure facts of `epaxosOwn`. -/
def epFacts (xs : XS) (s : RState) (isp : List GoSlice) (cfs : List Loc)
    (M : GMap replica.Node Loc) (cu : GoArray w32 5) (pm : GMap w64 src.gryffproto.ValTag) :
    Prop :=
  isp.length = 3 ∧ cfs.length = 3 ∧ s.crtInstance.length = 3 ∧ depsOf cu = s.committedUpTo ∧
    (∀ kk, kk ≠ W64 0 → pm.lookup kk = none) ∧ (pm.lookup (W64 0)).map vtOf = s.prevValTag ∧
    (∀ q i : w32, model.inBox q i = true →
      (s.inst q i).isSome = (M.lookup (sint.Z q, sint.Z i)).isSome) ∧
    (∀ q i : w32, model.inBox q i = false → s.inst q i = none) ∧
    (∀ n, (n ∈ xs.1 ∨ xs.numF n ≠ 0 ∨ xs.lowF n ≠ 0) → (M.lookup n).isSome) ∧
    (∀ n, (n ∈ xs.1 ∨ xs.numF n ≠ 0 ∨ xs.lowF n ≠ 0) → committedOrExecuted s n = true) ∧
    s.conf.length = 3 -- H2a-R2

theorem epaxosOwn_open (ρ : Repl2Names) (h r : Loc) (xs : XS) (s : RState) :
    epaxosOwn ρ h r xs s ⊣⊢
      ∃ (ispS crtS c1S : GoSlice) (isp : List GoSlice) (msR pvtR : Loc) (cfs : List Loc)
        (M : GMap replica.Node Loc) (cu : GoArray w32 5) (pm : GMap w64 src.gryffproto.ValTag),
      h.[src.gryff.EPaxosRMWHandler, go!"R"] ↦□ r ∗
      h.[src.gryff.EPaxosRMWHandler, go!"noConflicts"] ↦□ false ∗
      h.[src.gryff.EPaxosRMWHandler, go!"InstanceSpace"] ↦□ ispS ∗ ispS ↦*□ isp ∗
      h.[src.gryff.EPaxosRMWHandler, go!"crtInstance"] ↦□ crtS ∗
      h.[src.gryff.EPaxosRMWHandler, go!"conflicts1"] ↦□ c1S ∗ c1S ↦*□ cfs ∗
      h.[src.gryff.EPaxosRMWHandler, go!"maxSeqPerKey1"] ↦□ msR ∗
      h.[src.gryff.EPaxosRMWHandler, go!"PrevValTag"] ↦□ pvtR ∗
      h.[src.gryff.EPaxosRMWHandler, go!"CommittedUpTo"] ↦ cu ∗
      crtS ↦* s.crtInstance ∗
      ghostMapAuth ρ.ptrs 1 M ∗
      ([∗map] n ↦ p ∈ M, ghostMapElem ρ.ptrs n
        (if committedOrExecuted s n then DFrac.discard else DFrac.own 1) p) ∗
      ([∗list] q ↦ sq ∈ isp, rowOwn M q sq) ∗
      instsRep ρ xs s M ∗
      ([∗list] q ∈ List.finRange 3, monoNatAuthOwn (ρ.crt q) 1 (sint.Z (s.crt (rid32 q))).toNat) ∗
      ([∗list] q ↦ cr ∈ cfs, confRep cr (s.confAt q)) ∗ confRep msR s.maxSeqK0 ∗
      pvtR ↦$ pm ∗ epaxosRest h ∗
      ⌜epFacts xs s isp cfs M cu pm⌝ := by
  unfold epaxosOwn; exact .rfl

theorem copyRep_open (ρ : Repl2Names) (xs : XS) (n : replica.Node) (p : Loc) (c : Copy) :
    copyRep (GF := GF) ρ xs n p c ⊣⊢ ∃ iv : src.gryff.Instance, p ↦ iv ∗ cmdsRep iv.Cmds' c.cmds ∗
      lbRep ρ iv.lb' c.lb ∗
      ⌜iv.ballot' = c.ballot ∧ iv.Status' = c.status ∧ iv.Seq' = c.seq ∧
        depsOf iv.Deps' = c.deps ∧ vtOf iv.Base' = c.base ∧ iv.Slot' = c.slot ∧
        iv.Leader' = c.leader ∧ iv.vbal' = c.vbal ∧
        sint.Z iv.Leader' = n.1 ∧ sint.Z iv.Slot' = n.2 ∧
        sint.Z iv.Index' = xs.numF n ∧ sint.Z iv.Lowlink' = xs.lowF n ∧
        (c.status = model.St.EXECUTED ↔ n ∈ xs.1)⌝ := by
  unfold copyRep; exact .rfl

/-- A copy's node is a pair of `int32`s. -/
theorem copyRep_node (ρ : Repl2Names) (xs : XS) (n : replica.Node) (p : Loc) (c : Copy) :
    copyRep (GF := GF) ρ xs n p c ⊢ ⌜n = (sint.Z (BitVec.ofInt 32 n.1), sint.Z (BitVec.ofInt 32 n.2))⌝ := by
  iintro H
  icases (copyRep_open ..).1 $$ H with ⟨%iv, -, -, -, %Hf⟩
  ipureintro
  obtain ⟨-, -, -, -, -, -, -, -, h1, h2, -⟩ := Hf
  refine Prod.ext ?_ ?_ <;> simp only [← h1, ← h2, BitVec.ofInt_toInt]

/-- The nodes of two `int32` pairs are equal iff the pairs are. -/
theorem node_eq_iff (q i q' i' : w32) :
    ((sint.Z q', sint.Z i') : replica.Node) = (sint.Z q, sint.Z i) ↔ q' = q ∧ i' = i := by
  constructor
  · intro h
    simp only [Prod.mk.injEq] at h
    exact ⟨BitVec.eq_of_toInt_eq h.1, BitVec.eq_of_toInt_eq h.2⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- **Update an instance**: its copy out, back at a new state that changes only it. -/
theorem insts_update (ρ : Repl2Names) (xs : XS) (s : RState) (M : GMap replica.Node Loc)
    (q i : w32) (p : Loc) (c : Copy) (hM : M.lookup (sint.Z q, sint.Z i) = some p)
    (hs : s.inst q i = some c) :
    instsRep (GF := GF) ρ xs s M ⊢ copyRep ρ xs (sint.Z q, sint.Z i) p c ∗
      ∀ (s' : RState) (c' : Copy), ⌜s'.inst q i = some c' ∧
          ∀ q' i', ¬(q' = q ∧ i' = i) → s'.inst q' i' = s.inst q' i'⌝ -∗
        copyRep ρ xs (sint.Z q, sint.Z i) p c' -∗ instsRep ρ xs s' M := by
  unfold instsRep
  iintro H
  icases (BigSepM.bigSepM_delete (show get? M (sint.Z q, sint.Z i) = some p from hM)).1 $$ H
    with ⟨⟨%c0, %Hc0, Hp⟩, Hrest⟩
  simp only [BitVec.ofInt_toInt, hs, Option.some.injEq] at Hc0
  subst Hc0
  iframe Hp
  iintro %s' %c' %Hs' Hp'
  iapply (BigSepM.bigSepM_delete (show get? M (sint.Z q, sint.Z i) = some p from hM)).2
  isplitl [Hp']
  · iexists c'
    iframe Hp'
    ipureintro
    simp only [BitVec.ofInt_toInt]; exact Hs'.1
  iapply BigSepM.bigSepM_mono (fun {n p'} hnp => ?_) $$ Hrest
  have hne : n ≠ (sint.Z q, sint.Z i) := by
    intro e; subst e
    rw [LawfulPartialMap.get?_delete_eq rfl] at hnp; cases hnp
  iintro ⟨%c1, %Hc1, Hp1⟩
  ihave %Hn := copyRep_node ρ xs n p' c1 $$ Hp1
  iexists c1
  iframe Hp1
  ipureintro
  rw [Hs'.2]
  · exact Hc1
  · rintro ⟨h1, h2⟩
    apply hne
    rw [Hn, h1, h2]

/-- **Create an instance** at a node `M` does not have. -/
theorem insts_insert (ρ : Repl2Names) (xs : XS) (s s' : RState) (M : GMap replica.Node Loc)
    (q i : w32) (p : Loc) (c' : Copy) (hM : M.lookup (sint.Z q, sint.Z i) = none)
    (hs' : s'.inst q i = some c')
    (hoth : ∀ q' i', ¬(q' = q ∧ i' = i) → s'.inst q' i' = s.inst q' i') :
    instsRep (GF := GF) ρ xs s M ∗ copyRep ρ xs (sint.Z q, sint.Z i) p c' ⊢
      instsRep ρ xs s' (GMap.insert (sint.Z q, sint.Z i) p M) := by
  unfold instsRep
  iintro ⟨H, Hp⟩
  iapply (BigSepM.bigSepM_insert (show get? M (sint.Z q, sint.Z i) = none from hM)).2
  isplitl [Hp]
  · iexists c'
    iframe Hp
    ipureintro
    simp only [BitVec.ofInt_toInt]; exact hs'
  iapply BigSepM.bigSepM_mono (fun {n p'} hnp => ?_) $$ H
  have hne : n ≠ (sint.Z q, sint.Z i) := by
    intro e; subst e
    rw [show get? M (sint.Z q, sint.Z i) = none from hM] at hnp; cases hnp
  iintro ⟨%c1, %Hc1, Hp1⟩
  ihave %Hn := copyRep_node ρ xs n p' c1 $$ Hp1
  iexists c1
  iframe Hp1
  ipureintro
  rw [hoth]
  · exact Hc1
  · rintro ⟨h1, h2⟩
    apply hne
    rw [Hn, h1, h2]

/-- The instances depend on the state's instances only. -/
theorem insts_congr (ρ : Repl2Names) (xs : XS) (s s' : RState) (M : GMap replica.Node Loc)
    (h : s'.inst = s.inst) : instsRep (GF := GF) ρ xs s M ⊢ instsRep ρ xs s' M := by
  unfold instsRep
  rw [h]

/-- A row depends on its own nodes only. -/
theorem rowOwn_congr (M M' : GMap replica.Node Loc) (k : Nat) (sq : GoSlice)
    (h : ∀ j : Nat, M'.lookup ((k : Int), (j : Int)) = M.lookup ((k : Int), (j : Int))) :
    (rowOwn M k sq : IProp GF) ⊢ rowOwn M' k sq := by
  iintro H
  icases (replica.rowOwn_open ..).1 $$ H with ⟨%ptrs, Hs, %Hf⟩
  iapply (replica.rowOwn_open ..).2
  iexists ptrs
  iframe Hs
  ipureintro
  refine ⟨Hf.1, fun j p hp => ?_⟩
  rw [h]; exact Hf.2 j p hp

/-- Row `q` out of the rows, back at a pointer map that changes only row `q`. -/
theorem rows_acc' (M : GMap replica.Node Loc) (isp : List GoSlice) (q : Nat) (sq : GoSlice)
    (h : isp[q]? = some sq) :
    ([∗list] k ↦ s ∈ isp, (rowOwn M k s : IProp GF)) ⊢
      rowOwn M q sq ∗ ∀ M' : GMap replica.Node Loc,
        ⌜∀ k j : Nat, k ≠ q → M'.lookup ((k : Int), (j : Int)) = M.lookup ((k : Int), (j : Int))⌝ -∗
        rowOwn M' q sq -∗ [∗list] k ↦ s ∈ isp, rowOwn M' k s := by
  iintro H
  icases (BigSepL.bigSepL_delete h).1 $$ H with ⟨Hq, Hrest⟩
  iframe Hq
  iintro %M' %Hag Hq'
  iapply (BigSepL.bigSepL_delete h).2
  iframe Hq'
  iapply BigSepL.bigSepL_mono (fun {k x} _ => ?_) $$ Hrest
  iintro Hk %hk
  ihave Hk := Hk $$ %hk
  iapply rowOwn_congr M M' k x (fun j => Hag k j hk) $$ Hk

/-- A row with a new pointer at an empty slot. -/
theorem rowOwn_insert (M : GMap replica.Node Loc) (q i : Nat) (sq : GoSlice) (ptrs : List Loc)
    (p : Loc) (hp : p ≠ Loc.null) (hlen : ptrs.length = nSlots)
    (hf : ∀ (j : Nat) (p' : Loc), ptrs[j]? = some p' →
      M.lookup ((q : Int), (j : Int)) = (if p' = Loc.null then none else some p')) :
    sq ↦* ptrs.set i p ⊢ (rowOwn (GMap.insert ((q : Int), (i : Int)) p M) q sq : IProp GF) := by
  iintro Hs
  iapply (replica.rowOwn_open ..).2
  iexists _
  iframe Hs
  ipureintro
  refine ⟨by rw [List.length_set, hlen], fun j p' hp' => ?_⟩
  by_cases hji : j = i
  · subst hji
    have hj : j < ptrs.length := by
      have := (List.getElem?_eq_some_iff.1 hp').1
      rwa [List.length_set] at this
    rw [List.getElem?_set_self hj] at hp'
    cases hp'
    rw [GMap.lookup_insert, ite_eq_right_iff.2 (fun h => absurd h hp)]
  · rw [List.getElem?_set_ne (Ne.symm hji)] at hp'
    rw [GMap.lookup_insert_ne _ _ (by intro e; simp only [Prod.mk.injEq] at e; omega)]
    exact hf j p' hp'

/-- `crtInstance[q] = x` (`x` at least the old value): the lower bounds' authorities move. -/
theorem crt_monos_update (ρ : Repl2Names) (s : RState) (q x : w32)
    (hle : (sint.Z (s.crt q)).toNat ≤ (sint.Z x).toNat) :
    ([∗list] q' ∈ List.finRange 3,
        (monoNatAuthOwn (ρ.crt q') 1 (sint.Z (s.crt (rid32 q'))).toNat : IProp GF)) ⊢
      |==> [∗list] q' ∈ List.finRange 3,
        monoNatAuthOwn (ρ.crt q') 1 (sint.Z ((s.setCrt q x).crt (rid32 q'))).toNat := by
  have hmono : ∀ q' : w32, (sint.Z (s.crt q')).toNat ≤ (sint.Z ((s.setCrt q x).crt q')).toNat := by
    intro q'
    by_cases h : q' = q
    · subst h
      by_cases hl : q'.toNat < s.crtInstance.length
      · simp only [RState.crt, RState.setCrt, List.getD_eq_getElem?_getD, List.getElem?_set_self hl,
          Option.getD_some]
        simpa [RState.crt, List.getD_eq_getElem?_getD] using hle
      · simp only [RState.crt, RState.setCrt, List.set_eq_of_length_le (by omega : s.crtInstance.length ≤ q'.toNat)]
        exact Nat.le_refl _
    · have : q'.toNat ≠ q.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
      simp only [RState.crt, RState.setCrt, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm this)]
      exact Nat.le_refl _
  have hfin : List.finRange 3 = [0, 1, 2] := by decide
  rw [hfin]
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H0, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H2, -⟩
  imod (mono_nat_own_update _ (hmono (rid32 0))) $$ H0 with ⟨H0, -⟩
  imod (mono_nat_own_update _ (hmono (rid32 1))) $$ H1 with ⟨H1, -⟩
  imod (mono_nat_own_update _ (hmono (rid32 2))) $$ H2 with ⟨H2, -⟩
  imodintro
  iapply BigSepL.bigSepL_cons.2; iframe H0
  iapply BigSepL.bigSepL_cons.2; iframe H1
  iapply BigSepL.bigSepL_cons.2; iframe H2
  iapply BigSepL.bigSepL_nil.2
  itrivial

/-- `maxSeq` out of `epaxosRest` (any new value back). -/
theorem epaxosRest_maxSeq (h : Loc) :
    epaxosRest (GF := GF) h ⊢ ∃ ms : w32, h.[src.gryff.EPaxosRMWHandler, go!"maxSeq"] ↦ ms ∗
      (∀ ms' : w32, h.[src.gryff.EPaxosRMWHandler, go!"maxSeq"] ↦ ms' -∗ epaxosRest h) := by
  unfold epaxosRest
  iintro ⟨%ms, %lcp, %lci, %cS, %cs, %mskR, %msk, Hms, Hrest⟩
  iexists ms
  iframe Hms
  iintro %ms' Hms'
  iexists ms', lcp, lci, cS, cs, mskR, msk
  iframe

end

end Perennial.gryff.replica2
