/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/CoordSC.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1b: the coordinator's `ShortCircuit` (the riskiest coordinator step: the sort, the reads
loop over the sorted `ShortReads`, the empty `ShortWrites` loop).

The helpers of `H1/CoordSC.lean` (its definitions and lemmas, everything before its method
proofs), apart so that other modules import them without the proofs (CLAUDE.md, "Import tiers").
-/

module

public import Dsverify.Proof.gryff.H1.CoordStartDefs
public import Dsverify.Proof.gryff.H1.Sort
public import Dsverify.Proof.gryff.H1.PureSC
public import Dsverify.GeneratedProof.gryff.examples.gryffnet
public import Dsverify.Proof.gryff.Lib.SortHyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB RecoveryInstance Proposal ReadOp WriteOp OngoingOp
  Msg Ev Ext Out Cmd Deps AMap StepRes)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF]
variable [sortA : SortSliceHyp GF]
variable [strconvA : strconv.Assumptions] -- N-5


theorem val_false_ne_true : ((#false : val) = #true) = False :=
  propext ⟨fun h => absurd (GoGlobalContext.intoVal_inj_bool h) (by decide), False.elim⟩

theorem gmap_delete_comm {K V : Type} [DecidableEq K] (m : GMap K V) (a b : K) :
    GMap.delete a (GMap.delete b m) = GMap.delete b (GMap.delete a m) := by
  apply GMap.ext; intro j
  change (GMap.delete a (GMap.delete b m)) !! j = (GMap.delete b (GMap.delete a m)) !! j
  simp only [GMap.lookup_delete_iff]
  split <;> split <;> simp_all

theorem gmap_delete_idem {K V : Type} [DecidableEq K] (m : GMap K V) (a : K) :
    GMap.delete a (GMap.delete a m) = GMap.delete a m := by
  apply GMap.ext; intro j
  change (GMap.delete a (GMap.delete a m)) !! j = (GMap.delete a m) !! j
  simp only [GMap.lookup_delete_iff]
  split <;> simp_all

/-- `OngoingReqs[k]`'s struct during `ShortCircuit`'s reads loop: entry `n`'s struct is held apart
(its `ShortReads` slice is the loop's range). Read it, and put it back unchanged or deleted. -/
theorem orAcc (am : AMap 32 OngoingOp) (m : GMap w32 Loc) (n kk : w32) (pn p : Loc)
    (gn : src.gryffcommon.OngoingOp) (hp : m !! kk = some p) (hn : m !! n = none ∨ m !! n = some pn)
    (hnv : ∀ x, am.get? n = some x → x.requestId = gn.RequestId' ∧ x.clientId = gn.ClientId')
    (hdom : ∀ j, (m !! j).isSome = (am.get? j).isSome) :
    amapEnts (GF := GF) am (GMap.delete n m) ongoingOpRep ∗ pn ↦ gn ⊢
      ∃ (o : OngoingOp) (g : src.gryffcommon.OngoingOp),
        ⌜am.get? kk = some o ∧ g.RequestId' = o.requestId ∧ g.ClientId' = o.clientId⌝ ∗ p ↦ g ∗
        ((p ↦ g -∗ amapEnts am (GMap.delete n m) ongoingOpRep ∗ pn ↦ gn) ∧
         (p ↦ g -∗ amapEnts (am.del kk) (GMap.delete n (GMap.delete kk m)) ongoingOpRep ∗
           pn ↦ gn)) := by
  by_cases hk : kk = n
  · subst hk
    have hpe : p = pn := by
      rcases hn with h | h <;> rw [h] at hp <;> cases hp; rfl
    subst hpe
    obtain ⟨o, ho⟩ : ∃ o, am.get? kk = some o := by
      have := hdom kk; rw [hp] at this
      cases h : am.get? kk with
      | none => rw [h] at this; cases this
      | some o => exact ⟨o, rfl⟩
    obtain ⟨h1, h2⟩ := hnv o ho
    iintro ⟨Hents, Hpn⟩
    iexists o, gn
    iframe Hpn
    isplitl []
    · ipureintro; exact ⟨ho, h1.symm, h2.symm⟩
    isplit
    · iintro Hpn; iframe Hents Hpn
    · iintro Hpn
      iframe Hpn
      rw [gmap_delete_idem]
      iapply amapEnts_del $$ Hents
  · have hp' : (GMap.delete n m) !! kk = some p := by
      rw [GMap.lookup_delete_ne _ (Ne.symm hk)]; exact hp
    iintro ⟨Hents, Hpn⟩
    icases amapEnts_take _ _ _ _ p hp' $$ Hents with ⟨Hents, ⟨%o, %Ho, Hop⟩⟩
    icases ongoingOpRep_open p o $$ Hop with ⟨%g, %sw, Hp, Hsr, Hsrc, Hsw, %Hg⟩
    iexists o, g
    iframe Hp
    isplitl []
    · ipureintro; exact ⟨Ho, Hg.1, Hg.2.1⟩
    isplit
    · iintro Hp
      iframe Hpn
      iapply amapEnts_update am (GMap.delete n m) ongoingOpRep kk p o hp'
      |>.trans (amapEnts_congr _ _ _ _ (fun j => by
        rw [amap_put_get]; by_cases hj : j = kk
        · subst hj; simp [Ho]
        · simp [hj]))
      iframe Hents
      iapply ongoingOpRep_close
      unfold ongoingOpRepC
      iexists g, sw
      iframe Hp Hsr Hsrc Hsw
      ipureintro; exact Hg
    · iintro -
      iframe Hpn
      rw [gmap_delete_comm m n kk]
      iapply (amapEnts_del am (GMap.delete n m) ongoingOpRep kk) $$ Hents



theorem amapEnts_congr_del {n : Nat} {V : Type} (am am' : AMap n V) (m : GMap (BitVec n) Loc)
    (R : Loc → V → IProp GF) (key : BitVec n) (h : ∀ j, j ≠ key → am.get? j = am'.get? j) :
    amapEnts am (GMap.delete key m) R ⊢ amapEnts am' (GMap.delete key m) R := by
  unfold amapEnts
  refine BigSepM.bigSepM_mono (M := GMap (BitVec n)) (fun {j q} hj => ?_)
  have hne : j ≠ key := by
    intro he; subst he
    change (GMap.delete j m) !! j = some q at hj; rw [GMap.lookup_delete] at hj; cases hj
  iintro ⟨%x, %Hx, H⟩
  iexists x
  iframe H
  ipureintro; rw [← h j hne]; exact Hx

/-- The low half of `ShiftInts(a, b)` is `b`. -/
theorem shiftInts_low (a b : w32) : (model.shiftInts a b).setWidth 32 = b := by
  -- bitwise, not `bv_decide` (its native evaluation adds an axiom to `goal_spec`)
  unfold model.shiftInts
  ext i hi
  simp [BitVec.getElem_setWidth, BitVec.getLsbD_signExtend, hi]
  omega

/-- `shortCircuit` keeps the read ops at the keys of their ids (H1b-R1). -/
theorem shortCircuit_ropsKeyed (s s2 : RState) (n : w32) (value : model.ValTag) (fo : Bool)
    (o : List Out) (h : model.shortCircuit s n value fo = some (s2, o)) (hk : ropsKeyed s.rops) :
    ropsKeyed s2.rops := by
  obtain ⟨op, -, hl, -⟩ := sc.shortCircuit_inv s s2 n value fo o h
  have := sc.loopF_inv (sc.scF n value.v fo)
    (fun st => ropsKeyed st.1.rops)
    (fun k st st' hst hf => by
      unfold sc.scF at hf
      split at hf
      · rcases hf with hf | hf <;> cases hf; exact hst
      · split at hf
        · split at hf
          · rcases hf with hf | hf <;> cases hf
            exact ropsKeyed_del _ _ hst
          · rcases hf with hf | hf <;> cases hf; exact hst
        · rcases hf with hf | hf <;> cases hf; exact hst)
    (sc.scKeys op) (sc.scInit s n op, []) hk
  rw [hl] at this
  exact this

/-- The pure part of the reads loop's invariant at index `i` (model state `st`, Go maps `m`
(`OngoingReqs`), `rmv` (`rops`), obligations `rem` still owed). -/
def scP (s s' : RState) (outs : List Out) (n : w32) (v : w64) (fo : Bool) (op : OngoingOp)
    (pn : Loc) (i : Nat) (st : RState × List Out) (m : GMap w32 Loc) (rmv : GMap w64 Loc)
    (rem : List Out) : Prop :=
  i ≤ (sc.scKeys op).length ∧
  sc.loopF (sc.scF n v fo) ((sc.scKeys op).drop i) st = (s', outs) ∧ st.2 ++ rem = outs ∧
  (∀ j, (m !! j).isSome = (st.1.ongoingReqs.get? j).isSome) ∧
  (∀ j, (rmv !! j).isSome = (st.1.rops.get? j).isSome) ∧
  (m !! n = none ∨ m !! n = some pn) ∧
  (∀ x, st.1.ongoingReqs.get? n = some x → x = { op with shortReads := sc.scKeys op }) ∧
  st.1.maxN = s.maxN ∧ (st.1.wops = s.wops ∧ ropsKeyed st.1.rops) -- H1b-R1


theorem scP_same (s s' : RState) (outs : List Out) (n : w32) (v : w64) (fo : Bool)
    (op : OngoingOp) (pn : Loc) (i : Nat) (st : RState × List Out) (m : GMap w32 Loc)
    (rmv : GMap w64 Loc) (rem : List Out) (h : scP s s' outs n v fo op pn i st m rmv rem)
    (hi : i < (sc.scKeys op).length)
    (hl : sc.loopF (sc.scF n v fo) ((sc.scKeys op).drop (i + 1)) st = (s', outs)) :
    scP s s' outs n v fo op pn (i + 1) st m rmv rem := by
  obtain ⟨-, -, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨hi, hl, h3, h4, h5, h6, h7, h8, h9⟩

theorem scP_del (s s' : RState) (outs : List Out) (n : w32) (v : w64) (fo : Bool)
    (op : OngoingOp) (pn : Loc) (i : Nat) (st : RState × List Out) (m : GMap w32 Loc)
    (rmv : GMap w64 Loc) (rem rem' : List Out) (kk : w32) (id : w64) (r : Out)
    (h : st.2 ++ rem = outs ∧ (∀ j, (m !! j).isSome = (st.1.ongoingReqs.get? j).isSome) ∧
      (∀ j, (rmv !! j).isSome = (st.1.rops.get? j).isSome) ∧
      (m !! n = none ∨ m !! n = some pn) ∧
      (∀ x, st.1.ongoingReqs.get? n = some x → x = { op with shortReads := sc.scKeys op }) ∧
      st.1.maxN = s.maxN ∧ (st.1.wops = s.wops ∧ ropsKeyed st.1.rops))
    (hi : i < (sc.scKeys op).length)
    (hl : sc.loopF (sc.scF n v fo) ((sc.scKeys op).drop (i + 1))
      ({ st.1 with rops := st.1.rops.del id, ongoingReqs := st.1.ongoingReqs.del kk },
        st.2 ++ [r]) = (s', outs))
    (hrem : rem = r :: rem') :
    scP s s' outs n v fo op pn (i + 1)
      ({ st.1 with rops := st.1.rops.del id, ongoingReqs := st.1.ongoingReqs.del kk }, st.2 ++ [r])
      (GMap.delete kk m) (GMap.delete id rmv) rem' := by
  obtain ⟨h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨hi, hl, by rw [← h3, hrem]; simp, fun j => ?_, fun j => ?_, ?_, fun x hx => ?_, h8, ⟨h9.1, ropsKeyed_del _ _ h9.2⟩⟩
  · by_cases hj : j = kk
    · subst hj; rw [GMap.lookup_delete]; simp only [amap_del_get_self]; rfl
    · rw [GMap.lookup_delete_ne _ (Ne.symm hj)]; simp only [amap_del_get_ne _ _ _ hj]; exact h4 j
  · by_cases hj : j = id
    · subst hj; rw [GMap.lookup_delete]; simp only [amap_del_get_self]; rfl
    · rw [GMap.lookup_delete_ne _ (Ne.symm hj)]; simp only [amap_del_get_ne _ _ _ hj]; exact h5 j
  · by_cases hk : kk = n
    · subst hk; left; exact GMap.lookup_delete _ _
    · rw [GMap.lookup_delete_ne _ hk]; exact h6
  · apply h7
    simp only at hx
    rw [amap_del_get] at hx
    split at hx
    · cases hx
    · exact hx

/-- What `ShortCircuit` changes: the read ops and `OngoingReqs`. -/
def scPost (ρ : Repl2Names) (ropsR orR : Loc) (s' : RState) : IProp GF :=
  iprop(amapRep ropsR s'.rops (fun p r => readOpRep ρ p r) ∗ amapRep orR s'.ongoingReqs ongoingOpRep)

/-- Back to the maps after the loop (entry `n` put back if still there). -/
theorem scClose (ρ : Repl2Names) (st1 : RState) (ropsR orR : Loc) (m : GMap w32 Loc)
    (rmv : GMap w64 Loc)
    (n : w32) (pn : Loc) (gn : src.gryffcommon.OngoingOp) (sw : List w32) (opS : OngoingOp)
    (hodom : ∀ j, (m !! j).isSome = (st1.ongoingReqs.get? j).isSome)
    (hrdom : ∀ j, (rmv !! j).isSome = (st1.rops.get? j).isSome)
    (hn : m !! n = none ∨ m !! n = some pn)
    (hnv : ∀ x, st1.ongoingReqs.get? n = some x → x = opS)
    (hg : gn.RequestId' = opS.requestId ∧ gn.ClientId' = opS.clientId ∧ gn.OpType' = opS.isRead ∧
      gn.Key' = W64 0 ∧ sw = []) :
    ropsR ↦$ rmv ∗ amapEnts (GF := GF) st1.rops rmv (fun p r => readOpRep ρ p r) ∗
      orR ↦$ m ∗ amapEnts st1.ongoingReqs (GMap.delete n m) ongoingOpRep ∗
      pn ↦ gn ∗ gn.ShortReads' ↦* opS.shortReads ∗ ownSliceCap w32 gn.ShortReads' (DFrac.own 1) ∗
      gn.ShortWrites' ↦* sw ⊢
    scPost ρ ropsR orR st1 := by
  unfold scPost
  iintro ⟨Hrm, Hrents, Hom, Hoents, Hpn, Hsr, Hsrc, Hsw⟩
  isplitl [Hrm Hrents]
  · iapply (amapRep_open ropsR _ _).2
    iexists rmv
    iframe Hrm Hrents
    ipureintro; exact hrdom
  iapply (amapRep_open orR _ _).2
  iexists m
  iframe Hom
  isplitl []
  · ipureintro; exact hodom
  rcases hn with hn | hn
  · rw [GMap.delete_notin _ _ hn]
    iexact Hoents
  · obtain ⟨x, hx⟩ : ∃ x, st1.ongoingReqs.get? n = some x := by
      have := hodom n; rw [hn] at this
      cases h : st1.ongoingReqs.get? n with
      | none => rw [h] at this; cases this
      | some x => exact ⟨x, rfl⟩
    have hxe := hnv x hx
    subst hxe
    have hput : ∀ j, (st1.ongoingReqs.put n x).get? j = st1.ongoingReqs.get? j := by
      intro j; rw [amap_put_get]; by_cases hj : j = n
      · subst hj; simp [hx]
      · simp [hj]
    iapply amapEnts_congr _ _ _ _ hput
    iapply amapEnts_update _ _ _ n pn x hn
    iframe Hoents
    iapply ongoingOpRep_close
    unfold ongoingOpRepC
    iexists gn, sw
    iframe Hpn Hsr Hsrc Hsw
    ipureintro; exact hg

end

end Perennial.gryff.replica2
