/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/CoordW2.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1b: the coordinator's `HandleWrite2Reply` (`ShortCircuit` on the write's own state).

The helpers of `H1/CoordW2.lean` (its definitions and lemmas, everything before its method
proofs), apart so that other modules import them without the proofs (CLAUDE.md, "Import tiers").
-/

module

public import Dsverify.Proof.gryff.H1.CoordSCDefs
public import Dsverify.Proof.gryff.H1.PureWrite
public import Dsverify.Proof.gryff.PureL.Frame
public import Dsverify.GeneratedProof.gryff.examples.gryffnet
public import Dsverify.Proof.gryff.Replica2.Specs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB RecoveryInstance Proposal ReadOp WriteOp OngoingOp
  Msg Ev Ext Out Cmd Deps AMap StepRes)

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem amap_put_ne_nil {n : Nat} {V : Type} (l : AMap n V) (k : BitVec n) (v : V) :
    l.put k v ≠ [] := by
  cases l with
  | nil => simp [model.AMap.put]
  | cons e t =>
    simp only [model.AMap.put]
    split
    · simp
    · split <;> simp

theorem amap_put_del {n : Nat} {V : Type} (l : AMap n V) (k : BitVec n) (v : V) :
    (l.put k v).del k = l.del k := by
  induction l with
  | nil => simp [model.AMap.put, model.AMap.del]
  | cons e t ih =>
    obtain ⟨k', v'⟩ := e
    simp only [model.AMap.put]
    by_cases h1 : k = k'
    · subst h1; simp [model.AMap.del]
    · simp only [h1, ↓reduceIte]
      have hne : (k' != k) = true := bne_iff_ne.2 (Ne.symm h1)
      split
      · simp [model.AMap.del, hne]
      · simp only [model.AMap.del, List.filter_cons, hne, ↓reduceIte] at ih ⊢
        rw [ih]

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF]
variable [strconvA : strconv.Assumptions] -- N-5


instance pure_wand_persistent_h1b (φ : Prop) (P : IProp GF) [Persistent P] :
    Persistent iprop(⌜φ⌝ -∗ P) where
  persistent := by
    by_cases h : φ
    · iintro H
      ihave #HP := H $$ %h
      imodintro
      iintro -
      iexact HP
    · iintro -
      imodintro
      iintro %hφ
      exact absurd hφ h

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 4096 in
instance (priority := high) icoordOk_persistent' (ρ : Repl2Names) (ic : GoInterface) (k : Fin 3)
    (C : model.ValTag → List Out → IProp GF) : Persistent (icoordOk ρ ic k C) := by
  unfold icoordOk specT; infer_instance

theorem coordMisc_mono (co : Loc) (maxN : w32) (P P' Q Q' : Prop) (mtR fkR : Loc)
    (h1 : P → P') (h2 : Q → Q') :
    coordMisc (GF := GF) co maxN P Q mtR fkR ⊢ coordMisc co maxN P' Q' mtR fkR := by
  unfold coordMisc
  iintro ⟨%mst, %mat, %fkc, %mt, %fk, Hn, Hs, Ha, Hf, Hmt, Hfk, %Hmt0, Hmtm, Hfkc, %Hq⟩
  iexists mst, mat, fkc, mt, fk
  iframe Hn Hs Ha Hf Hmt Hfk Hfkc
  isplitl []
  · ipureintro; exact Hmt0
  isplitl [Hmtm]
  · cases mt.lookup (W64 0) with
    | none => icases Hmtm with %Hp; ipureintro; exact h1 Hp
    | some p => iexact Hmtm
  ipureintro; exact h2 Hq

/-- `MaxTags[0]`'s cell: the coordinator's `maxAppliedTag` (owned) or a persistent tag. -/
theorem mtCell_acc (p0 A : Loc) (mat : src.gryffproto.Tag) :
    ((⌜p0 = A⌝ ∨ ∃ gt : src.gryffproto.Tag, p0 ↦□ gt) ∗ A ↦ mat : IProp GF) ⊢
      ∃ (dq : DFrac) (gt0 : src.gryffproto.Tag), p0 ↦{dq} gt0 ∗
        (p0 ↦{dq} gt0 -∗ A ↦ mat ∗ (⌜p0 = A⌝ ∨ ∃ gt : src.gryffproto.Tag, p0 ↦□ gt)) := by
  iintro ⟨(%Hp | ⟨%gt, #Hgt⟩), Ha⟩
  · subst Hp
    iexists DFrac.own 1, mat
    iframe Ha
    iintro Ha
    iframe Ha
    ileft; ipureintro; rfl
  · iexists DFrac.discard, gt
    iframe Hgt Ha
    iintro -
    iright; iexists gt; iframe Hgt

theorem wops_ne_nil {V : Type} (l : AMap 64 V) (k : w64) (v : V) (h : l.get? k = some v) :
    l ≠ [] := by
  rintro rfl; cases h

/-- The write op after the reply's counters (`numWrite2Replies++`, `numWrite2Applies++`). -/
theorem w2_wo (ρ : Repl2Names) (co p : Loc) (g : src.gryffcommon.WriteOp) (op : src.gryffcommon.Op)
    (wr : Loc) (gd : src.gryffproto.Dep) (gt : src.gryffproto.Tag) (w : WriteOp) (applied : w32)
    (wt : model.Tag) (hwt : w.writeTag = some wt) (hgt : tagOf gt = wt)
    (hg : op.RequestId' = w.requestId ∧ op.ClientId' = w.clientId ∧ op.Key' = W64 0 ∧ g.N' = w.n ∧
      depOf gd = w.dep ∧ g.WriteValue' = w.writeValue ∧ g.ForceWrite' = W32 1 ∧
      g.numWrite1Applies' = w.numWrite1Applies ∧ g.numWrite1Replies' = w.numWrite1Replies ∧
      g.numWrite2Applies' = w.numWrite2Applies ∧ g.numWrite2Replies' = w.numWrite2Replies ∧
      g.sentWrite2Round' = w.sentWrite2Round ∧ g.startedShortcircuitTimeout' = false) :
    writerIs (GF := GF) ρ w.clientId wr ∗
      p ↦ { g with numWrite2Replies' := g.numWrite2Replies' + W64 1,
                   numWrite2Applies' := if model.sgt applied 0 then g.numWrite2Applies' + W64 1
                                        else g.numWrite2Applies' } ∗
      g.Op' ↦ op ∗ op.Dep' ↦□ gd ∗
      (⌜g.MaxAppliedTag' = co.[src.gryffcommon.GryffCoordinator, go!"maxAppliedTag"]⌝ ∨
        ∃ gt : src.gryffproto.Tag, g.MaxAppliedTag' ↦□ gt) ∗
      optVtRep g.maxValTag' (some w.maxValTag) ∗ g.WriteTag' ↦□ gt ⊢
    writeOpRep ρ co p (w2Upd w applied) := by
  obtain ⟨Hg1, Hg2, Hg3, Hg4, Hg5, Hg6, Hg7, Hg8, Hg9, Hg10, Hg11, Hg12, Hg13⟩ := hg
  iintro ⟨#Hwr, Hp, Hop, #Hgd, Hmat, Hmvt, #Hgt⟩
  iapply (writeOpRep_open ρ co p _).2
  simp only [w2Upd]
  iexists _, op, wr, gd
  iframe Hwr Hp Hop Hgd Hmat Hmvt
  rw [hwt]
  isplitl []
  · iexists gt; iframe Hgt; ipureintro; exact hgt
  ipureintro
  refine ⟨Hg1, Hg2, Hg3, Hg4, Hg5, Hg6, Hg7, Hg8, Hg9, ?_, by simp [Hg11], Hg12, Hg13⟩
  simp only [Hg10]
  split <;> rfl

/-- The state with the write op at `id` updated in place. -/
def sMid (s : RState) (id : w64) (w' : WriteOp) : RState := { s with wops := s.wops.put id w' }

/-- Close `coordOwn` with the write op at `id` updated in place. -/
theorem coordOwn_close_wput (ρ : Repl2Names) (co : Loc) (ic : GoInterface) (k : Fin 3)
    (s : RState) (ropsR wopsR orR mtR fkR : Loc) (arS : GoSlice) (wm : GMap w64 Loc) (id : w64)
    (p : Loc) (w' : WriteOp) (hp : wm !! id = some p)
    (hdom : ∀ key, (wm.lookup key).isSome = (s.wops.get? key).isSome) (hrk : ropsKeyed s.rops) :
    coordFix (GF := GF) co ic k ropsR wopsR orR mtR fkR arS ∗
      coordMisc co s.maxN (s.wops.put id w' = [])
        (((s.wops.put id w').map (fun e => e.1.toNat)).Pairwise (· < ·)) mtR fkR ∗
      amapRep ropsR s.rops (fun p r => readOpRep ρ p r) ∗ amapRep orR s.ongoingReqs ongoingOpRep ∗
      wopsR ↦$ wm ∗ amapEnts s.wops (GMap.delete id wm) (fun p w => writeOpRep ρ co p w) ∗
      writeOpRep ρ co p w' ⊢
    coordOwn ρ co ic k { s with wops := s.wops.put id w' } := by
  iintro ⟨#Hfix, Hmisc, Hr, Ho, Hwm, Hwents, Hwo⟩
  iapply (coordOwn_open ρ co ic k _).2
  iexists ropsR, wopsR, orR, mtR, fkR, arS
  iframe Hfix Hmisc Hr Ho %hrk
  iapply (amapRep_open wopsR _ _).2
  iexists wm
  iframe Hwm
  isplitl []
  · ipureintro; intro key
    rw [amap_put_get]
    by_cases hk : key = id
    · subst hk; change (wm !! key).isSome = _; rw [hp, if_pos rfl]; rfl
    · rw [if_neg hk]; exact hdom key
  iapply amapEnts_update _ _ _ _ p _ hp
  iframe Hwents Hwo

end

end Perennial.gryff.replica2
