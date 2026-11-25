/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/CoordStart.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1: the coordinator's `StartRead`.

The helpers of `H1/CoordStart.lean` (its definitions and lemmas, everything before its method
proofs), apart so that other modules import them without the proofs (CLAUDE.md, "Import tiers").
-/

module

public import Dsverify.Proof.gryff.H1.Coord
public import Dsverify.Proof.gryff.H1.Pure
public import Dsverify.Proof.gryff.H1.PureStart
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


theorem wp_newOngoingOp (rid cid : w32) (b : Bool) (key : w64) (sw : Bool) (rs : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon }}
      (App (App (App (App (App (App (Val (@! src.gryffcommon.newOngoingOp))
        (Val #rid)) (Val #cid)) (Val #b)) (Val #key)) (Val #sw)) (Val #rs))
    {{ (op : Loc), RET #op; ∃ (g : src.gryffcommon.OngoingOp), op ↦ g ∗
        g.ShortReads' ↦* ([] : List w32) ∗ ownSliceCap w32 g.ShortReads' (DFrac.own 1) ∗
        g.ShortWrites' ↦* ([] : List w32) ∗
        ⌜g.RequestId' = rid ∧ g.ClientId' = cid ∧ g.OpType' = b ∧ g.Key' = key⌝ }} := by
  wp_start
  wp_auto
  wp_apply wp_slice_make2 (V := w32) as %sl1 ⟨Hsl1, Hcap1⟩
  · ipureintro; decide
  wp_apply wp_slice_make2 (V := w32) as %sl2 ⟨Hsl2, -⟩
  · ipureintro; decide
  simp only [show sint.nat (W64 0) = 0 from rfl, List.replicate_zero]
  iapply HΦ
  iexists _
  iframe
  ipureintro; simp

theorem amapEnts_forget {n : Nat} {V : Type} (am : AMap n V) (m : GMap (BitVec n) Loc)
    (R : Loc → V → IProp GF) (key : BitVec n) :
    amapEnts am m R ⊢ amapEnts am (GMap.delete key m) R := by
  cases hk : m !! key with
  | none => rw [GMap.delete_notin _ _ hk]
  | some p => exact (amapEnts_take am m R key p hk).trans BI.sep_elim_left

theorem amapEnts_acc {n : Nat} {V : Type} (am : AMap n V) (m : GMap (BitVec n) Loc)
    (R : Loc → V → IProp GF) (key : BitVec n) (p : Loc) (hp : m !! key = some p) :
    amapEnts am m R ⊢ (∃ v, ⌜am.get? key = some v⌝ ∗ R p v) ∗
      ((∃ v, ⌜am.get? key = some v⌝ ∗ R p v) -∗ amapEnts am m R) := by
  unfold amapEnts
  exact (BigSepM.bigSepM_lookup_acc (M := GMap (BitVec n)) hp).1

theorem writeOpRep_open (ρ : Repl2Names) (co p : Loc) (w : WriteOp) :
    writeOpRep (GF := GF) ρ co p w ⊣⊢ ∃ (g : src.gryffcommon.WriteOp) (o : src.gryffcommon.Op) (wr : Loc)
      (gd : src.gryffproto.Dep),
    writerIs ρ w.clientId wr ∗ p ↦ g ∗ g.Op' ↦ o ∗ o.Dep' ↦□ gd ∗
    (⌜g.MaxAppliedTag' = co.[src.gryffcommon.GryffCoordinator, go!"maxAppliedTag"]⌝ ∨
      ∃ gt : src.gryffproto.Tag, g.MaxAppliedTag' ↦□ gt) ∗
    optVtRep g.maxValTag' (some w.maxValTag) ∗
    (match w.writeTag with
     | none => iprop(⌜g.WriteTag' = Loc.null⌝)
     | some t => iprop(∃ gt : src.gryffproto.Tag, g.WriteTag' ↦□ gt ∗ ⌜tagOf gt = t⌝)) ∗
    ⌜o.RequestId' = w.requestId ∧ o.ClientId' = w.clientId ∧ o.Key' = W64 0 ∧ g.N' = w.n ∧
      depOf gd = w.dep ∧ g.WriteValue' = w.writeValue ∧ g.ForceWrite' = W32 1 ∧
      g.numWrite1Applies' = w.numWrite1Applies ∧ g.numWrite1Replies' = w.numWrite1Replies ∧
      g.numWrite2Applies' = w.numWrite2Applies ∧ g.numWrite2Replies' = w.numWrite2Replies ∧
      g.sentWrite2Round' = w.sentWrite2Round ∧ g.startedShortcircuitTimeout' = false⌝ := by
  unfold writeOpRep; exact .rfl

/-- `ongoingOpRep` with the capacity of `ShortReads` (`StartRead` appends to it). -/
def ongoingOpRepC (p : Loc) (o : OngoingOp) : IProp GF :=
  iprop(∃ (g : src.gryffcommon.OngoingOp) (sw : List w32), p ↦ g ∗ g.ShortReads' ↦* o.shortReads ∗
    ownSliceCap w32 g.ShortReads' (DFrac.own 1) ∗ g.ShortWrites' ↦* sw ∗
    ⌜g.RequestId' = o.requestId ∧ g.ClientId' = o.clientId ∧ g.OpType' = o.isRead ∧
      g.Key' = W64 0 ∧ sw = []⌝)

theorem ongoingOpRep_open (p : Loc) (o : OngoingOp) : ongoingOpRep (GF := GF) p o ⊢
    ∃ (g : src.gryffcommon.OngoingOp) (sw : List w32), p ↦ g ∗ g.ShortReads' ↦* o.shortReads ∗
    ownSliceCap w32 g.ShortReads' (DFrac.own 1) ∗ g.ShortWrites' ↦* sw ∗
    ⌜g.RequestId' = o.requestId ∧ g.ClientId' = o.clientId ∧ g.OpType' = o.isRead ∧
      g.Key' = W64 0 ∧ sw = []⌝ := by
  unfold ongoingOpRep; exact .rfl

theorem ongoingOpRep_close (p : Loc) (o : OngoingOp) : ongoingOpRepC (GF := GF) p o ⊢ ongoingOpRep p o := by
  unfold ongoingOpRep ongoingOpRepC
  iintro ⟨%g, %sw, Hp, Hsr, Hcap, Hsw, %Hg⟩
  iexists g, sw
  iframe Hp Hsr Hcap Hsw
  ipureintro; exact Hg

theorem wp_NewOp (rid cid : w32) (key : w64) (dp : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon }}
      (App (App (App (App (Val (@! src.gryffcommon.NewOp))
        (Val #rid)) (Val #cid)) (Val #key)) (Val #dp))
    {{ (o : Loc), RET #o; o ↦ (src.gryffcommon.Op.mk rid cid key dp) }} := by
  wp_start
  wp_auto
  iapply HΦ
  iframe

theorem wp_newRead (rid cid : w32) (key : w64) (dp : Loc) (n : w32) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon }}
      (App (App (App (App (App (Val (@! src.gryffcommon.newRead))
        (Val #rid)) (Val #cid)) (Val #key)) (Val #dp)) (Val #n))
    {{ (r : Loc), RET #r; ∃ (g : src.gryffcommon.ReadOp), r ↦ g ∗
        g.Op' ↦ (src.gryffcommon.Op.mk rid cid key dp) ∗
        ⌜g.N' = n ∧ g.maxValTag' = Loc.null ∧ g.ReadValTag' = Loc.null ∧
          g.numRead1Replies' = W64 0 ∧ g.numRead2Replies' = W64 0 ∧ g.readsWithMaxTag' = W64 0 ∧
          g.sentRead2Round' = false ∧ g.determinedReadVal' = false ∧
          g.replicasWithMaxTag' = slice.nil⌝ }} := by
  wp_start
  wp_auto
  wp_apply wp_NewOp as %o Ho
  wp_apply wp_slice_make2 (V := src.gryffcommon.ReadValTag) as %sl1 -
  · ipureintro; decide
  iapply HΦ
  iexists _
  iframe
  ipureintro; simp

theorem wp_ShiftInts (a b : w32) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon }}
      (App (App (Val (@! src.gryffcommon.ShiftInts)) (Val #a)) (Val #b))
    {{ RET #(model.shiftInts a b); True }} := by
  wp_start
  wp_auto
  have h : ∀ x : w32, W64 (sint.Z x) = x.signExtend 64 := fun x => rfl
  rw [h a, h b]
  have e : (BitVec.signExtend 64 a <<< W64 32 ||| BitVec.signExtend 64 b) = model.shiftInts a b := by
    have h32 : (W64 32).toNat = 32 := by decide
    simp only [model.shiftInts, BitVec.shiftLeft_eq', h32]
  rw [e]
  iapply HΦ
  ipureintro; trivial

end

end Perennial.gryff.replica2
