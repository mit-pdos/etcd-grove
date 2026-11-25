/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/Coord.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1: the coordinator's parts (`coordOwn` opened) and `icoordOk`'s.
-/
module

public import Dsverify.Proof.gryff.H1.Amap
public import Dsverify.Proof.gryff.PureLa.Count
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

instance writerIs_persistent_h1 (ρ : Repl2Names) (cid : w32) (w : Loc) :
    Persistent (writerIs ρ cid w : IProp GF) := by
  unfold writerIs; infer_instance

theorem readOpRep_open (ρ : Repl2Names) (p : Loc) (r : ReadOp) :
    readOpRep (GF := GF) ρ p r ⊣⊢ ∃ (g : src.gryffcommon.ReadOp) (o : src.gryffcommon.Op) (rws : List w32)
      (w : Loc) (gd : src.gryffproto.Dep),
    writerIs ρ r.clientId w ∗ p ↦ g ∗ o.Dep' ↦□ gd ∗
    g.Op' ↦ o ∗ optVtRep g.maxValTag' r.maxValTag ∗ optVtRep g.ReadValTag' r.readValTag ∗
    g.replicasWithMaxTag' ↦* rws ∗ ownSliceCap w32 g.replicasWithMaxTag' (DFrac.own 1) ∗
    ⌜o.RequestId' = r.requestId ∧ o.ClientId' = r.clientId ∧ o.Key' = W64 0 ∧ g.N' = r.n ∧
      g.numRead1Replies' = r.numRead1Replies ∧ g.numRead2Replies' = r.numRead2Replies ∧
      g.readsWithMaxTag' = r.readsWithMaxTag ∧ g.sentRead2Round' = r.sentRead2Round ∧
      g.determinedReadVal' = r.determinedReadVal ∧ rws = r.replicasWithMaxTag⌝ := by
  unfold readOpRep; exact .rfl

/-- H1-R10's fact gives distinct keys (integration). -/
theorem wops_sorted_nodup {n : Nat} {V : Type} (l : model.AMap n V)
    (h : (l.map (fun e => e.1.toNat)).Pairwise (· < ·)) : (l.map Prod.fst).Nodup := by
  have h1 : ((l.map Prod.fst).map BitVec.toNat).Nodup := by
    rw [List.map_map]; exact h.imp (fun hlt => Nat.ne_of_lt hlt)
  exact List.Pairwise.of_map BitVec.toNat (fun a b hne hab => hne (by rw [hab])) h1

/-- H1-R10's fact is kept by `put` (integration; unit L-a's `srt_put`). -/
theorem wops_sorted_put {n : Nat} {V : Type} (l : model.AMap n V) (k : BitVec n) (v : V)
    (h : (l.map (fun e => e.1.toNat)).Pairwise (· < ·)) :
    ((l.put k v).map (fun e => e.1.toNat)).Pairwise (· < ·) := by
  have h1 : pure.La.Srt l := List.pairwise_map.1 h
  exact List.pairwise_map.2 (pure.La.srt_put h1 k v)

/-- Hub request H1b-R1: every read op sits at the key of its ids. -/
def ropsKeyed (l : AMap 64 ReadOp) : Prop :=
  ∀ id r, l.get? id = some r → id = model.shiftInts r.requestId r.clientId

theorem ropsKeyed_del (l : AMap 64 ReadOp) (k : w64) (h : ropsKeyed l) :
    ropsKeyed (l.del k) := by
  intro id r hr
  rw [amap_del_get] at hr
  split at hr
  · cases hr
  · exact h id r hr

theorem ropsKeyed_put (l : AMap 64 ReadOp) (k : w64) (r : ReadOp) (h : ropsKeyed l)
    (hk : k = model.shiftInts r.requestId r.clientId) : ropsKeyed (l.put k r) := by
  intro id r' hr
  rw [amap_put_get] at hr
  split at hr
  · cases hr; subst_vars; rfl
  · exact h id r' hr

/-- The coordinator's fixed fields (persistent). -/
def coordFix (co : Loc) (ic : GoInterface) (k : Fin 3) (ropsR wopsR orR mtR fkR : Loc)
    (arS : GoSlice) : IProp GF :=
  iprop(co.[src.gryffcommon.GryffCoordinator, go!"id"] ↦□ rid32 k ∗
    co.[src.gryffcommon.GryffCoordinator, go!"icoord"] ↦□ ic ∗
    co.[src.gryffcommon.GryffCoordinator, go!"regular"] ↦□ false ∗
    co.[src.gryffcommon.GryffCoordinator, go!"numReplicas"] ↦□ W64 3 ∗
    co.[src.gryffcommon.GryffCoordinator, go!"proxy"] ↦□ true ∗
    co.[src.gryffcommon.GryffCoordinator, go!"thrifty"] ↦□ false ∗
    co.[src.gryffcommon.GryffCoordinator, go!"epaxosMode"] ↦□ false ∗
    co.[src.gryffcommon.GryffCoordinator, go!"allReplicas"] ↦□ arS ∗ arS ↦*□ [W32 0, W32 1, W32 2] ∗
    co.[src.gryffcommon.GryffCoordinator, go!"rops"] ↦□ ropsR ∗
    co.[src.gryffcommon.GryffCoordinator, go!"wops"] ↦□ wopsR ∗
    co.[src.gryffcommon.GryffCoordinator, go!"OngoingReqs"] ↦□ orR ∗
    co.[src.gryffcommon.GryffCoordinator, go!"MaxTags"] ↦□ mtR ∗
    co.[src.gryffcommon.GryffCoordinator, go!"ForcedKeys"] ↦□ fkR)

instance coordFix_persistent (co : Loc) (ic : GoInterface) (k : Fin 3)
    (ropsR wopsR orR mtR fkR : Loc) (arS : GoSlice) :
    Persistent (coordFix (GF := GF) co ic k ropsR wopsR orR mtR fkR arS) := by
  unfold coordFix; infer_instance

theorem coordFix_open (co : Loc) (ic : GoInterface) (k : Fin 3) (ropsR wopsR orR mtR fkR : Loc)
    (arS : GoSlice) :
    coordFix (GF := GF) co ic k ropsR wopsR orR mtR fkR arS ⊣⊢
    co.[src.gryffcommon.GryffCoordinator, go!"id"] ↦□ rid32 k ∗
    co.[src.gryffcommon.GryffCoordinator, go!"icoord"] ↦□ ic ∗
    co.[src.gryffcommon.GryffCoordinator, go!"regular"] ↦□ false ∗
    co.[src.gryffcommon.GryffCoordinator, go!"numReplicas"] ↦□ W64 3 ∗
    co.[src.gryffcommon.GryffCoordinator, go!"proxy"] ↦□ true ∗
    co.[src.gryffcommon.GryffCoordinator, go!"thrifty"] ↦□ false ∗
    co.[src.gryffcommon.GryffCoordinator, go!"epaxosMode"] ↦□ false ∗
    co.[src.gryffcommon.GryffCoordinator, go!"allReplicas"] ↦□ arS ∗ arS ↦*□ [W32 0, W32 1, W32 2] ∗
    co.[src.gryffcommon.GryffCoordinator, go!"rops"] ↦□ ropsR ∗
    co.[src.gryffcommon.GryffCoordinator, go!"wops"] ↦□ wopsR ∗
    co.[src.gryffcommon.GryffCoordinator, go!"OngoingReqs"] ↦□ orR ∗
    co.[src.gryffcommon.GryffCoordinator, go!"MaxTags"] ↦□ mtR ∗
    co.[src.gryffcommon.GryffCoordinator, go!"ForcedKeys"] ↦□ fkR := .rfl

/-- The coordinator's fields other than its three op maps (`wopsNil`: the model's `wops = []`,
what an absent `MaxTags[0]` says). -/
def coordMisc (co : Loc) (maxN : w32) (wopsNil wopsSorted : Prop) (mtR fkR : Loc) :
    IProp GF :=
  iprop(∃ (mst mat : src.gryffproto.Tag) (fkc : GoSlice) (mt : GMap w64 Loc) (fk : GMap w64 w32),
    co.[src.gryffcommon.GryffCoordinator, go!"maxN"] ↦ maxN ∗
    co.[src.gryffcommon.GryffCoordinator, go!"maxSeenTag"] ↦ mst ∗
    co.[src.gryffcommon.GryffCoordinator, go!"maxAppliedTag"] ↦ mat ∗
    co.[src.gryffcommon.GryffCoordinator, go!"ForcedKeysChanged"] ↦ fkc ∗
    mtR ↦$ mt ∗ fkR ↦$ fk ∗
    ⌜∀ kk, kk ≠ W64 0 → mt.lookup kk = none⌝ ∗
    (match mt.lookup (W64 0) with
     | none => iprop(⌜wopsNil⌝)
     | some p => iprop(⌜p = co.[src.gryffcommon.GryffCoordinator, go!"maxAppliedTag"]⌝ ∨
        ∃ gt : src.gryffproto.Tag, p ↦□ gt)) ∗
    fkc ↦* ([] : List w64) ∗ ⌜wopsSorted⌝)

theorem coordOwn_open (ρ : Repl2Names) (co : Loc) (ic : GoInterface) (k : Fin 3) (s : RState) :
    coordOwn (GF := GF) ρ co ic k s ⊣⊢ ∃ (ropsR wopsR orR mtR fkR : Loc) (arS : GoSlice),
      coordFix co ic k ropsR wopsR orR mtR fkR arS ∗
      coordMisc co s.maxN (s.wops = []) ((s.wops.map (fun e => e.1.toNat)).Pairwise (· < ·)) mtR fkR ∗
      ⌜ropsKeyed s.rops⌝ ∗ -- H1b-R1
      amapRep ropsR s.rops (fun p r => readOpRep ρ p r) ∗
      amapRep wopsR s.wops (fun p w => writeOpRep ρ co p w) ∗
      amapRep orR s.ongoingReqs ongoingOpRep := by
  unfold coordOwn coordFix coordMisc
  constructor
  · iintro ⟨%ropsR, %wopsR, %orR, %mtR, %fkR, %arS, %mst, %mat, %fkc, %mt, %fk, #H1, #H2, #H3,
      #H4, #H5, #H6, #H7, #H8, #H9, #H10, #H11, #H12, #H13, #H14, Hn, Hs, Ha, Hf, Hmt, Hfk,
      %Hmt0, Hmtm, Hfkc, %Hsrt, %Hrk, Hr, Hw, Ho⟩
    iexists ropsR, wopsR, orR, mtR, fkR, arS
    iframe H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 Hr Hw Ho
    isplitl [Hn Hs Ha Hf Hmt Hfk Hmtm Hfkc]
    · iexists mst, mat, fkc, mt, fk
      iframe Hn Hs Ha Hf Hmt Hfk Hmtm Hfkc
      ipureintro; exact ⟨Hmt0, Hsrt⟩
    · ipureintro; exact Hrk
  · iintro ⟨%ropsR, %wopsR, %orR, %mtR, %fkR, %arS, ⟨#H1, #H2, #H3, #H4, #H5, #H6, #H7, #H8,
      #H9, #H10, #H11, #H12, #H13, #H14⟩, ⟨%mst, %mat, %fkc, %mt, %fk, Hn, Hs, Ha, Hf, Hmt, Hfk,
      %Hmt0, Hmtm, Hfkc, %Hsrt⟩, %Hrk, Hr, Hw, Ho⟩
    iexists ropsR, wopsR, orR, mtR, fkR, arS, mst, mat, fkc, mt, fk
    iframe H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 Hr Hw Ho Hn Hs Ha Hf Hmt Hfk Hmtm Hfkc
    ipureintro; exact ⟨Hmt0, Hsrt, Hrk⟩

end

end Perennial.gryff.replica2
