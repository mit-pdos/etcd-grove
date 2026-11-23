/-
The linked results of `SortFuncOn.lean` (moved out of it for the import tiers, CLAUDE.md
"Import tiers": a proof file sees its callees through their specs; this linking module composes the
proofs).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.breakPatternsCmpFunc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.choosePivotCmpFunc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.heapSortCmpFunc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.insertionSortCmpFunc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.medianAdjacentCmpFunc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.medianCmpFunc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.order2CmpFunc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.partialInsertionSortCmpFunc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.partitionCmpFunc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.partitionEqualCmpFunc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.pdqsortCmpFunc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.reverseRangeCmpFunc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.siftDownCmpFunc

@[expose] public section
set_option linter.iris.style.nameCheck false
noncomputable section

namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std

section link
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

theorem slices.wp_insertionSortCmpFuncOn : slices.insertionSortCmpFunc.specOn (GF := GF) (hG := hG) :=
  slices.insertionSortCmpFunc.wp_proofOn

theorem slices.wp_siftDownCmpFuncOn : slices.siftDownCmpFunc.specOn (GF := GF) (hG := hG) :=
  slices.siftDownCmpFunc.wp_proofOn

theorem slices.wp_heapSortCmpFuncOn : slices.heapSortCmpFunc.specOn (GF := GF) (hG := hG) :=
  slices.heapSortCmpFunc.wp_proofOn slices.wp_siftDownCmpFuncOn

theorem slices.wp_breakPatternsCmpFuncOn : slices.breakPatternsCmpFunc.specOn (GF := GF) (hG := hG) :=
  slices.breakPatternsCmpFunc.wp_proofOn slices.wp_nextPowerOfTwo slices.xorshift.wp_Next

theorem slices.wp_order2CmpFuncOn : slices.order2CmpFunc.specOn (GF := GF) (hG := hG) :=
  slices.order2CmpFunc.wp_proofOn

theorem slices.wp_medianCmpFuncOn : slices.medianCmpFunc.specOn (GF := GF) (hG := hG) :=
  slices.medianCmpFunc.wp_proofOn slices.wp_order2CmpFuncOn

theorem slices.wp_medianAdjacentCmpFuncOn : slices.medianAdjacentCmpFunc.specOn (GF := GF) (hG := hG) :=
  slices.medianAdjacentCmpFunc.wp_proofOn slices.wp_medianCmpFuncOn

theorem slices.wp_choosePivotCmpFuncOn : slices.choosePivotCmpFunc.specOn (GF := GF) (hG := hG) :=
  slices.choosePivotCmpFunc.wp_proofOn slices.wp_medianCmpFuncOn slices.wp_medianAdjacentCmpFuncOn

theorem slices.wp_reverseRangeCmpFuncOn : slices.reverseRangeCmpFunc.specOn (GF := GF) (hG := hG) :=
  slices.reverseRangeCmpFunc.wp_proofOn

theorem slices.wp_partialInsertionSortCmpFuncOn :
    slices.partialInsertionSortCmpFunc.specOn (GF := GF) (hG := hG) :=
  slices.partialInsertionSortCmpFunc.wp_proofOn

theorem slices.wp_partitionEqualCmpFuncOn : slices.partitionEqualCmpFunc.specOn (GF := GF) (hG := hG) :=
  slices.partitionEqualCmpFunc.wp_proofOn

theorem slices.wp_partitionCmpFuncOn : slices.partitionCmpFunc.specOn (GF := GF) (hG := hG) :=
  slices.partitionCmpFunc.wp_proofOn

theorem slices.wp_pdqsortCmpFuncOn : slices.pdqsortCmpFunc.specOn (GF := GF) (hG := hG) :=
  slices.pdqsortCmpFunc.wp_proofOn slices.wp_insertionSortCmpFuncOn slices.wp_heapSortCmpFuncOn
    slices.wp_breakPatternsCmpFuncOn slices.wp_choosePivotCmpFuncOn slices.wp_reverseRangeCmpFuncOn
    slices.wp_partialInsertionSortCmpFuncOn slices.wp_partitionEqualCmpFuncOn
    slices.wp_partitionCmpFuncOn

theorem slices.wp_SortFuncPhi : slices.SortFunc.specPhi (GF := GF) (hG := hG) :=
  slices.SortFunc.wp_proofPhi math.bits.wp_Len slices.wp_pdqsortCmpFuncOn

end link

end Perennial

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section link
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [slices.Assumptions]

/-- `slices.SortFunc.specOn`, linked (`SortFunc.wp_proofOn` over `wp_SortFuncPhi`). -/
theorem slices.wp_SortFuncOn : slices.SortFunc.specOn (hG := hG) :=
  slices.SortFunc.wp_proofOn slices.wp_SortFuncPhi

end link

end Perennial.github_com.imdea_software.swiftpaxos
