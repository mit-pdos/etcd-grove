/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/SortedIds.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The recovery's sorting (recovery.go `sortedIds`; dpath.go `cmdIdLess`, `cmdIdCmp`) refining the
model's `sortIds` (Spec/swift/Model/Defs.lean), over Perennial's proved `slices.SortFunc.spec`
(SW3 resolved in the fork, aff5b1a: the sorts use `slices.SortFunc` with three-way comparators).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HashLogKey
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HashLeafDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Steps
public import Perennial.Spec.slices.SortFunc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SortedIdsDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-! ## Pure: `cmdIdLess`, `sortIds` -/

namespace sp

end sp

/-! ## The Go functions -/

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]

variable [swift.Assumptions] [slices.Assumptions]

theorem swift.cmdIdLess.wp_proof : swift.cmdIdLess.specI (hG := hG) := fun a b => by
  wp_start
  wp_auto
  wp_if_destruct
  · ihave H := HΦ $$ []
    · itrivial
    iExactEq H; congr 2; unfold swift.cmdIdLt; simp [Hif]
  · wp_if_destruct
    · ihave H := HΦ $$ []
      · itrivial
      iExactEq H; congr 2; unfold swift.cmdIdLt; simp [Hif]
    · ihave H := HΦ $$ []
      · itrivial
      iExactEq H; congr 2; unfold swift.cmdIdLt; simp [Hif]; omega

theorem swift.cmdIdCmp.wp_proof (wp_cmdIdLess : swift.cmdIdLess.specI (hG := hG)) :
    swift.cmdIdCmp.specI (hG := hG) := fun a b => by
  wp_start
  wp_auto
  wp_apply wp_cmdIdLess
  cases hab : swift.cmdIdLt a b
  · wp_auto
    wp_apply wp_cmdIdLess
    cases hba : swift.cmdIdLt b a
    · wp_auto
      iapply HΦ; ipureintro; simp
    · wp_auto
      iapply HΦ; ipureintro; simp
  · wp_auto
    iapply HΦ; ipureintro; simp

theorem swift.sortedIds.wp_proof (wp_SortFunc : slices.SortFunc.spec (hG := hG))
    (wp_cmdIdCmp : swift.cmdIdCmp.specI (hG := hG)) : swift.sortedIds.specI (hG := hG) := by
  intro m mk dq
  haveI := swift.hlog.cmdId_intoValInj (sem := sem)
  wp_start as ⟨Hm, %Hbd⟩
  ihave #Hcmp := swift.cmdIdCmp_implements wp_cmdIdCmp $$ []
  · iassumption
  wp_auto
  wp_apply_core (wp_map_len_lt (K := swift.CommandId) (V := Loc) m mk dq) $$ [$Hm]
  iintro ⟨Hm, %Hsz⟩
  wp_auto
  wp_apply (wp_slice_make3 (V := swift.CommandId) (W64 0) (W64 (GMap.size mk)) (by word))
    as %sl0 ⟨Hsl0, Hcap0, -⟩
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range (fun keys i => iprop(∃ (sl : GoSlice),
      ids_ptr ↦ sl ∗ sl ↦* keys.take i.toNat ∗ ownSliceCap swift.CommandId sl (DFrac.own 1) ∗
      (∃ x : swift.CommandId, id_ptr ↦ x) ∗ ⌜0 ≤ i⌝))) $$ Hm
  iintro %keys %Hkeys
  isplitl [ids Hsl0 Hcap0 id]
  · iexists sl0
    iframe
    ipureintro; omega
  isplitl []
  · imodintro
    iintro %i %key %v %Hiv ⟨%sl, ids, Hsl, Hcap, ⟨%x, id⟩, %Hi0⟩
    wp_auto
    wp_bind (App (Val (GoInstruction (CompositeLiteral
      (go.GoType.SliceType swift.CommandId.ty)))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := swift.CommandId) (t := swift.CommandId.ty) [key]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %lsl ⟨Hlsl, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [Hsl Hcap Hlsl] as %nsl ⟨Hsl, Hcap, -⟩
    · iframe
    unfold forMapPostcondition
    iright; ileft
    isplitr; · ipureintro; rfl
    iexists nsl
    iframe ids Hcap
    isplitl [Hsl]
    · iExactEq Hsl; congr 1
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_succ, Hiv.1]; rfl
    isplitl [id]
    · iexists _; iexact id
    ipureintro; omega
  iintro ⟨%sl, ids, Hsl, Hcap, -, %Hi0⟩ Hm
  wp_auto
  have htake : List.take (↑mk.size : Int).toNat keys = keys := by
    rw [List.take_of_length_le]; rw [Hkeys.2.1]; omega
  rw [htake]
  wp_apply (wp_SortFunc (E := swift.CommandId) (S := go.GoType.SliceType swift.CommandId.ty)
      (fun a b => swift.cmdIdLt a b = true) sl _ keys swift.cmdIdLt_swo) $$ [Hsl Hcmp]
    as %xs' ⟨Hsl, %Hperm, %Hsorted⟩
  · iframe Hsl Hcmp
    ipureintro; rw [Hkeys.2.1]; omega
  iapply HΦ
  iframe
  ipureintro
  have hperm := Hperm
  refine ⟨hperm.nodup_iff.mp Hkeys.2.2, fun k => by rw [← hperm.mem_iff]; exact Hkeys.1 k,
    fun L hL => sp.sortIds_eq L _ hL.symm ?_⟩
  rw [List.pairwise_map, List.pairwise_iff_getElem]
  intro i j hi hj hij
  have := Hsorted i j _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj) hij
  rw [swift.cmdIdLt_toCmdId] at this
  simp [this]

end specs

end Perennial.github_com.imdea_software.swiftpaxos
