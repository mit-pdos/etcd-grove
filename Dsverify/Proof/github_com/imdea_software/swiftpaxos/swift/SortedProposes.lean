/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/SortedProposes.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`sortedProposes(m)` (recovery.go; `handleSync`'s reproposals): the same code as `sortedIds` on a
map with pointer values, so the same proof (SortedIds.lean's, without the sorting fact, which
`sortedProposes.specI` does not state). Round 14, sv-swa.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SortedIds
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncSpecs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [slices.Assumptions]

theorem swift.sortedProposes.wp_proof (wp_SortFunc : slices.SortFunc.spec (hG := hG))
    (wp_cmdIdCmp : swift.cmdIdCmp.specI (hG := hG)) : swift.sortedProposes.specI (hG := hG) := by
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
  exact ⟨hperm.nodup_iff.mp Hkeys.2.2, fun k => by rw [← hperm.mem_iff]; exact Hkeys.1 k⟩

end specs

end Perennial.github_com.imdea_software.swiftpaxos
