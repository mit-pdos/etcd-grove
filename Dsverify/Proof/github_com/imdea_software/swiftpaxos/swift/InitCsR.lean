/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/InitCsR.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`initCs(&r.cs, r.RPC)` on the replica's table (swift/defs.go:301): `swift.initCs.specR`
(Proof/swift/NewSpecs.lean), proved as the client's `initCs.wp_proof`
(Proof/swift/client/InitCs.lean), keeping every channel and entry.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewSpecs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

open swift.rd

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [rpc.Assumptions] [time.Assumptions]

set_option goose.wp.extras true

set_option hygiene false in
/-- `make(chan fastrpc.Serializable, defs.CHAN_BUFFER_SIZE)`, its fresh channel named `H`. -/
macro "mk_chR" H:ident : tactic => `(tactic| (
  wp_apply chan.wp_make2 (V := GoInterface) (W64 2000000) as %ch %γ ⟨#Hch, %Hcap, Hown⟩
  · ipureintro; decide
  ihave Hnew : freshChan ch $$ [Hown]
  · unfold freshChan; iexists γ; iframe Hch; iExactEq Hown; rfl
  irename Hnew => $H
  try wp_auto
  try isimp only at Hcs))

set_option hygiene false in
/-- `t.Register(new(M), ch)`. -/
macro "reg_oneR" : tactic => `(tactic| (
  wp_alloc_auto
  try wp_auto
  wp_apply rpc.wp_Register $$ [Ht] as Ht
  · iexact Ht
  try wp_auto
  try isimp only at Hcs))

theorem swift.initCs.wp_proofR : swift.initCs.specR (hG := hG) := by
  intro cs t v
  wp_start as ⟨Hcs, Ht⟩
  wp_auto
  mk_chR H1
  mk_chR H2
  mk_chR H3
  mk_chR H4
  mk_chR H5
  mk_chR H6
  mk_chR H7
  mk_chR H8
  mk_chR H9
  mk_chR H10
  mk_chR H11
  mk_chR H12
  mk_chR H13
  mk_chR H14
  reg_oneR
  reg_oneR
  reg_oneR
  reg_oneR
  reg_oneR
  reg_oneR
  reg_oneR
  reg_oneR
  reg_oneR
  reg_oneR
  reg_oneR
  reg_oneR
  reg_oneR
  reg_oneR
  iapply HΦ
  iexists _, _
  isplitl [Hcs]
  · iexact Hcs
  isplitl [Ht]
  · iExactEq Ht; rfl
  isplitl [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14]
  · unfold swift.csChans
    iframe
  ipureintro
  refine ⟨?_, ?_, rfl⟩
  · unfold swift.csCodes
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · unfold swift.tableIs swift.entryIs
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      try (simp (config := { decide := true }) only [GMap.lookup_insert_eq_iff, ↓reduceIte] <;>
        exact ⟨_, rfl⟩)
    intro c hc
    have key : ∀ (k : w8) (p : rpc.Pair') (M : GMap w8 rpc.Pair') (c : w8),
        ((<[k := p]> M) !! c).isSome → c = k ∨ (M !! c).isSome := by
      intro k p M c h
      by_cases hk : c = k
      · exact Or.inl hk
      · right; rwa [lookup_insert_ne _ _ (Ne.symm hk)] at h
    repeat (rcases key _ _ _ _ hc with rfl | hc; · decide)
    simp at hc

end proof

end Perennial.github_com.imdea_software.swiftpaxos
