/-
Lemmas of `node.run`'s proof (raft v3.7 retarget, stage R5): the removed-node check reads the
`Voters` and `VotersOutgoing` fields of the fresh `*pb.ConfState` `applyConfChange` returns
(`csPts`, `InvPb.lean`), which then goes whole to `confstatec`.
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A conf state's `Voters` and `VotersOutgoing` fields and slices, out of `csPts` and back. -/
theorem csPts_voters (p : Loc) (dq : DFrac) (c : ConfStateM) (al : Bool) :
    csPts (GF := GF) p dq c al ⊢ ∃ sv so : GoSlice,
      p.[raftpb.ConfState, go!"Voters"] ↦{dq} sv ∗ sv ↦*{dq} c.Voters' ∗
      p.[raftpb.ConfState, go!"VotersOutgoing"] ↦{dq} so ∗ so ↦*{dq} c.VotersOutgoing' ∗
      (p.[raftpb.ConfState, go!"Voters"] ↦{dq} sv -∗ sv ↦*{dq} c.Voters' -∗
       p.[raftpb.ConfState, go!"VotersOutgoing"] ↦{dq} so -∗ so ↦*{dq} c.VotersOutgoing' -∗
       csPts p dq c al) := by
  iintro H
  iunfold csPts at H
  icases H with ⟨%sv, %sl, %so, %sn, %pa, %pw, %pwo, %Hnn, H⟩
  iNamed H
  iexists sv, so
  iframe HV Hv HO Ho
  iintro HV Hv HO Ho
  iunfold csPts
  iexists sv, sl, so, sn, pa, pw, pwo
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cA cW cWO Hpb
  ipureintro; exact Hal

/-- One of the two voter slices (`for _, sl := range [][]uint64{cs.Voters, cs.VotersOutgoing}`),
at position `j` of the literal, lent out of both. -/
theorem voters_pick (sv so : GoSlice) (dq : DFrac) (xs os : List w64) (j : w64)
    (Hj : j = W64 0 ∨ j = W64 1) :
    (sv ↦*{dq} xs : IProp GF) -∗ so ↦*{dq} os -∗
      ∃ (v : GoSlice) (vs : List w64), ⌜[sv, so][(sint.Z j).toNat]? = some v⌝ ∗ v ↦*{dq} vs ∗
        (v ↦*{dq} vs -∗ sv ↦*{dq} xs ∗ so ↦*{dq} os) := by
  iintro Hv Ho
  rcases Hj with rfl | rfl
  · iexists sv, xs
    iframe Hv
    isplitr
    · ipureintro; rfl
    iintro Hv
    iframe Hv Ho
  · iexists so, os
    iframe Ho
    isplitr
    · ipureintro; rfl
    iintro Ho
    iframe Hv Ho

end lemmas

end EtcdGrove
end Perennial
