/- Lean-first (no Rocq counterpart). The proof of `toHS`: the three cells (`newU64`), the struct split
into its fields, the cells frozen and the hidden fields made into raft's `protobuf` invariant
(`pbMsg_alloc`), as `walRaftP.ZeroLaw`'s proof does for `&raftpb.HardState{}`. -/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.toHS
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.newU64

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3 WalEnc WalFs
open github_com.mit_pdos.etcd_grove.examples.etcd.wal

section pure
variable [GooseExts]

/-- `toHS(h)`'s wire content: the three cells set. -/
def tHsC (h : THs) : WalHsC := ⟨some h.term', some h.vote', some h.commit', []⟩

theorem tHsC_canon (h : THs) : hsEmptyP (absHs h) ∨ tHsC h = walHsCanon (absHs h) := by
  unfold walHsCanon
  split
  · left; assumption
  · right; rfl

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

theorem toHS.wp_proof (wp_newU64 : newU64.spec (GF := GF) (hG := hG)) :
    toHS.spec (GF := GF) (hG := hG) := by
  intro h
  wp_start
  try wp_auto
  wp_apply wp_newU64 as %pt Hpt
  try wp_auto
  wp_apply wp_newU64 as %pv Hpv
  try wp_auto
  iapply wp_fupd
  wp_apply wp_newU64 as %pc Hpc
  try wp_auto
  ihave %Hnn := typedPointsto_not_null $$ «$r0»
  icases typedPointsto_split _ _ _ $$ «$r0» with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨Hst, HT, HV, HC, Huf, Hsc, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HT with #HT
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HV with #HV
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HC with #HC
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hpt with #Hpt
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hpv with #Hpv
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hpc with #Hpc
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod (pbMsg_alloc raftpb.HardState «$r0_ptr» _ _ _ [] ⊤ (ufWire_nil _)) $$ [Hst Hsc Huf Hnil] with #Hpb
  · iframe
  imodintro
  iapply HΦ
  simp only [walRaftP]
  unfold walHsIn
  iright
  iexists tHsC h
  unfold hsRoC hsCells
  simp only [tHsC]
  iframe Hpb
  isplitl
  · iexists pt, pv, pc
    iframe HT HV HC
    unfold optCell
    iframe Hpt Hpv Hpc
    ipureintro; exact Hnn
  · ipureintro; exact ⟨rfl, tHsC_canon h⟩

end proof

end etcd_wal
end EtcdGrove
end Perennial
