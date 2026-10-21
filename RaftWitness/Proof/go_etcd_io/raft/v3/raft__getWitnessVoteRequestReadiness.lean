/-
`(*raft).getWitnessVoteRequestReadiness` (2026-10-19, witness support; 2026-10-20 at any
configuration): the witnesses read `[c.wit, 0]` (`raft.wp_load_trk_witnessC'`).
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raft__getWitnessVoteRequestReadiness
public import RaftWitness.Proof.go_etcd_io.raft.v3.LemmasWitnessR

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

-- `w1 := r.trk.Witnesses[0]; w2 := r.trk.Witnesses[1]`: `c.wit` and `0`
set_option hygiene false in
local macro "gw_rest" : tactic => `(tactic| (
  wp_apply raft.wp_load_trk_witnessC' c r id s (W64 0) (by decide) $$ Hphys as Hphys
  try wp_auto
  wp_apply raft.wp_load_trk_witnessC' c r id s (W64 1) (by decide) $$ Hphys as Hphys
  rw [witOf_zero, witOf_one]
  try wp_auto
  by_cases hw : c.wit = W64 0
  · -- no witness: `return nil`
    rw [decide_eq_true hw]
    try wp_auto
    iapply HΦ
    iframe Hphys
    ileft; ipureintro; exact ⟨rfl, Or.inl hw⟩
  rw [decide_eq_false hw]
  try wp_auto
  wp_apply wp_map_make1 (K := w64) (V := Bool) as %wm Hwm
  try wp_auto
  -- `w1 == w2`: no (`c.wit ≠ 0`)
  rw [decide_eq_false hw]
  try wp_auto
  -- `w1 > 0`: `w[w1] = v1 == 1`
  rw [decide_eq_true (by have : uint.Z c.wit ≠ 0 := fun h => hw (by word); word)]
  try wp_auto
  wp_apply wp_mapInsert $$ Hwm as Hwm
  try wp_auto
  -- `w2 > 0`: no
  try wp_auto
  iapply HΦ
  iframe Hphys
  iright
  iexists _
  iframe Hwm
  ipureintro
  refine ⟨hw, ?_⟩
  simp))

theorem raft.getWitnessVoteRequestReadiness.wp_proof :
    raft.getWitnessVoteRequestReadiness.spec (GF := GF) (hG := hG) := by
  intro c V r id s d v1 v2 Hd
  wp_start as Hphys
  wp_auto
  -- `v1 := votesToWin[0]; v2 := votesToWin[1]`
  icases array_acc_same _ (sint.Z (W64 0)) _ _ _ v1 (by decide) (by rw [Hd]; rfl)
    $$ votesToWin with ⟨Hv0, Hv0back⟩
  wp_auto
  ihave votesToWin := Hv0back $$ Hv0
  icases array_acc_same _ (sint.Z (W64 1)) _ _ _ v2 (by decide) (by rw [Hd]; rfl)
    $$ votesToWin with ⟨Hv1, Hv1back⟩
  wp_auto
  ihave votesToWin := Hv1back $$ Hv1
  -- `if v1 > 1 && v2 > 1 { return nil }`
  by_cases h1 : sint.Z (W64 1) < sint.Z v1
  · rw [decide_eq_true h1]
    wp_auto
    by_cases h2 : sint.Z (W64 1) < sint.Z v2
    · rw [decide_eq_true h2]
      wp_auto
      iapply HΦ
      iframe Hphys
      ileft; ipureintro
      exact ⟨rfl, Or.inr ⟨by simpa using h1, by simpa using h2⟩⟩
    · rw [decide_eq_false h2]
      wp_auto
      gw_rest
  · rw [decide_eq_false h1]
    wp_auto
    gw_rest

end proof

end EtcdGrove
end Perennial
