/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Set__Union`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set__Union
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.NewSet

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

theorem Set.Union.wp_proof (wp_NewSet : NewSet.spec (GF := GF) (hG := hG)) :
    Set.Union.spec (GF := GF) (hG := hG) := by
  intro sl s tl t
  wp_start as ⟨#Hs, #Ht⟩
  iunfold setRO at Hs Ht
  icases Hs with ⟨%xs, #Hxs, %Hxm⟩
  icases Ht with ⟨%ys, #Hys, %Hym⟩
  wp_auto
  ihave #Hnil := ownSlice_nil (V := w64) (GF := GF) (DFrac.own 1)
  ihave Hcap0 := ownSliceCap_nil (V := w64) (GF := GF)
  wp_apply wp_slice_append slice.nil [] sl xs DFrac.discard $$ [Hnil Hcap0 Hxs] as %s1 ⟨Hs1, Hcap1, -⟩
  · iframe Hnil Hcap0 Hxs
  try wp_auto
  wp_apply wp_slice_append s1 _ tl ys DFrac.discard $$ [Hs1 Hcap1 Hys] as %s2 ⟨Hs2, -, -⟩
  · iframe Hs1 Hcap1 Hys
  try wp_auto
  imod ownSlice_persist $$ Hs2 with #Hs2
  wp_apply wp_NewSet s2 _ $$ [Hs2] as %u #Hu
  · iexact Hs2
  try wp_auto
  iapply HΦ
  have : SetIds.mk ((([] ++ xs) ++ ys).map (fun x => uint.nat x)) = s.union t := by
    rw [List.nil_append, List.map_append, Hxm, Hym]; rfl
  rw [← this]
  iexact Hu

end proof

end Etcdraft
end EtcdGrove
end Perennial
