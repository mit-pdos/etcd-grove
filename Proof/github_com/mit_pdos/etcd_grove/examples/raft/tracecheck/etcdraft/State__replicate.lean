/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__replicate`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__replicate
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__mut

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

theorem State.replicate.wp_proof (wp_mut : State.mut.spec (GF := GF) (hG := hG)) :
    State.replicate.spec (GF := GF) (hG := hG) := by
  intro p st M i gv w typ
  wp_start as ⟨Hst, #Hv, %Hi⟩
  wp_auto
  mut_open p, st, M, i
  iunfold logRO at Hcl
  icases Hcl with ⟨%es, #Hes, #Hel⟩
  ihave %Hesl := ownSlice_wf $$ Hes
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; exact Hesl.1, Int.le_refl _, Hesl.2⟩)]
  ihave #Hfs := ownSlice_fullSlice_len _ _ _ $$ Hes
  ihave Hfcap := ownSliceCap_empty (V := G.Entry) (GF := GF)
    (slice.fullSlice gc.Log' G.Entry (W64 0) gc.Log'.len gc.Log'.len) (by simp [slice.fullSlice])
    (by simp only [slice.fullSlice]; rw [show gc.Log'.len - W64 0 = gc.Log'.len by word]; exact Hesl.1)
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl0 ⟨Hsl0, -⟩
  wp_apply wp_slice_append_persistent _ es _ _ (DFrac.own 1) $$ [Hfs Hfcap Hsl0] as %s2 ⟨#Hs2, -, -⟩
  · iframe Hsl0
    isplitr
    · iexact Hfs
    iexact Hfcap
  try wp_auto
  ihave #Hcl : logRO (GF := GF) s2 ((st.s (uint.nat i)).log ++ [{ term := (st.s (uint.nat i)).currentTerm, type := typ, value := w }]) $$ []
  · iunfold logRO
    iexists _
    iframe Hs2
    iapply (BigSepL2.bigSepL2_snoc).2
    iframe Hel
    iunfold entryRO
    iframe Hv
    ipureintro; exact ⟨Hcf.1, rfl⟩
  close_copy { gc with Log' := s2 },
    (fun v => { v with log := v.log ++ [{ term := v.currentTerm, type := typ, value := w }] }), Hcf
  iapply HΦ; unfold State.replicate; iexact Hs

end proof

end Etcdraft
end EtcdGrove
end Perennial
