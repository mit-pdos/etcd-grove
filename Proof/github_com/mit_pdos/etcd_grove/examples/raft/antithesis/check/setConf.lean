/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `setConf` (as `setPre`'s).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setConf
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem setConf.wp_proof : setConf.spec (GF := GF) (hG := hG) := by
  intro a us k v u
  wp_start as ⟨#Ha, #Hv, %Hk⟩
  iunfold confsRO at Ha
  icases Ha with ⟨%ps, #Hps, #Hpu⟩
  ihave %Hpl := ownSlice_len $$ Hps
  ihave %Hl := BigSepL2.bigSepL2_length $$ Hpu
  iapply wp_fupd
  wp_auto
  wp_apply wp_slice_make2 (V := G.Conf) a.len $$ [] as %out ⟨Hout, -⟩
  · ipureintro; exact Hpl.2
  try wp_auto
  wp_apply wp_slice_copy out _ a ps DFrac.discard $$ [Hout Hps] as %c ⟨-, Hout, -⟩
  · iframe Hout Hps
  rw [copy_full ps _ _ Hpl.1] 
  try wp_auto
  ihave %Hol := ownSlice_len $$ Hout
  have hko : sint.Z k < sint.Z out.len := by have := Hk.2; rw [← Hl, Hol.1] at this; word
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z out.len from ⟨Hk.1, hko⟩))]
  wp_apply wp_store_slice_index out (sint.Z k) ps v $$ [Hout] as Hout
  · iframe Hout; ipureintro; exact ⟨Hk.1, by rw [Hl]; exact Hk.2⟩
  try wp_auto
  imod ownSlice_persist $$ Hout with #Hout
  imodintro
  iapply HΦ
  iunfold confsRO
  iexists _
  iframe Hout
  iapply bigSepL2_set (fun p u => confRO (GF := GF) p u) ps us _ v u (by have := Hk.2; word)
  iframe Hpu Hv

end proof

end AntCheck
end EtcdGrove
end Perennial
