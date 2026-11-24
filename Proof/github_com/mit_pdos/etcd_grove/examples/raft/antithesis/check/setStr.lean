/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `setStr` (as `setPre`'s).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setStr
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

theorem setStr.wp_proof : setStr.spec (GF := GF) (hG := hG) := by
  intro a ps k v
  wp_start as ⟨#Ha, %Hk⟩
  iunfold strsRO at Ha
  ihave #Hps := Ha
  have Hl : ps.length = ps.length := rfl
  ihave %Hpl := ownSlice_len $$ Hps
  iapply wp_fupd
  wp_auto
  wp_apply wp_slice_make2 (V := Str) a.len $$ [] as %out ⟨Hout, -⟩
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
  iunfold strsRO
  iexact Hout

end proof

end AntCheck
end EtcdGrove
end Perennial
