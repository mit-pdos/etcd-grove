/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `setConfirmed` (as `setPre`'s).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setConfirmed
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

/-- `Forall₂` of two lists with one pair replaced. -/
theorem setConfirmed_forall₂_set {A B : Type} {R : A → B → Prop} :
    ∀ {l1 : List A} {l2 : List B}, List.Forall₂ R l1 l2 → ∀ (i : Nat) {a : A} {b : B}, R a b →
      List.Forall₂ R (l1.set i a) (l2.set i b)
  | _, _, .nil, _, _, _, _ => .nil
  | _, _, .cons _ hr, 0, _, _, hab => .cons hab hr
  | _, _, .cons h hr, i + 1, _, _, hab => .cons h (setConfirmed_forall₂_set hr i hab)

theorem setConfirmed.wp_proof : setConfirmed.spec (GF := GF) (hG := hG) := by
  intro a xs k v x
  wp_start as ⟨#Ha, %Hvx, %Hk⟩
  iunfold confirmedsRO at Ha
  icases Ha with ⟨%ps, #Hps, %Hpx⟩
  have Hl : ps.length = xs.length := Hpx.length_eq
  ihave %Hpl := ownSlice_len $$ Hps
  iapply wp_fupd
  wp_auto
  wp_apply wp_slice_make2 (V := G.Confirmed) a.len $$ [] as %out ⟨Hout, -⟩
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
  iunfold confirmedsRO
  iexists _
  iframe Hout
  ipureintro
  exact setConfirmed_forall₂_set Hpx _ Hvx

end proof

end AntCheck
end EtcdGrove
end Perennial
