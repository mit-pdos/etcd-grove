/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/linkv3p/partitioner.lean` (the partition
plan's S3a, 2026-10-20; the client steps since 2026-10-21, `notes/client-cut-plan.md` K3).
Lean-first (no Rocq counterpart). The flags `holed` made all `false` (every bridge not blackholed:
its owner's flag); the range loop over the steps, each copied into the loop's variable;
`time.Sleep` (Perennial's spec: it returns); a peer step (`peerStep`) or a client step
(`clientStep`, which keeps each bridge's ownership with its flag as `holed` holds it) by the kind.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3p.partitioner
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3p.peerStep
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3p.clientStep
public import Perennial.Proof.time.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]

theorem partitioner.wp_proof
    (wp_peerStep : peerStep.spec (GF := GF) (hG := hG))
    (wp_clientStep : clientStep.spec (GF := GF) (hG := hG)) :
    partitioner.spec (GF := GF) (hG := hG) := by
  intro γn srvs brs sched ss bs steps
  wp_start as ⟨#Hsrvs, #Hbrs, #Hsched, #Hmem, Hown⟩
  ihave %Hbl := ownSlice_len $$ Hbrs
  ihave %Hstl := ownSlice_len $$ Hsched
  wp_auto
  wp_apply wp_slice_make2 (V := Bool) $$ [] as %hl ⟨Hhl, -⟩
  · ipureintro; word
  ihave Hown := (BigSepL2.bigSepL2_replicate_right (Φ := fun _ br h =>
    iprop(∃ addr : GoString, bridgeP.ownBridge (GF := GF) br addr h)) (l := bs) (x := false)).2 $$ Hown
  have hrep : List.replicate (sint.nat brs.len) (zero_val Bool) = List.replicate bs.length false := by
    rw [Hbl.1]; rfl
  rw [hrep]
  -- the loop over the steps: `i` the index, `st` the current step
  ihave HI : (∃ (j : w64) (st0 : github_com.mit_pdos.etcd_grove.examples.linkv3p.Step)
      (hs : List Bool),
      "i" ∷ i_ptr ↦ j ∗ "st" ∷ st_ptr ↦ st0 ∗ "Hhl" ∷ hl ↦* hs ∗
      "Hown" ∷ ([∗list] br; h ∈ bs; hs, ∃ addr : GoString, bridgeP.ownBridge br addr h) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sched.len⌝ : IProp GF) $$ [i st Hhl Hown]
  · iexists W64 0, _, _
    iframe
    ipureintro
    constructor
    · decide
    · have := Hstl.2; word
  wp_for HI
  wp_if_destruct
  · -- an iteration: the step `steps[j]`, copied into `st`, then its delay
    have Hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sched.len := ⟨Hj.1, Hif⟩
    simp only [Hb, _root_.and_self, ↓reduceIte]
    list_elem steps (sint.nat j) as stp
    wp_apply wp_load_slice_index _ (sint.Z j) steps _ stp Hj.1 $$ [] as -
    · iframe #; ipureintro; exact Hstp_lookup
    (try wp_auto)
    wp_apply time.wp_Sleep
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      wp_apply (wp_peerStep γn srvs ss _ _ _) $$ []
      · iframe #
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, _, hs
      iframe
      ipureintro; constructor <;> word
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      wp_apply (wp_peerStep γn srvs ss _ _ _) $$ []
      · iframe #
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, _, hs
      iframe
      ipureintro; constructor <;> word
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      wp_apply (wp_clientStep brs hl bs hs _ _) $$ [Hhl Hown] as ⟨%hs', Hhl, Hown⟩
      · iframe #; iframe
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, _, hs'
      iframe
      ipureintro; constructor <;> word
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      wp_apply (wp_clientStep brs hl bs hs _ _) $$ [Hhl Hown] as ⟨%hs', Hhl, Hown⟩
      · iframe #; iframe
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, _, hs'
      iframe
      ipureintro; constructor <;> word
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      wp_apply (wp_clientStep brs hl bs hs _ _) $$ [Hhl Hown] as ⟨%hs', Hhl, Hown⟩
      · iframe #; iframe
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, _, hs'
      iframe
      ipureintro; constructor <;> word
    (try wp_auto)
    wp_for_post
    iframe
    iexists j + W64 1, _, hs
    iframe
    ipureintro; constructor <;> word
  · iapply HΦ
    itrivial

end proof

end linkv3p
end EtcdGrove
end Perennial
