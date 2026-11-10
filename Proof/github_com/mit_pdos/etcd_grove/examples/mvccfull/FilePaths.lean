/- Lean-first (no Rocq counterpart). The proof of `FilePaths` (the loop over the snapshots): Draft, to come. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.FilePaths
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.memberPath
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.buildPath

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

theorem FilePaths.wp_proof
    (wp_memberPath : memberPath.spec (GF := GF) (hG := hG))
    (wp_buildPath : buildPath.spec (GF := GF) (hG := hG)) :
    FilePaths.spec (GF := GF) (hG := hG) := by
  intro cfg hops
  wp_start
  wp_auto
  wp_apply wp_memberPath cfg.Prefix' (W64 0) (by decide)
  wp_apply wp_memberPath cfg.Prefix' (W64 1) (by decide)
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, Hcap⟩
  (try wp_auto)
  rw [show ([memberPathM cfg.Prefix' 0, zero_val GoString].set (sint.nat (W64 (0 + 1)))
      (memberPathM cfg.Prefix' 1)) = [memberPathM cfg.Prefix' 0, memberPathM cfg.Prefix' 1] from rfl]
  generalize (slice.mk sl _ _ : GoSlice) = s0
  ihave IH : (∃ (nv : w64) (s : GoSlice),
      "n" ∷ n_ptr ↦ nv ∗ "ps" ∷ ps_ptr ↦ s ∗
      "Hsl" ∷ s ↦* ([memberPathM cfg.Prefix' 0, memberPathM cfg.Prefix' 1] ++
        (List.range' 1 (sint.nat nv - 1)).map (buildPathM cfg.Prefix')) ∗
      "Hcap" ∷ ownSliceCap GoString s (DFrac.own 1) ∗ "cfg" ∷ cfg_ptr ↦ cfg ∗
      "%Hn" ∷ ⌜1 ≤ sint.Z nv ∧ sint.Z nv ≤ max (sint.Z cfg.Ops') 0 + 1⌝ : IProp GF)
      $$ [n ps Hsl Hcap cfg]
  · iexists W64 1, s0
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · wp_apply wp_buildPath cfg.Prefix' nv (by word)
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %osl ⟨Hosl, -⟩
    (try wp_auto)
    wp_apply wp_slice_append $$ [$Hsl $Hcap $Hosl] as %s1 ⟨Hsl, Hcap, -⟩
    (try wp_auto)
    wp_for_post
    iframe
    iexists nv + W64 1, s1
    iframe
    have h1 : sint.nat (nv + W64 1) - 1 = (sint.nat nv - 1) + 1 := by word
    rw [h1, List.range'_concat, List.map_append, ← List.append_assoc]
    rw [show 1 + 1 * (sint.nat nv - 1) = sint.nat nv by word]
    iframe
    ipureintro; constructor <;> word
  · (try wp_auto)
    iapply HΦ
    unfold filePathsM
    rw [show sint.nat nv - 1 = sint.nat cfg.Ops' by word]
    iframe

end proof

end mvccfull
end EtcdGrove
end Perennial
