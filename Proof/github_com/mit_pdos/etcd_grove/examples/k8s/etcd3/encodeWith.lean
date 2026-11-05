module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.encodeWith

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem encodeWith.wp_proof : encodeWith.spec (GF := GF) (hG := hG) := by
  intro tag name uid val
  wp_start
  (try wp_auto)
  wp_apply wp_string_to_bytes tag as %s0 ⟨Hs0, Hc0⟩
  (try wp_auto)
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %s1 ⟨Hs1, -⟩
  wp_apply wp_slice_append $$ [$Hs0 $Hc0 $Hs1] as %s2 ⟨Hs2, Hc2, -⟩
  (try wp_auto)
  wp_apply wp_string_to_bytes name as %s3 ⟨Hs3, -⟩
  wp_apply wp_slice_append $$ [$Hs2 $Hc2 $Hs3] as %s4 ⟨Hs4, Hc4, -⟩
  (try wp_auto)
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hlu
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %s7 ⟨Hs7, -⟩
  wp_apply wp_slice_append $$ [$Hs4 $Hc4 $Hs7] as %s8 ⟨Hs8, Hc8, -⟩
  (try wp_auto)
  wp_apply wp_string_to_bytes uid as %s9 ⟨Hs9, -⟩
  wp_apply wp_slice_append $$ [$Hs8 $Hc8 $Hs9] as %s10 ⟨Hs10, Hc10, -⟩
  (try wp_auto)
  wp_apply wp_string_to_bytes val as %s5 ⟨Hs5, -⟩
  wp_apply wp_slice_append $$ [$Hs10 $Hc10 $Hs5] as %s6 ⟨Hs6, -, -⟩
  (try wp_auto)
  iapply HΦ
  have h : sint.Z (W64 (name.length : Int)) = (name.length : Int) := by word
  have hu : sint.Z (W64 (uid.length : Int)) = (uid.length : Int) := by word
  rw [h, hu]
  unfold encodeWith
  iexact Hs6

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
