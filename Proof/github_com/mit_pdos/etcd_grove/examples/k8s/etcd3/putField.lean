module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.putField

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

theorem putField.wp_proof : putField.spec (GF := GF) (hG := hG) := by
  intro sl out f
  wp_start as ⟨Hs, Hc⟩
  (try wp_auto)
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %s1 ⟨Hs1, -⟩
  wp_apply wp_slice_append $$ [$Hs $Hc $Hs1] as %s2 ⟨Hs2, Hc2, -⟩
  (try wp_auto)
  wp_apply wp_string_to_bytes f as %s3 ⟨Hs3, -⟩
  wp_apply wp_slice_append $$ [$Hs2 $Hc2 $Hs3] as %s4 ⟨Hs4, Hc4, -⟩
  (try wp_auto)
  iapply HΦ
  have h : sint.Z (W64 (f.length : Int)) = (f.length : Int) := by word
  rw [h]
  unfold putF
  iframe Hs4 Hc4

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
