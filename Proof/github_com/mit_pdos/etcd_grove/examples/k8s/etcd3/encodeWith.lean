module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.encodeWith
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

theorem encodeWith.wp_proof (wp_putField : putField.spec (GF := GF) (hG := hG)) :
    encodeWith.spec (GF := GF) (hG := hG) := by
  intro tag v
  wp_start
  (try wp_auto)
  wp_apply wp_string_to_bytes tag as %s0 ⟨Hs0, Hc0⟩
  (try wp_auto)
  wp_apply wp_putField $$ [$Hs0 $Hc0] as %s1 ⟨Hs1, Hc1⟩
  (try wp_auto)
  wp_apply wp_putField $$ [$Hs1 $Hc1] as %s2 ⟨Hs2, Hc2⟩
  (try wp_auto)
  wp_apply wp_putField $$ [$Hs2 $Hc2] as %s3 ⟨Hs3, Hc3⟩
  (try wp_auto)
  wp_apply wp_putField $$ [$Hs3 $Hc3] as %s4 ⟨Hs4, Hc4⟩
  (try wp_auto)
  wp_apply wp_putField $$ [$Hs4 $Hc4] as %s5 ⟨Hs5, Hc5⟩
  (try wp_auto)
  wp_apply wp_string_to_bytes v.Value' as %s6 ⟨Hs6, -⟩
  wp_apply wp_slice_append $$ [$Hs5 $Hc5 $Hs6] as %s7 ⟨Hs7, -, -⟩
  (try wp_auto)
  iapply HΦ
  unfold encodeWith
  iexact Hs7

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
