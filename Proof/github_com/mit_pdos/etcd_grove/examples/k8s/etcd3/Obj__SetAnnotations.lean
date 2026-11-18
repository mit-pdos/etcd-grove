module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj__SetAnnotations

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

theorem Obj.SetAnnotations.wp_proof :
    Obj.SetAnnotations.spec (GF := GF) (hG := hG) := by
  intro p v m dq M
  wp_start as ⟨Hp, Hm⟩
  icases (typedPointsto_not_null_dup _ _ _) $$ Hp with ⟨Hp, %Hpn⟩
  iStructNamed Hp
  (try wp_auto)
  wp_apply (wp_map_lookup1 go.string go.string m M) $$ Hm as Hm
  iapply HΦ
  iframe Hm
  have hb : decide ((M !! go!"k8s.io/initial-events-end").getD (zero_val GoString) = go!"true") =
      decide (M !! go!"k8s.io/initial-events-end" = some go!"true") := by
    cases M !! go!"k8s.io/initial-events-end" <;> simp [zero_val]
  rw [hb]
  iapply typedPointsto_combine p _ (DFrac.own 1) Hpn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
