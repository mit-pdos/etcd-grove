/-
Proof of `Spec/k8s_io/client_go/util/consistency/consistencyStore__WroteAt.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.consistency.consistencyStore__WroteAt
public import Spec.k8s_io.client_go.util.consistency.consistencyStore__ensureWrittenRecord
public import Spec.k8s_io.client_go.util.consistency.ownerRecord__WroteAt

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace consistency

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.consistency

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.consistency.Assumptions]

theorem consistencyStore.WroteAt.wp_proof
    (wp_ensureWrittenRecord : consistencyStore.ensureWrittenRecord.spec (GF := GF) (hG := hG))
    (wp_recWroteAt : ownerRecord.WroteAt.spec (GF := GF) (hG := hG)) :
    consistencyStore.WroteAt.spec (GF := GF) (hG := hG) := by
  intro c γ T S G o uid gr rv q
  iintro %Φ ⟨#Hpkg, #Hc, HT, Hrd⟩ HAU
  ihave #Hc' := Hc
  iNamed Hc'
  wp_method_call
  wp_call
  wp_auto
  wp_bind
  iapply (wp_ensureWrittenRecord c γ T S G o uid gr rv q) $$ [$Hpkg $Hc $HT $Hrd]
  inext
  imod HAU with ⟨%M, HM, Hcl⟩
  imodintro
  iexists M
  iframe HM
  iintro HM'
  imod Hcl $$ HM' with HΦ
  imodintro
  iintro %r ⟨Hrd, %s, %id, #Hrec, %ho, Htok⟩
  subst ho
  wp_pures
  wp_bind
  iapply (wp_recWroteAt γ T r s id gr rv q) $$ [$Hpkg $Hinv $Hexcl $Hrec $Htok]
  inext
  iintro HT
  wp_auto
  iapply HΦ
  iframe

end proof

end consistency
end EtcdGrove
end Perennial
