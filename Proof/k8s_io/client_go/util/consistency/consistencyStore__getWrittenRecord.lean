/-
Proof of `Spec/k8s_io/client_go/util/consistency/consistencyStore__getWrittenRecord.lean`.
Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.consistency.consistencyStore__getWrittenRecord

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

theorem consistencyStore.getWrittenRecord.wp_proof :
    consistencyStore.getWrittenRecord.spec (GF := GF) (hG := hG) := by
  intro c γ T S G o Q
  wp_start as ⟨#Hc, Hrd, Hvs⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iNamed Hc
  wp_auto
  wp_apply wp_with_defer as %defer defer
  iunfold consReader at Hrd
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hrl, HP⟩
  iunfold writesP at HP
  icases HP with ⟨%W, Hm, Hg⟩
  wp_apply wp_map_lookup1 $$ [$Hm] as Hm
  imod Hvs $$ Hg with ⟨Hg, HQ⟩
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hm Hg]
  · iunfold writesP; iexists W; iframe
  iintro Hrd
  wp_auto
  iapply HΦ
  isplitl [Hrd]
  · iunfold consReader; iexact Hrd
  iexists W
  iframe HQ
  ipureintro; rfl

end proof

end consistency
end EtcdGrove
end Perennial
