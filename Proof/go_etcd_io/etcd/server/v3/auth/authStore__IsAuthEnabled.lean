/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/authStore__IsAuthEnabled.lean`. Lean-first (no Rocq counterpart;
unit P2).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__IsAuthEnabled

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.IsAuthEnabled.wp_proof :
    auth.authStore.IsAuthEnabled.spec (GF := GF) (hG := hG) := by
  intro st R M
  wp_start as ⟨#Hinv, Hrd⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold authInv at Hinv
  icases Hinv with ⟨%Hst, -, -, -, -, -, -⟩
  iunfold enabledRd at Hrd
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hlk, HP⟩
  iunfold enabledP at HP
  icases HP with ⟨%b, Hb, #Hv, Hg⟩
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hb Hg] as Hrd
  · inext; iunfold enabledP; iexists b; iframe Hb Hg; iexact Hv
  iapply HΦ
  iunfold enabledRd
  iframe Hrd
  iexact Hv

end proof

end EtcdGrove
end Perennial
