/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/authStore__authInfoFromToken.lean`. Lean-first (no Rocq counterpart;
unit P2).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__authInfoFromToken
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__Revision

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.authInfoFromToken.wp_proof
    (h_Revision : auth.authStore.Revision.spec (GF := GF) (hG := hG)) :
    auth.authStore.authInfoFromToken.spec (GF := GF) (hG := hG) := by
  intro st R M ctx token
  wp_start as #Hinv
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, -, -, ⟨%tp, #Htp, #Htpok⟩, -, -⟩
  iunfold tokenProviderOk at Htpok
  icases Htpok with ⟨%Atp, %ti, %Hti, #Hinfo, -⟩
  subst Hti
  (try wp_auto)
  wp_apply (h_Revision st R M none) $$ [$Hinv] as %rev -
  · iunfold authOwnOpt; itrivial
  (try wp_auto)
  wp_apply Hinfo as %a %ok Ha
  iapply HΦ
  iexact Ha

end proof

end EtcdGrove
end Perennial
