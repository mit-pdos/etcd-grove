/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/tokenNop__renew.lean` (pr-verify etcd#22560, 2026-10-16).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.tokenNop__renew

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

theorem auth.tokenNop.renew.wp_proof :
    auth.tokenNop.renew.spec (GF := GF) (hG := hG) := fun t ctx tk rev => by
  wp_start
  ihave Hai : (authInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨-, -, -, -, -, -, -, #HAF, -⟩
  iunfold authErrVar at HAF
  icases HAF with ⟨%e, #He, -⟩
  wp_auto
  iapply HΦ
  iunfold errVarIs
  iexists e
  iframe #
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial
