/-
**The no-op token provider meets the token provider's contract** (`tokenNop`, `nop.go`; the auth
plan's S5, 2026-10-24; `notes/decisions.md`, "S5 of the auth plan"). Lean-first (no Rocq
counterpart).

`tokenNop` (what `NewTokenProvider` returns for an empty token option; etcd's server defaults
to the simple provider) accepts no token (`info` returns `nil, false`) and issues none (`assign` returns
`ErrAuthFailed`; `genTokenPrefix` returns `""`), so it meets the contract in every mode: the binding holds vacuously. This is the
contract's sanity check; the simple and JWT providers are not proved yet.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth

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

/-- **`tokenNop` meets the contract** in every mode `M`, for any receiver `p`. -/
theorem auth.tokenNop_ok (p : Loc) (M : AuthMode) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ⊢
      tokenProviderOk (interface.mkOk (go.GoType.PointerType tokenNop.ty) #p) M := by
  iintro #Hpkg
  icases authErrVar_of_init .authFailed $$ Hpkg with ⟨%eAF, #HeAF⟩
  simp only [AuthErr.var]
  iunfold tokenProviderOk
  iexists (iprop(True) : IProp GF), _
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> %ctx %token %rev %Φ !> - HΦ
    wp_method_call; wp_call
    (try wp_auto)
    iapply HΦ
    isplitr
    · iunfold authInfoRO; ileft; ipureintro; rfl
    simp only [Bool.false_eq_true, ite_false]
    itrivial
  isplitr
  · iintro !> %Φ !> - HΦ
    wp_method_call; wp_call
    (try wp_auto)
    iapply HΦ; itrivial
  isplitr
  · iintro !> %Φ !> - HΦ
    wp_method_call; wp_call
    (try wp_auto)
    iapply HΦ; itrivial
  isplitr
  · iintro !> %name %Φ !> - HΦ
    wp_method_call; wp_call
    (try wp_auto)
    iapply HΦ; itrivial
  isplitr
  · iintro !> %ctx %user %rev %Φ !> - HΦ
    wp_method_call; wp_call
    (try wp_auto)
    iapply HΦ
    iright
    isplitr
    · ipureintro; simp
    iexists .authFailed
    iunfold authErrOf
    iexists eAF
    simp only [AuthErr.var]
    iframe HeAF
  · iintro !> %Φ !> - HΦ
    wp_method_call; wp_call
    (try wp_auto)
    iapply HΦ; ipureintro; exact ⟨rfl, by simp [tokPrefixOk]⟩

end proof

end EtcdGrove
end Perennial
