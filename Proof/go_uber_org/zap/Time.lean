/-
Proof of `Spec/go_uber_org/zap/Time.lean` (srvloops2, 2026-11-21): `val.Before(_minTimeInt64) ||
val.After(_maxTimeInt64)` (the bounds zap's fact holds), then a field of `val.UnixNano()` and
`val.Location()`, or of `val` itself. Lean-first.
-/
module

public import Spec.go_uber_org.zap.Time

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_uber_org

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_uber_org.zap.Assumptions]

theorem zap.Time.wp_proof : zap.Time.spec (GF := GF) (hG := hG) := by
  intro k v
  wp_start as #Hpkg
  ihave ⟨%tmin, %tmax, #Hmin, #Hmax⟩ : (iprop(∃ tmin tmax : _root_.Perennial.time.Time,
      typedPointsto (globalAddr _root_.Perennial.go_uber_org.zap._minTimeInt64) tmin DFrac.discard ∗
      typedPointsto (globalAddr _root_.Perennial.go_uber_org.zap._maxTimeInt64) tmax DFrac.discard) :
      IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  ihave #Ptime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  wp_auto
  wp_apply _root_.Perennial.time.Time.wp_ptr_Before $$ [$val] as %b1 val
  cases b1
  · wp_auto
    wp_method_call
    wp_call
    (try wp_auto)
    wp_apply _root_.Perennial.time.Time.wp_After
    generalize (_root_.Perennial.time.Time.after _ _) = b2
    (try wp_auto)
    cases b2
    · wp_auto
      wp_apply (_root_.Perennial.time.Time.wp_ptr_UnixNano val_ptr v) $$ [$val] as %ns val
      (try wp_auto)
      wp_method_call
      wp_call
      (try wp_auto)
      wp_apply _root_.Perennial.time.Time.wp_Location as %loc -
      (try wp_auto)
      iapply HΦ
      itrivial
    · wp_auto
      iapply HΦ
      itrivial
  · wp_auto
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
