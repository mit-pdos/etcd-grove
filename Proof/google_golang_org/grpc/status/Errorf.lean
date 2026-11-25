/-
`status.Errorf(c, format)` with no arguments and a format without `%`: proved over grpc's translated
`status` (status-bodies, 2026-11-25; until then a trust-boundary axiom), over `status.Error`'s spec and
Perennial's `fmt.Sprintf`. See `Spec/google_golang_org/grpc/status/Errorf.lean`.
-/
module

public import Spec.google_golang_org.grpc.status.Errorf
public import Spec.google_golang_org.grpc.status.Error
public import Perennial.Proof.fmt

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [status_sem : google_golang_org.grpc.status.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `status.Errorf(c, format)` (`status/status.go:63-65`): `Error(c, fmt.Sprintf(format))`, and
`Sprintf` of a format without `%` and no arguments returns it. -/
theorem status.Errorf.wp_proof
    (wp_Sprintf : _root_.Perennial.fmt.Sprintf.spec (GF := GF) (hG := hG))
    (wp_Error : status.Error.spec (GF := GF) (hG := hG)) :
    status.Errorf.spec (GF := GF) (hG := hG) := by
  intro c format
  wp_start as %h
  obtain ⟨hc, hf⟩ := h
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_auto
  wp_apply (wp_Sprintf format [.lit format] slice.nil [] [] (DFrac.own 1)
      (by simp [_root_.Perennial.fmt.encode, _root_.Perennial.fmt.Piece.encode])
      (.lit _ _ _ hf .nil)) $$ [] as %r ⟨-, -, %hr⟩
  · isplitl
    · iapply ownSlice_nil
    · iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
  have hr' : r = format := by
    cases hr with
    | lit _ _ _ out h => cases h; simp
  subst hr'
  wp_apply (wp_Error c r) $$ [] as %err ⟨%h1, #H2, #H3, %h4, %h5, #H6, %h7⟩
  · ipureintro; exact hc
  iapply HΦ
  iframe H2 H3 H6
  ipureintro; exact ⟨h1, h4, h5, h7⟩

end proof

end EtcdGrove
end Perennial
