/-
`status.FromError` of an error grpc accepts, and the `Code()` and `Message()` of the `*Status` it
returns: proved over grpc's translated `status` and `internal/status` (status-bodies, 2026-11-25; until
then a trust-boundary axiom). See `Spec/google_golang_org/grpc/status/FromError.lean`.
-/
module

public import Spec.google_golang_org.grpc.status.FromError
public import Spec.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError__Error
public import Proof.google_golang_org.grpc.internal.status.Methods

@[expose] public section

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
variable [rpctypes_sem : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]

/-- `status.FromError` (`status/status.go:96-127`): `nil` gives `(nil, true)`; an error whose type
has `GRPCStatus() *Status` (a `*status.Error`, `grpcStatusIs`) the status it holds and `true`; any
other (a leaf, so `errors.As` finds nothing) `New(Unknown, err.Error())` and `false`. -/
theorem status.FromError.wp_proof
    (wp_EtcdErrorError : rpctypes.EtcdError.Error.spec (GF := GF) (hG := hG)) :
    status.FromError.spec (GF := GF) (hG := hG) := by
  intro err m c
  wp_start as ⟨#Hok, #Hd, #Hc⟩
  cases err with
  | nil =>
    wp_auto
    ihave %hc := statusCodeIs_nil_eq c $$ Hc
    ihave %hm := descIs_nil_eq m $$ Hd
    subst hc hm
    iapply HΦ
    isplitr
    · ipureintro; intro; rfl
    isplitr
    · iintro !> %Ψ HΨ
      wp_apply wp_Status_Code_nil
      iapply HΨ
    isplitr
    · iintro !> %Ψ HΨ
      wp_apply wp_Status_Message_nil
      iapply HΨ
    isplitr
    · iintro !> %e' %h
      exact absurd h.2 nofun
    isplitr
    · ipureintro; intro e' h; cases h
    · ipureintro; rintro ⟨e', h, -⟩; cases h
  | ok e =>
    by_cases hg : methodSet e.ty !! go!"GRPCStatus" = some grpcStatusSig
    · ihave ⟨%s, %c', #Hgd⟩ := descIs_GRPC e m hg $$ Hd
      ihave ⟨%s', %m', #Hgc⟩ := statusCodeIs_GRPC e c hg $$ Hc
      ihave %hag := status.grpcStatusIs_agree _ _ _ _ _ _ _ $$ Hgd Hgc
      obtain ⟨rfl, rfl, rfl⟩ := hag
      ihave #Hw := status.grpcStatusIs_wp _ _ _ _ $$ Hgd
      ihave #Hro := status.grpcStatusIs_statusAt _ _ _ _ $$ Hgd
      ihave %hsn := status.statusAt_nonnull _ _ _ $$ Hro
      wp_auto
      rw [typeSetContains_grpcstatus, decide_eq_true hg]
      simp only [↓reduceIte]
      wp_auto
      wp_apply Hw
      rw [decide_eq_false hsn]
      wp_auto
      iapply HΦ
      isplitr
      · ipureintro; intro; rfl
      isplitr
      · iintro !> %Ψ HΨ
        wp_apply (wp_Status_Code_ro s c' m) $$ [Hro]
        · iexact Hro
        iapply HΨ
      isplitr
      · iintro !> %Ψ HΨ
        wp_apply (wp_Status_Message_ro s c' m) $$ [Hro]
        · iexact Hro
        iapply HΨ
      isplitr
      · iintro !> %e' %h
        exact absurd h.1 nofun
      isplitr
      · ipureintro; intro e' h hne; cases h; exact absurd hg hne
      · ipureintro; intro; rfl
    · have hts : go.typeSetContains e.ty google_golang_org.grpc.status.grpcstatus.ty = false := by
        rw [typeSetContains_grpcstatus]; simpa using hg
      ihave %hc := statusCodeIs_noGRPC_eq e c hg $$ Hc
      subst hc
      ihave #HE : (□ ∀ Ψ : val → IProp GF, ▷ Ψ #m -∗
          WP (App (Val #(methods e.ty go!"Error" e.v)) (Val #())) {{ Ψ }}) $$ []
      · ihave #Hdn := descIs_noGRPC e m hg $$ Hd
        icases Hdn with (%hx | #Hm)
        · obtain ⟨x, hx, rfl⟩ := hx
          simp only [interface.mkOk] at hx
          injection hx with hx
          subst hx
          iintro !> %Ψ HΨ
          wp_apply wp_EtcdErrorError
          iapply HΨ
        · unfold errorMsgIs
          iexact Hm
      ihave %hleaf : ⌜_root_.Perennial.errors.isLeafError e⌝ $$ [Hok]
      · unfold statusErrOk
        icases Hok $$ %e %rfl with ⟨-, %hl, -⟩
        ipureintro; exact hl
      wp_auto
      rw [hts]
      simp only [Bool.false_eq_true, ↓reduceIte]
      wp_auto
      ihave #Herr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
      · iPkgInit
      have hT : _root_.Perennial.errors.AsTarget google_golang_org.grpc.status.grpcstatus.ty := by
        left; rw [go.is_underlying (t := google_golang_org.grpc.status.grpcstatus.ty)]; exact ⟨_, rfl⟩
      wp_apply (_root_.Perennial.errors.wp_As.2.2 0 (GoInterface.ok e) gs_ptr GoInterface.nil hT)
        $$ [gs] as gs
      · iframe gs
        simp only [_root_.Perennial.errors.asNoMatch]
        ipureintro
        right
        refine ⟨e, rfl, hleaf, ?_, ?_⟩
        · unfold _root_.Perennial.errors.asAssignable
          rw [grpcstatus_isInterface]; simpa using hts
        · intro h; rw [grpcstatus_isInterface] at h; cases h
      wp_apply HE
      wp_apply wp_status_New as %st #Hst
      iapply HΦ
      isplitr
      · ipureintro; intro h; cases h
      isplitr
      · iintro !> %Ψ HΨ
        wp_apply (wp_Status_Code_ro st (W32 2) m) $$ [Hst]
        · iexact Hst
        iapply HΨ
      isplitr
      · iintro !> %Ψ HΨ
        wp_apply (wp_Status_Message_ro st (W32 2) m) $$ [Hst]
        · iexact Hst
        iapply HΨ
      isplitr
      · iintro !> %e' %h
        obtain ⟨-, he⟩ := h
        cases he
        iexact HE
      isplitr
      · ipureintro; intros; rfl
      · ipureintro; rintro ⟨e', he, hg'⟩; cases he; exact absurd hg' hg

end proof

end EtcdGrove
end Perennial
