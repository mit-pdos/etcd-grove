/-
`status.Error(c, msg)` for a code other than `OK`: proved over grpc's translated `status` and
`internal/status` (prove-statuserror, 2026-11-26; until then a trust-boundary axiom), over
`fmt.Sprintf`, `codes.Code.String` and `proto.Equal` of two `*spb.Status` (an axiom). See
`Spec/google_golang_org/grpc/status/Error.lean`.
-/
module

public import Spec.google_golang_org.grpc.status.Error
public import Proof.google_golang_org.grpc.internal.status.ErrorMethods

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

/-- `status.Error(c, msg)` (`status/status.go:58-60`): `New(c, msg).Err()`, which for `c ≠ OK` is
`&Error{s: s}` (`internal/status/status.go:125-130`) of the fresh read-only status `s`. -/
theorem status.Error.wp_proof
    (wp_Sprintf : _root_.Perennial.fmt.Sprintf.spec (GF := GF) (hG := hG))
    (wp_CodeString : codes.Code.String.spec (GF := GF) (hG := hG))
    (wp_Equal : proto.EqualStatus.spec (GF := GF) (hG := hG)) :
    status.Error.spec (GF := GF) (hG := hG) := by
  intro c msg
  wp_start as %hc
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave #Hcodes : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.codes $$ []
  · iPkgInit
  ihave #Hproto : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  wp_auto
  wp_apply status.wp_New_statusAt c msg as %s #Hs
  wp_method_call
  wp_auto
  wp_apply wp_Status_Code_ro s c msg
  · iexact Hs
  have hc0 : c ≠ W32 0 := fun h => hc (by subst h; rfl)
  rw [decide_eq_false hc0]
  wp_auto
  wp_alloc l as Hl
  ihave %hl := typedPointsto_not_null _ _ _ $$ Hl
  iStructNamed Hl
  ipersist s
  wp_auto
  -- the method set of `*status.Error`: `Error`, `GRPCStatus`, `Is`
  have hms := fun n => go.method_set_is
    (t := go.GoType.PointerType google_golang_org.grpc.internal.status.Error.ty) n
  have hGS := hms go!"GRPCStatus"
  have hIs := hms go!"Is"
  have hEr := hms go!"Error"
  have hFm := hms go!"Format"
  have hAs := hms go!"As"
  have hUn := hms go!"Unwrap"
  simp only [go.methodSetLookup_cons, go.methodSetLookup_nil,
    gooseReduceIteDecide] at hGS hIs hEr hFm hAs hUn
  have hne : go.GoType.PointerType google_golang_org.grpc.internal.status.Error.ty ≠
      go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty := by
    unfold go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty; nofun
  ihave #Hg : status.grpcStatusIs
      ⟨go.GoType.PointerType google_golang_org.grpc.internal.status.Error.ty, #l⟩ s c msg $$ []
  · unfold status.grpcStatusIs
    isplitr
    · ipureintro; rfl
    iexists l
    iframe s Hs
    ipureintro; rfl
  ihave #HE := status.errorMsgIs_Error wp_Sprintf wp_CodeString l s c msg $$ [$Hfmt $Hcodes $s $Hs]
  iapply HΦ
  simp only [interface.mkOk]
  isplitr
  · ipureintro; nofun
  isplitr
  · -- statusErrOk
    unfold statusErrOk
    iintro !> %e %he
    injection he with he
    subst he
    isplitr
    · iexists _; iexact HE
    isplitr
    · ipureintro
      refine ⟨?_, ?_, ?_⟩ <;> simp [hAs, hUn]
    isplitr
    · unfold grpcErrMethodsOk
      isplitr
      · iintro -
        iexists s, c, msg
        iexact Hg
      iintro - !> %target %m₁ %m' %Ψ #Hd #Ht HΨ
      ihave ⟨%s₁, %c₁, #Hg₁⟩ := descIs_GRPC _ m₁ hGS hne $$ Hd
      ihave %hag := status.grpcStatusIs_agree _ _ _ _ _ _ _ $$ Hg Hg₁
      obtain ⟨-, -, rfl⟩ := hag
      iapply (status.wp_Error_Is wp_Equal l s c msg target m' Ψ) $$ [$Hproto $s $Hs] Ht HΨ
    isplitr
    · ipureintro; exact ⟨hFm, hEr⟩
    ipureintro
    exact stTypedErr_ptr _ ⟨_, l, rfl, rfl⟩
  isplitr
  · -- descIs
    unfold descIs
    iright; iright
    iexists _
    isplitr
    · ipureintro
      refine ⟨rfl, ?_⟩
      rintro ⟨x, hx⟩
      simp only [interface.mkOk] at hx
      injection hx with hx
      exact hne (congrArg GoInterfaceOk.ty hx)
    iright
    iexists s, c
    iframe Hg
    ipureintro; exact hGS
  isplitr
  · ipureintro; intro ii h; injection h with h; subst h; rfl
  isplitr
  · ipureintro; intro ii h; injection h with h; subst h; exact ⟨l, rfl⟩
  isplitr
  · unfold statusCodeIs
    iright; iright
    iexists _, s, msg
    iframe Hg
    ipureintro; exact ⟨rfl, hGS⟩
  ipureintro
  exact ⟨_, rfl, hGS⟩

end proof

end EtcdGrove
end Perennial
