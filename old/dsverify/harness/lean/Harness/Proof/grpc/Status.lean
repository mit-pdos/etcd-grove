/-
The proofs of the `status` and `codes` models' specs (`StatusSpec.lean`).
-/
module

public import Harness.Proof.grpc.StatusSpec

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace google_golang_org.grpc.status

/-- `uint32` (`codes.Code`'s underlying type) is not an interface type (the method-resolution step
on a `codes.Code` value needs it; Perennial has the instance for `Named` types, but `go.uint32`
is a definition). -/
instance notInterface_uint32 [GooseExts] [GoGlobalContext] : go.NotInterface go.uint32 := by
  unfold go.uint32; infer_instance

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [google_golang_org.grpc.codes.Assumptions] [google_golang_org.grpc.status.Assumptions]
variable [context.Assumptions] [fmt.Assumptions]

set_option goose.wp.extras true

theorem New.wp_proof : New.spec (GF := GF) (hG := hG) := by
  intro c msg
  wp_start
  iapply wp_fupd
  wp_auto
  ihave %Hnn := typedPointsto_not_null $$ «$r0»
  iStructNamed «$r0»
  ipersist code
  ipersist msg
  imodintro
  iapply HΦ
  isplitr
  · ipureintro; exact Hnn
  unfold isStatus
  iright
  iframe code msg
  ipureintro; exact Hnn

theorem Status.Code.wp_proof : Status.Code.spec (GF := GF) (hG := hG) := by
  intro st c msg
  wp_start as #Hs
  unfold isStatus
  simp only [google_golang_org.grpc.codes.OK]
  icases Hs with (%Hn | ⟨%Hn, #Hc, #Hm⟩)
  · obtain ⟨rfl, rfl, rfl⟩ := Hn
    wp_auto
    iapply HΦ; itrivial
  · wp_auto
    rw [decide_eq_false Hn]
    wp_auto
    iapply HΦ; itrivial

theorem Status.Message.wp_proof : Status.Message.spec (GF := GF) (hG := hG) := by
  intro st c msg
  wp_start as #Hs
  unfold isStatus
  icases Hs with (%Hn | ⟨%Hn, #Hc, #Hm⟩)
  · obtain ⟨rfl, rfl, rfl⟩ := Hn
    wp_auto
    iapply HΦ; itrivial
  · wp_auto
    rw [decide_eq_false Hn]
    wp_auto
    iapply HΦ; itrivial

theorem Status.Err.wp_proof : Status.Err.spec (GF := GF) (hG := hG) := by
  intro st c msg
  wp_start as #Hs
  wp_auto
  wp_apply Status.Code.wp_proof $$ [$Hpkg $Hs]
  wp_if_destruct
  · iapply HΦ; unfold errPost; ileft; ipureintro; exact ⟨rfl, rfl⟩
  · iapply wp_fupd
    wp_alloc e as He
    wp_auto
    iStructNamed He
    ipersist s
    imodintro
    iapply HΦ
    unfold errPost statusErrOf
    iright
    iexists _, st
    iframe s Hs
    ipureintro; exact ⟨rfl, by assumption⟩

theorem Error.wp_proof : Error.spec (GF := GF) (hG := hG) := by
  intro c msg
  wp_start
  wp_auto
  wp_apply New.wp_proof $$ [$Hpkg] as %st ⟨%Hn, #Hs⟩
  wp_apply Status.Err.wp_proof $$ [$Hpkg $Hs] as %err Herr
  iapply HΦ $$ Herr

theorem itoa.wp_proof (n : w32) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.codes }}
      (App (Val (@! google_golang_org.grpc.codes.itoa)) (Val #n))
    {{ (r : GoString), RET #r; True }} := by
  wp_start
  wp_auto
  wp_if_destruct
  · iapply HΦ; itrivial
  ihave HI : (∃ (m : w32) (sl : GoSlice) (bs : List w8), "n" ∷ n_ptr ↦ m ∗ "b" ∷ b_ptr ↦ sl ∗
      "Hsl" ∷ sl ↦* bs : IProp GF) $$ [n b]
  · iexists n, _, []
    iframe
    iapply ownSlice_nil
  wp_for HI
  wp_if_destruct
  · wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w8) (t := go.byte) [_]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %lit ⟨Hlit, Hcap⟩
    wp_auto
    wp_apply wp_slice_append (V := w8) _ _ sl bs (DFrac.own 1) $$ [$Hlit $Hcap $Hsl]
      as %r ⟨Hr, -, -⟩
    wp_for_post
    iframe
    iexists _, r, _
    iframe
  · wp_apply wp_bytes_to_string $$ Hsl as -
    iapply HΦ; itrivial

theorem codes.Code.String.wp_proof : codes.Code.String.spec (GF := GF) (hG := hG) := by
  intro c
  wp_start
  simp only [google_golang_org.grpc.codes.Canceled, google_golang_org.grpc.codes.Unknown, google_golang_org.grpc.codes.InvalidArgument, google_golang_org.grpc.codes.DeadlineExceeded, google_golang_org.grpc.codes.NotFound, google_golang_org.grpc.codes.AlreadyExists, google_golang_org.grpc.codes.PermissionDenied, google_golang_org.grpc.codes.ResourceExhausted, google_golang_org.grpc.codes.FailedPrecondition, google_golang_org.grpc.codes.Aborted, google_golang_org.grpc.codes.OutOfRange, google_golang_org.grpc.codes.Unimplemented, google_golang_org.grpc.codes.Internal, google_golang_org.grpc.codes.Unavailable, google_golang_org.grpc.codes.DataLoss, google_golang_org.grpc.codes.Unauthenticated]
  wp_auto
  repeat (wp_if_destruct; · iapply HΦ; itrivial)
  wp_apply itoa.wp_proof $$ [$Hpkg] as %r -
  iapply HΦ; itrivial

/-- The packages `status` imports are initialized. -/
theorem deps_of_pkg :
    isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ⊢
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗
      isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.codes := by
  refine (isPkgInit_unfold_deps (PROP := IProp GF) pkg_id.google_golang_org.grpc.status).trans ?_
  show iprop(isPkgInit (PROP := IProp GF) pkg_id.context ∗ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗
    isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.codes ∗ _) ⊢ _
  iintro ⟨H1, H2, H3, -⟩
  iframe

/-- `s.String()`: some string. -/
theorem Status.String.wp_proof (st : Loc) (c : w32) (msg : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗ isStatus st c msg }}
      (App (Val (st @!! go.GoType.PointerType Status.ty @!! go!"String")) (Val #()))
    {{ (r : GoString), RET #r; True }} := by
  wp_start as #Hs
  ihave ⟨-, -, #Hcodes⟩ := deps_of_pkg $$ Hpkg
  wp_auto
  wp_apply Status.Code.wp_proof $$ [$Hpkg $Hs]
  wp_apply codes.Code.String.wp_proof $$ [$Hcodes] as %r -
  wp_apply Status.Message.wp_proof $$ [$Hpkg $Hs]
  iapply HΦ; itrivial

theorem statusErrOf_errAny : statusErrOf_errAny.stmt (GF := GF) (hG := hG) := by
  intro err c msg
  iintro ⟨#Hpkg, #He⟩
  unfold statusErrOf
  icases He with ⟨%e, %st, %Heq, #Hsf, #Hs⟩
  obtain ⟨rfl, -⟩ := Heq
  unfold net.rpc.errAny
  iexists _
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; go_type_set
  imodintro
  iintro %Φ HΦ
  wp_method_call
  wp_call
  wp_auto
  wp_apply Status.String.wp_proof $$ [$Hpkg $Hs] as %r -
  iapply HΦ

theorem FromError.wp_proof : FromError.spec (GF := GF) (hG := hG) := by
  intro err
  wp_start as Herr
  icases Herr with (%Hn | ⟨%c, %msg, #He⟩ | ⟨#Ha, %Hns⟩)
  · subst Hn
    wp_auto
    iapply HΦ
    ileft; ipureintro; exact ⟨rfl, rfl, rfl⟩
  · ihave #He' := He
    unfold statusErrOf
    icases He' with ⟨%e, %st, %Heq, #Hsf, #Hs⟩
    obtain ⟨rfl, -⟩ := Heq
    wp_auto
    iapply HΦ
    iright; ileft
    iexists c, msg
    iframe He Hs
    ipureintro; rfl
  · ihave #Ha' := Ha
    unfold net.rpc.errAny
    icases Ha' with ⟨%e, %Heq, %Ht, #HE⟩
    subst Heq
    wp_auto
    have hne := Hns e rfl
    simp only [hne, ↓reduceIte, decide_false]
    wp_auto
    wp_apply HE as %m
    simp only [google_golang_org.grpc.codes.Unknown]
    wp_apply New.wp_proof $$ [$Hpkg] as %st ⟨%Hsn, #Hs⟩
    iapply HΦ
    iright; iright
    isplitr
    · ipureintro; rfl
    iexists m; iexact Hs

theorem Code.wp_proof : Code.spec (GF := GF) (hG := hG) := by
  intro err
  wp_start as Herr
  simp only [google_golang_org.grpc.codes.OK, google_golang_org.grpc.codes.Unknown]
  icases Herr with (%Hn | ⟨%c, %msg, #He⟩ | ⟨#Ha, %Hns⟩)
  · subst Hn
    wp_auto
    iapply HΦ
    ileft; ipureintro; exact ⟨rfl, rfl⟩
  · ihave #He' := He
    unfold statusErrOf
    icases He' with ⟨%e, %st, %Heq, #Hsf, #Hs⟩
    obtain ⟨rfl, -⟩ := Heq
    wp_auto
    wp_apply Status.Code.wp_proof $$ [$Hpkg $Hs]
    iapply HΦ
    iright; ileft
    iexists msg
    iexact He
  · ihave #Ha' := Ha
    unfold net.rpc.errAny
    icases Ha' with ⟨%e, %Heq, %Ht, #HE⟩
    subst Heq
    wp_auto
    have hne := Hns e rfl
    simp only [hne, ↓reduceIte, decide_false]
    wp_auto
    iapply HΦ
    iright; iright; ipureintro; rfl

theorem FromContextError.wp_proof : FromContextError.spec (GF := GF) (hG := hG) := by
  intro err
  wp_start as ⟨#Ha, %Hc⟩
  ihave ⟨#Hctx, -, -⟩ := deps_of_pkg $$ Hpkg
  ihave #Hci := context.isInit_access $$ Hctx
  icases Hci with ⟨-, -, -, -, -, ⟨%x, #HC, #Hxs⟩, #HD, -⟩
  unfold net.rpc.errAny
  icases Ha with ⟨%e, %Heq, %Ht, #HE⟩
  subst Heq
  simp only [google_golang_org.grpc.codes.DeadlineExceeded, google_golang_org.grpc.codes.Canceled,
    google_golang_org.grpc.codes.Unknown]
  rcases Hc with ⟨T, l, hT⟩ | hD
  · have he : e = ⟨go.GoType.PointerType T, #l⟩ := by
      simp only [interface.mkOk, GoInterface.ok.injEq] at hT; exact hT
    subst he
    have hnd : go.GoType.PointerType T ≠ context.deadlineExceededError.ty := by
      unfold context.deadlineExceededError.ty; simp
    simp only [hnd, ↓reduceIte]
    wp_auto
    by_cases hTe : T = errors.errorString.ty
    · subst hTe
      simp only [↓reduceIte]
      wp_auto
      wp_if_destruct
      · wp_apply HE as %m
        wp_apply New.wp_proof $$ [$Hpkg] as %st ⟨%Hsn, #Hs⟩
        iapply HΦ
        iexists _, m
        iframe Hs
        ipureintro; decide
      · wp_apply HE as %m
        wp_apply New.wp_proof $$ [$Hpkg] as %st ⟨%Hsn, #Hs⟩
        iapply HΦ
        iexists _, m
        iframe Hs
        ipureintro; decide
    · have hne : go.GoType.PointerType T ≠ go.GoType.PointerType errors.errorString.ty := by
        intro h; apply hTe; injection h
      simp only [hne, ↓reduceIte]
      wp_auto
      wp_apply HE as %m
      wp_apply New.wp_proof $$ [$Hpkg] as %st ⟨%Hsn, #Hs⟩
      iapply HΦ
      iexists _, m
      iframe Hs
      ipureintro; decide
  · have he : e = ⟨context.deadlineExceededError.ty, #(zero_val context.deadlineExceededError)⟩ := by
      simp only [interface.mkOk, GoInterface.ok.injEq] at hD; exact hD
    subst he
    wp_auto
    wp_apply HE as %m
    wp_apply New.wp_proof $$ [$Hpkg] as %st ⟨%Hsn, #Hs⟩
    iapply HΦ
    iexists _, m
    iframe Hs
    ipureintro; decide

end proofs

end google_golang_org.grpc.status

end Perennial
