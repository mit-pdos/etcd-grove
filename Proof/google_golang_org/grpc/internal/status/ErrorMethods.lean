/-
The methods of grpc's `*internal/status.Error` built by `(*Status).Err()` (prove-statuserror,
2026-11-26): `Error()` returns one fixed string, `"rpc error: code = <code> desc = <message>"`
(`status.errMsg`), through `(*Status).String()`, `fmt.Sprintf` and `codes.Code.String()`; `Is(target)`
returns `true` only for a `*status.Error` target of the same message, through `proto.Equal`. Proved
over the translation, taking the callees' specs; what `status.Error`'s proof assembles into
`statusErrOk` (`Proof/google_golang_org/grpc/status/Error.lean`).
-/
module

public import Proof.google_golang_org.grpc.internal.status.Methods
public import Spec.google_golang_org.grpc.codes.Code__String
public import Spec.google_golang_org.protobuf.proto.EqualStatus
public import Proof.fmt.SprintfPure

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

/-- What `(*Status).String()` of a status of code `c` and message `m` returns (`internal/status/
status.go:131-133`, `fmt.Sprintf("rpc error: code = %s desc = %s", s.Code(), s.Message())`), and so
`(*Error).Error()`. -/
def status.errMsg (c : w32) (m : GoString) : GoString :=
  go!"rpc error: code = " ++ codes.codeStr c ++ go!" desc = " ++ m

/-- The pieces of `"rpc error: code = %s desc = %s"`. -/
abbrev status.errMsgPieces : List _root_.Perennial.fmt.Piece :=
  [.lit go!"rpc error: code = ", .dir none _root_.Perennial.fmt.verb_s, .lit go!" desc = ",
    .dir none _root_.Perennial.fmt.verb_s]

theorem status.errMsg_encode :
    go!"rpc error: code = %s desc = %s" = _root_.Perennial.fmt.encode status.errMsgPieces := by
  fmt_encode

/-- `Sprintf`'s output for those pieces, a code formatted by a `String()` returning `codeStr c` and
the message `m`, is `errMsg c m`. -/
theorem status.errMsg_out [GooseExts] (c : w32) (m s : GoString)
    (h : _root_.Perennial.fmt.Out status.errMsgPieces
      [.method (· = codes.codeStr c), .str m] s) :
    s = status.errMsg c m := by
  cases h with
  | lit _ _ _ _ h1 =>
    cases h1 with
    | dir _ _ _ _ _ _ _ hd h2 =>
      cases h2 with
      | lit _ _ _ _ h3 =>
        cases h3 with
        | dir _ _ _ _ _ _ _ hd' h4 =>
          cases h4
          cases hd; cases hd'; simp_all [status.errMsg]

section methods
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.internal.status.Assumptions]
variable [codes_sem : google_golang_org.grpc.codes.Assumptions]
variable [fmt_sem : _root_.Perennial.fmt.Assumptions]

/-- **`s.String()` of a read-only status of code `c` and message `m` returns `errMsg c m`**
(`internal/status/status.go:131-133`): `Sprintf` of the code (formatted by its `String()`,
`codes.codeStr c`) and the message. -/
theorem status.wp_Status_String_ro
    (wp_Sprintf : _root_.Perennial.fmt.Sprintf.spec (GF := GF) (hG := hG))
    (wp_CodeString : codes.Code.String.spec (GF := GF) (hG := hG))
    (s : Loc) (c : w32) (m : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.codes ∗
        status.statusAt s c m }}
      (App (Val (s @!! go.GoType.PointerType google_golang_org.grpc.internal.status.Status.ty @!!
        go!"String")) (Val #()))
    {{ RET #(status.errMsg c m); True }} := by
  wp_start as #Hs
  wp_auto
  wp_apply wp_Status_Code_ro s c m
  · iexact Hs
  wp_apply wp_Status_Message_ro s c m
  · iexact Hs
  wp_apply wp_slice_literal (V := GoInterface)
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  have hE := go.method_set_is (t := google_golang_org.grpc.codes.Code.ty) go!"Error"
  have hF := go.method_set_is (t := google_golang_org.grpc.codes.Code.ty) go!"Format"
  have hS := go.method_set_is (t := google_golang_org.grpc.codes.Code.ty) go!"String"
  have hC := go.method_set_is (t := google_golang_org.grpc.codes.Code.ty) go!"CanInterface"
  simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at hE hF hS hC
  wp_apply (wp_Sprintf _ status.errMsgPieces _ _ [.method (· = codes.codeStr c), .str m]
    (DFrac.own 1) status.errMsg_encode (by fmt_fits)) $$ [$Hpkg $Hsl] as %r ⟨-, -, %hr⟩
  · have hxs : [interface.mkOk google_golang_org.grpc.codes.Code.ty #c, GoInterface.nil].set
        (sint.nat (W64 (0 + 1))) (interface.mkOk go.string #m) =
        [interface.mkOk google_golang_org.grpc.codes.Code.ty #c, interface.mkOk go.string #m] := by
      rfl
    rw [hxs]
    iapply BigSepL2.bigSepL2_cons.2
    isplitl
    · unfold _root_.Perennial.fmt.isArg
      iexists ⟨google_golang_org.grpc.codes.Code.ty, #c⟩, go!"String"
      isplitr
      · ipureintro; exact ⟨rfl, fmt.methodArg_stringer _ hF hE hS hC⟩
      unfold _root_.Perennial.fmt.methodSpec
      imodintro
      iintro %Φ' HΦ'
      wp_apply wp_CodeString c
      iapply HΦ'
      ipureintro; rfl
    · iapply BigSepL2.bigSepL2_cons.2
      isplitl
      · unfold _root_.Perennial.fmt.isArg; ipureintro; rfl
      · iapply BigSepL2.bigSepL2_nil.2; itrivial
  rw [status.errMsg_out c m r hr]
  iapply HΦ
  itrivial

/-- **`Error()` of a `*status.Error` holding a read-only status of code `c` and message `m` returns
`errMsg c m` on every call** (`internal/status/status.go:211-213`, `e.s.String()`): `errorMsgIs`. -/
theorem status.errorMsgIs_Error
    (wp_Sprintf : _root_.Perennial.fmt.Sprintf.spec (GF := GF) (hG := hG))
    (wp_CodeString : codes.Code.String.spec (GF := GF) (hG := hG))
    (l s : Loc) (c : w32) (m : GoString) :
    isPkgInit (PROP := IProp GF) pkg_id.fmt ∗
      isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.codes ∗
      l.[google_golang_org.grpc.internal.status.Error, go!"s"] ↦□ s ∗ status.statusAt s c m ⊢
    go_etcd_io.etcd.cache.v3.errorMsgIs
      ⟨go.GoType.PointerType google_golang_org.grpc.internal.status.Error.ty, #l⟩
      (status.errMsg c m) := by
  iintro ⟨#Hf, #Hc, #Hl, #Hs⟩
  unfold go_etcd_io.etcd.cache.v3.errorMsgIs
  iintro !> %Φ HΦ
  simp only
  rw [method_unfold]
  wp_auto
  wp_apply status.wp_Status_String_ro wp_Sprintf wp_CodeString s c m
  · iexact Hs
  iexact HΦ

/-- **`Is(target)` of a `*status.Error` holding a read-only status of message `m` returns `true` only
for a target whose description is `m`** (`internal/status/status.go:222-228`: a target that is no
`*Error` gives `false`; one that is, `proto.Equal` of the two `*spb.Status`, which is `true` only for
equal messages): the `Is` clause of `grpcErrMethodsOk`. -/
theorem status.wp_Error_Is [proto_sem : google_golang_org.protobuf.proto.Assumptions]
    (wp_Equal : proto.EqualStatus.spec (GF := GF) (hG := hG))
    (l s : Loc) (c : w32) (m : GoString) (target : GoInterface) (m' : GoString)
    (Φ : val → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗
      l.[google_golang_org.grpc.internal.status.Error, go!"s"] ↦□ s ∗ status.statusAt s c m ⊢
    go_etcd_io.etcd.cache.v3.descIs target m' -∗ ▷ (∀ b : Bool, ⌜b = true → m = m'⌝ -∗ Φ #b) -∗
    WP (App (Val #(methods (go.GoType.PointerType google_golang_org.grpc.internal.status.Error.ty)
      go!"Is" #l)) (Val #target)) {{ Φ }} := by
  iintro ⟨#Hp, #Hl, #Hs⟩ #Ht HΦ
  rw [method_unfold]
  wp_auto
  cases target with
  | nil =>
    wp_auto
    iapply HΦ
    ipureintro; intro h; cases h
  | ok ii =>
    by_cases hty : ii.ty = go.GoType.PointerType google_golang_org.grpc.internal.status.Error.ty
    · have hg : methodSet ii.ty !! go!"GRPCStatus" = some grpcStatusSig := by
        have h := go.method_set_is
          (t := go.GoType.PointerType google_golang_org.grpc.internal.status.Error.ty) go!"GRPCStatus"
        simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at h
        rw [hty, h]
      have hne : ii.ty ≠ go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty := by
        rw [hty]; unfold go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty; nofun
      ihave ⟨%s', %c', #Hg⟩ := descIs_GRPC ii m' hg hne $$ Ht
      unfold status.grpcStatusIs
      icases Hg with ⟨-, %l', %hl', #Hl', #Hs'⟩
      obtain ⟨ty, v⟩ := ii
      simp only at hty hl'
      subst hty hl'
      simp only [ite_true, decide_true]
      unfold status.statusAt
      rw [status.statusAtRaw_eq, status.statusAtRaw_eq]
      icases Hs with ⟨%hs, #⟨%p, #Hsp, #Hp1⟩⟩
      icases Hs' with ⟨%hs', #⟨%p', #Hsp', #Hp1'⟩⟩
      wp_auto
      wp_apply wp_Equal p p' c c' m m' as %b %hb
      · iframe Hp1 Hp1'
      iapply HΦ
      ipureintro; intro h; exact (hb h).2
    · simp only [hty, ite_false, decide_false]
      wp_auto
      iapply HΦ
      ipureintro; intro h; cases h

end methods

end EtcdGrove
end Perennial
