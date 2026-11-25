/-
grpc's `internal/status` (status-bodies, 2026-11-25: translated with the bodies of `New` and the
`Status`/`Error` methods): what its methods do on a read-only status (`status.statusAt`) and on a
`*status.Error` holding one (`status.grpcStatusIs`), proved over the translation. The shared
vocabulary of the status slice's proofs (`Proof/google_golang_org/grpc/status/`) and of their callers.
-/
module

public import Proof.google_golang_org.grpc.status.StatusRO
public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section methods
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.internal.status.Assumptions]

/-- **`GRPCStatus()` of a `*status.Error` returns the status it holds** (`return e.s`,
`internal/status/status.go:216-218`): the WP form the specs stated before status-bodies. -/
theorem status.grpcStatusIs_wp (e : GoInterfaceOk) (s : Loc) (c : w32) (m : GoString) :
    status.grpcStatusIs (GF := GF) e s c m ⊢
      □ ∀ Φ : val → IProp GF, ▷ Φ #s -∗
        WP (App (Val #(methods e.ty go!"GRPCStatus" e.v)) (Val #())) {{ Φ }} := by
  obtain ⟨ty, v⟩ := e
  unfold status.grpcStatusIs
  iintro ⟨%hty, %l, %hl, #Hl, -⟩
  simp only at hty hl
  subst hty hl
  iintro !> %Φ HΦ
  rw [method_unfold]
  wp_auto
  iexact HΦ

/-- **`s.Code()` of a read-only status returns its code** (`internal/status/status.go:107-112`:
`codes.Code(s.s.Code)`, `s` and `s.s` non-nil). -/
theorem wp_Status_Code_ro (s : Loc) (c : w32) (m : GoString) :
    {{ status.statusAt (GF := GF) s c m }}
      (App (Val (s @!! go.GoType.PointerType google_golang_org.grpc.internal.status.Status.ty @!!
        go!"Code")) (Val #()))
    {{ RET #c; True }} := by
  wp_start as #Hs
  unfold status.statusAt status.statusAtRaw
  icases Hs with ⟨%hs, #⟨%p, %hp, #Hsp, #Hc, #Hm⟩⟩
  wp_auto
  rw [decide_eq_false hs]
  wp_auto
  rw [decide_eq_false hp]
  wp_auto
  iapply HΦ
  iclear «$res0»; itrivial

/-- `s.Code()` of a `nil` status returns `OK`. -/
theorem wp_Status_Code_nil :
    {{ (True : IProp GF) }}
      (App (Val (null @!! go.GoType.PointerType google_golang_org.grpc.internal.status.Status.ty @!!
        go!"Code")) (Val #()))
    {{ RET #(W32 0); True }} := by
  wp_start
  wp_auto
  iapply HΦ
  itrivial

/-- **`s.Message()` of a read-only status returns its message** (`status.go:115-120`). -/
theorem wp_Status_Message_ro (s : Loc) (c : w32) (m : GoString) :
    {{ status.statusAt (GF := GF) s c m }}
      (App (Val (s @!! go.GoType.PointerType google_golang_org.grpc.internal.status.Status.ty @!!
        go!"Message")) (Val #()))
    {{ RET #m; True }} := by
  wp_start as #Hs
  unfold status.statusAt status.statusAtRaw
  icases Hs with ⟨%hs, #⟨%p, %hp, #Hsp, #Hc, #Hm⟩⟩
  wp_auto
  rw [decide_eq_false hs]
  wp_auto
  rw [decide_eq_false hp]
  wp_auto
  iapply HΦ
  iclear «$res0»; itrivial

/-- `s.Message()` of a `nil` status returns `""`. -/
theorem wp_Status_Message_nil :
    {{ (True : IProp GF) }}
      (App (Val (null @!! go.GoType.PointerType google_golang_org.grpc.internal.status.Status.ty @!!
        go!"Message")) (Val #()))
    {{ RET #(go!""); True }} := by
  wp_start
  wp_auto
  iapply HΦ
  itrivial

/-- **`New(c, msg)` returns a fresh read-only status of code `c` and message `msg`**
(`status.go:76-78`, `&Status{s: &spb.Status{Code: int32(c), Message: msg}}`; the fields made
persistent: nothing writes them after). -/
theorem wp_New (c : w32) (msg : GoString) :
    {{ (True : IProp GF) }}
      (App (App (Val (@! google_golang_org.grpc.internal.status.New)) (Val #c)) (Val #msg))
    {{ (s : Loc), RET #s; status.statusAt s c msg }} := by
  wp_start
  iapply wp_fupd
  wp_auto
  ihave %hp := typedPointsto_not_null _ _ _ $$ «$v0»
  ihave %hs := typedPointsto_not_null _ _ _ $$ «$r0»
  iStructNamed «$v0»
  iStructNamed «$r0»
  ipersist Code
  ipersist Message
  ipersist s
  imodintro
  iapply HΦ
  unfold status.statusAt status.statusAtRaw
  isplitr
  · ipureintro; exact hs
  imodintro
  iexists _
  iframe Code Message s
  ipureintro; exact hp

/-- grpc `status.New(c, msg)` is `internal/status.New(c, msg)` (`status/status.go:51-53`). -/
theorem wp_status_New [google_golang_org.grpc.status.Assumptions] (c : w32) (msg : GoString) :
    {{ (True : IProp GF) }}
      (App (App (Val (@! google_golang_org.grpc.status.New)) (Val #c)) (Val #msg))
    {{ (s : Loc), RET #s; status.statusAt s c msg }} := by
  wp_start
  wp_auto
  wp_apply wp_New as %s #Hs
  iapply HΦ
  iexact Hs

end methods

section facts
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- grpc's `GRPCStatus() *Status` signature. -/
abbrev grpcStatusSig : go.signature :=
  go.Signature [] false [go.GoType.PointerType google_golang_org.grpc.internal.status.Status.ty]

/-- `EtcdError` has no `GRPCStatus` method (its method set: `Code`, `Error`). -/
theorem etcdError_noGRPCStatus [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] :
    methodSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty !! go!"GRPCStatus" = none := by
  have h := go.MethodSetIs.method_set_is
    (t := go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) go!"GRPCStatus"
  simpa [go.methodSetLookup_cons, go.methodSetLookup_nil] using h

/-- The code of `nil` is `OK`. -/
theorem statusCodeIs_nil_eq (c : w32) :
    statusCodeIs (GF := GF) GoInterface.nil c ⊢ ⌜c = W32 0⌝ := by
  unfold statusCodeIs
  iintro (%h | %h | ⟨%e, %s, %m, %h, -⟩)
  · ipureintro; exact h.2
  · obtain ⟨e, he, -⟩ := h; cases he
  · cases h.1

/-- The description of `nil` is `""`. -/
theorem descIs_nil_eq (m : GoString) :
    descIs (GF := GF) GoInterface.nil m ⊢ ⌜m = go!""⌝ := by
  unfold descIs
  iintro (%h | %h | ⟨%e, %h, -⟩)
  · ipureintro; exact h.2
  · obtain ⟨x, hx, -⟩ := h; cases hx
  · cases h.1

/-- The code of an error without `GRPCStatus` is `Unknown`. -/
theorem statusCodeIs_noGRPC_eq (e : GoInterfaceOk) (c : w32)
    (hg : methodSet e.ty !! go!"GRPCStatus" ≠ some grpcStatusSig) :
    statusCodeIs (GF := GF) (GoInterface.ok e) c ⊢ ⌜c = W32 2⌝ := by
  unfold statusCodeIs
  iintro (%h | %h | ⟨%e', %s, %m, %h, -⟩)
  · cases h.1
  · obtain ⟨e', he, -, hc⟩ := h; ipureintro; exact hc
  · obtain ⟨he, hg'⟩ := h; cases he; exact absurd hg' hg

/-- The code of an error with `GRPCStatus`: that of the status its `*status.Error` holds. -/
theorem statusCodeIs_GRPC (e : GoInterfaceOk) (c : w32)
    (hg : methodSet e.ty !! go!"GRPCStatus" = some grpcStatusSig) :
    statusCodeIs (GF := GF) (GoInterface.ok e) c ⊢
      ∃ (s : Loc) (m : GoString), status.grpcStatusIs e s c m := by
  unfold statusCodeIs
  iintro (%h | %h | ⟨%e', %s, %m, %h, #H⟩)
  · cases h.1
  · obtain ⟨e', he, hg', -⟩ := h; cases he; exact absurd hg hg'
  · obtain ⟨he, -⟩ := h; cases he
    iexists s, m; iexact H

/-- The description of an error with `GRPCStatus` of a type other than `EtcdError`'s (a
`*status.Error`, `grpcStatusIs_ty`): the message of the status it holds. -/
theorem descIs_GRPC (e : GoInterfaceOk) (m : GoString)
    (hg : methodSet e.ty !! go!"GRPCStatus" = some grpcStatusSig)
    (hty : e.ty ≠ go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) :
    descIs (GF := GF) (GoInterface.ok e) m ⊢
      ∃ (s : Loc) (c : w32), status.grpcStatusIs e s c m := by
  unfold descIs
  iintro (%h | %h | ⟨%e', %h, (⟨%hg', -⟩ | ⟨%s, %c, %hg', #H⟩)⟩)
  · cases h.1
  · obtain ⟨x, hx, -⟩ := h
    simp only [interface.mkOk] at hx
    injection hx with hx
    exact absurd (by rw [hx]) hty
  · obtain ⟨he, -⟩ := h; cases he; exact absurd hg hg'
  · obtain ⟨he, -⟩ := h; cases he
    iexists s, c; iexact H

/-- A `*status.Error`'s type is not `EtcdError`'s. -/
theorem grpcStatusIs_ty (e : GoInterfaceOk) (s : Loc) (c : w32) (m : GoString) :
    status.grpcStatusIs (GF := GF) e s c m ⊢
      ⌜e.ty ≠ go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty⌝ := by
  unfold status.grpcStatusIs
  iintro ⟨%h, -⟩
  ipureintro
  rw [h]
  unfold go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty
  nofun

/-- An error whose type is not `EtcdError`'s is no `EtcdError` value. -/
theorem ne_etcdError_of_ty (e : GoInterfaceOk)
    (hty : e.ty ≠ go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) :
    ∀ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError,
      GoInterface.ok e ≠ interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x := by
  intro x hx
  simp only [interface.mkOk] at hx
  injection hx with hx
  exact hty (by rw [hx])

/-- **An error of a code other than `OK` and `Unknown`, or with `GRPCStatus`, is no `EtcdError`
value**: it is a `*status.Error` (`statusCodeIs`'s third case). -/
theorem statusCodeIs_notEtcd (err : GoInterface) (c : w32)
    (h : c ≠ W32 0 ∧ c ≠ W32 2 ∨ hasGRPCStatus err) :
    statusCodeIs (GF := GF) err c ⊢
      ⌜∀ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError,
        err ≠ interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x⌝ := by
  unfold statusCodeIs
  iintro (%h' | %h' | ⟨%e, %s, %m, %h', #H⟩)
  · obtain ⟨rfl, rfl⟩ := h'
    rcases h with h | ⟨e, he, -⟩
    · exact absurd rfl h.1
    · cases he
  · obtain ⟨e, rfl, hg, rfl⟩ := h'
    rcases h with h | ⟨e', he, hg'⟩
    · exact absurd rfl h.2
    · cases he; exact absurd hg' hg
  · obtain ⟨rfl, -⟩ := h'
    ihave %hty := grpcStatusIs_ty _ _ _ _ $$ H
    ipureintro
    exact ne_etcdError_of_ty e hty

/-- The description of an error without `GRPCStatus`: an `EtcdError`'s `desc`, or what its `Error()`
stably returns. -/
theorem descIs_noGRPC (e : GoInterfaceOk) (m : GoString)
    (hg : methodSet e.ty !! go!"GRPCStatus" ≠ some grpcStatusSig) :
    descIs (GF := GF) (GoInterface.ok e) m ⊢
      ⌜∃ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError,
        GoInterface.ok e = interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x ∧
        m = x.desc'⌝ ∨ errorMsgIs e m := by
  unfold descIs
  iintro (%h | %h | ⟨%e', %h, (⟨%hg', #H⟩ | ⟨%s, %c, %hg', -⟩)⟩)
  · cases h.1
  · ileft; ipureintro; exact h
  · obtain ⟨he, -⟩ := h; cases he
    iright; iexact H
  · obtain ⟨he, -⟩ := h; cases he; exact absurd hg' hg

/-- `FromError`'s local interface `grpcstatus` (`interface{ GRPCStatus() *Status }`) holds a type
exactly when its method set has `GRPCStatus() *Status`. -/
theorem typeSetContains_grpcstatus [google_golang_org.grpc.status.Assumptions] (t : go.GoType) :
    go.typeSetContains t google_golang_org.grpc.status.grpcstatus.ty =
      decide (methodSet t !! go!"GRPCStatus" = some grpcStatusSig) := by
  unfold go.typeSetContains
  rw [go.is_underlying (t := google_golang_org.grpc.status.grpcstatus.ty)]
  simp [go.typeSetElemsContains, go.typeSetElemContains, grpcStatusSig]

/-- `grpcstatus` is an interface type. -/
theorem grpcstatus_isInterface [google_golang_org.grpc.status.Assumptions] :
    go.isInterfaceType (underlying google_golang_org.grpc.status.grpcstatus.ty) = true := by
  rw [go.is_underlying (t := google_golang_org.grpc.status.grpcstatus.ty)]
  rfl

end facts

end EtcdGrove
end Perennial
