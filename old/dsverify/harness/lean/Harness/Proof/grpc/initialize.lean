/-
The package initializers of the lab's grpc and protobuf models (`initialize'` of each translated
package): from `ownInitializing`, each returns with its `isPkgInit` (`Base.lean`).
-/
module

public import Harness.Proof.grpc.Base
public import Harness.Spec.net.initialize
public import Perennial.Spec.sync.initialize
public import Perennial.Spec.errors.initialize
public import Perennial.Spec.context.initialize
public import Perennial.Spec.fmt.initialize
public import Perennial.Proof.github_com.goose_lang.primitive.initialize

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [google_golang_org.protobuf.reflect.protoreflect.Assumptions]
variable [google_golang_org.protobuf.runtime.protoimpl.Assumptions]
variable [google_golang_org.protobuf.proto.Assumptions]
variable [google_golang_org.grpc.codes.Assumptions] [google_golang_org.grpc.status.Assumptions]
variable [google_golang_org.grpc.credentials.Assumptions]
variable [google_golang_org.grpc.Assumptions]

/-- `protoreflect`'s initializer. -/
abbrev google_golang_org.protobuf.reflect.protoreflect.initialize'.spec : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp GF),
  GetIsPkgInitProp pkg_id.google_golang_org.protobuf.reflect.protoreflect get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }}
      (App (Val google_golang_org.protobuf.reflect.protoreflect.initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.reflect.protoreflect }}

theorem google_golang_org.protobuf.reflect.protoreflect.initialize'.wp_proof :
    google_golang_org.protobuf.reflect.protoreflect.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iframe Hown
  is_pkg_init_finish

/-- `protoimpl`'s initializer. -/
abbrev google_golang_org.protobuf.runtime.protoimpl.initialize'.spec : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp GF),
  GetIsPkgInitProp pkg_id.google_golang_org.protobuf.runtime.protoimpl get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }}
      (App (Val google_golang_org.protobuf.runtime.protoimpl.initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.runtime.protoimpl }}

theorem google_golang_org.protobuf.runtime.protoimpl.initialize'.wp_proof :
    google_golang_org.protobuf.runtime.protoimpl.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := google_golang_org.protobuf.runtime.protoimpl.Export)
    google_golang_org.protobuf.runtime.protoimpl.X
    google_golang_org.protobuf.runtime.protoimpl.Export.ty as -
  wp_apply google_golang_org.protobuf.reflect.protoreflect.initialize'.wp_proof _ Hinit.2.1 $$ Hown
    as ⟨Hown, #H1⟩
  iframe Hown
  is_pkg_init_finish

/-- `codes`' initializer. -/
abbrev google_golang_org.grpc.codes.initialize'.spec : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp GF),
  GetIsPkgInitProp pkg_id.google_golang_org.grpc.codes get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }}
      (App (Val google_golang_org.grpc.codes.initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.codes }}

theorem google_golang_org.grpc.codes.initialize'.wp_proof :
    google_golang_org.grpc.codes.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iframe Hown
  is_pkg_init_finish

/-- `credentials`' initializer. -/
abbrev google_golang_org.grpc.credentials.initialize'.spec : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp GF),
  GetIsPkgInitProp pkg_id.google_golang_org.grpc.credentials get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }}
      (App (Val google_golang_org.grpc.credentials.initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.credentials }}

theorem google_golang_org.grpc.credentials.initialize'.wp_proof :
    google_golang_org.grpc.credentials.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iframe Hown
  is_pkg_init_finish

section insecure
-- scoped here: no other initializer needs it (a program that never imports `credentials/insecure`
-- has no node assumption providing it)
variable [google_golang_org.grpc.credentials.insecure.Assumptions]

/-- `insecure`'s initializer. -/
abbrev google_golang_org.grpc.credentials.insecure.initialize'.spec : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp GF),
  GetIsPkgInitProp pkg_id.google_golang_org.grpc.credentials.insecure get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }}
      (App (Val google_golang_org.grpc.credentials.insecure.initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.credentials.insecure }}

theorem google_golang_org.grpc.credentials.insecure.initialize'.wp_proof :
    google_golang_org.grpc.credentials.insecure.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply google_golang_org.grpc.credentials.initialize'.wp_proof _ Hinit.2.1 $$ Hown
    as ⟨Hown, #H1⟩
  iframe Hown
  is_pkg_init_finish

end insecure

variable [context.Assumptions] [fmt.Assumptions]

/-- `status`' initializer. -/
abbrev google_golang_org.grpc.status.initialize'.spec : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp GF),
  GetIsPkgInitProp pkg_id.google_golang_org.grpc.status get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }}
      (App (Val google_golang_org.grpc.status.initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status }}

theorem google_golang_org.grpc.status.initialize'.wp_proof
    (wp_context_initialize : context.initialize'.spec (GF := GF) (hG := hG))
    (wp_fmt_initialize : fmt.initialize'.spec (GF := GF) (hG := hG)) :
    google_golang_org.grpc.status.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply google_golang_org.grpc.codes.initialize'.wp_proof _ Hinit.2.2.2.1 $$ Hown
    as ⟨Hown, #H3⟩
  wp_apply wp_fmt_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #H2⟩
  wp_apply wp_context_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #H1⟩
  iframe Hown
  is_pkg_init_finish

variable [google_golang_org.protobuf.proto.PbKit]

/-- `proto`'s initializer. -/
abbrev google_golang_org.protobuf.proto.initialize'.spec : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp GF),
  GetIsPkgInitProp pkg_id.google_golang_org.protobuf.proto get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }}
      (App (Val google_golang_org.protobuf.proto.initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto }}

theorem google_golang_org.protobuf.proto.initialize'.wp_proof
    (wp_sync_initialize : sync.initialize'.spec (GF := GF) (hG := hG)) :
    google_golang_org.protobuf.proto.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := Loc) google_golang_org.protobuf.proto.codec
    (go.GoType.PointerType google_golang_org.protobuf.proto.Codec.ty) as Hcodec
  wp_apply wp_GlobalAlloc (V := sync.Mutex) google_golang_org.protobuf.proto.codecMu
    sync.Mutex.ty as HcodecMu
  iapply wp_fupd
  imod sync.init_Mutex google_golang_org.protobuf.proto.codecInv ⊤
      (globalAddr google_golang_org.protobuf.proto.codecMu) $$ [HcodecMu] [Hcodec] with #HcMu
  · iexact HcodecMu
  · inext; unfold google_golang_org.protobuf.proto.codecInv; ileft; iexact Hcodec
  wp_apply google_golang_org.protobuf.reflect.protoreflect.initialize'.wp_proof _ Hinit.2.2.1 $$ Hown
    as ⟨Hown, #H2⟩
  wp_apply wp_sync_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #H1⟩
  imodintro
  iframe Hown
  is_pkg_init_finish
  unfold google_golang_org.protobuf.proto.isInit
  iframe HcMu
  ipureintro; exact isPanic_intoVal ()

variable [net.Assumptions] [net.model.Assumptions]

/-- The `grpc` model's initializer. -/
abbrev google_golang_org.grpc.initialize'.spec : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp GF),
  GetIsPkgInitProp pkg_id.google_golang_org.grpc get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }}
      (App (Val google_golang_org.grpc.initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc }}

set_option goose.wp.extras true in
theorem google_golang_org.grpc.initialize'.wp_proof
    (wp_context_initialize : context.initialize'.spec (GF := GF) (hG := hG))
    (wp_errors_initialize : errors.initialize'.spec (GF := GF) (hG := hG))
    (wp_net_initialize : net.initialize'.spec (GF := GF) (hG := hG))
    (wp_sync_initialize : sync.initialize'.spec (GF := GF) (hG := hG))
    (wp_fmt_initialize : fmt.initialize'.spec (GF := GF) (hG := hG)) :
    google_golang_org.grpc.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoInterface) google_golang_org.grpc.errFrame go.error as HeF
  wp_apply wp_GlobalAlloc (V := GoInterface) google_golang_org.grpc.errNoTransportSecurity go.error
    as HeT
  wp_apply github_com.goose_lang.primitive.initialize'.wp_proof _ Hinit.2.2.2.2.2.2.2.2.2.1
    $$ Hown as ⟨Hown, #H9⟩
  wp_apply google_golang_org.grpc.credentials.initialize'.wp_proof _ Hinit.2.2.2.2.2.2.2.2.1
    $$ Hown as ⟨Hown, #H8⟩
  wp_apply google_golang_org.protobuf.proto.initialize'.wp_proof wp_sync_initialize _
    Hinit.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H7⟩
  wp_apply google_golang_org.grpc.status.initialize'.wp_proof wp_context_initialize
    wp_fmt_initialize _ Hinit.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H6⟩
  wp_apply google_golang_org.grpc.codes.initialize'.wp_proof _ Hinit.2.2.2.2.2.1 $$ Hown
    as ⟨Hown, #H5⟩
  wp_apply wp_sync_initialize _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #H4⟩
  wp_apply wp_net_initialize _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #H3⟩
  wp_apply wp_errors_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #H2⟩
  wp_apply wp_context_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #H1⟩
  iapply wp_fupd
  wp_apply errors.wp_New_errorString as %xT #ET
  wp_apply errors.wp_New_errorString as %xF #EF
  ipersist HeF
  ipersist HeT
  imodintro
  isplitr
  · ipureintro; exact isPanic_intoVal ()
  iframe Hown
  is_pkg_init_finish
  imodintro
  unfold google_golang_org.grpc.isInit errors.newVar
  isplitl
  · iexists xF
    iframe HeF EF
  isplitl
  · iexists xT
    iframe HeT ET
  itrivial

end spec

end Perennial
