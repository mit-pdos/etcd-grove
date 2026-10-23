/-
Package initialization of `k8s_io.apiserver.pkg.storage`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`storageInit`, `storage/etcd3/Base.lean`): `RequestWatchProgress` holds a string.
Its initializer allocates its translated variables (`errors.go`, `feature.go`, `selection_predicate.go`:
six `errors.New` errors, the map `errCodeToMessage`, three strings, and `Everything`, a
`SelectionPredicate` of `labels.Everything()` and `fields.Everything()`, names-only, the
trust-boundary axioms `labels.Everything.wp_proof` and `fields.Everything.wp_proof`), initializes
its imports and runs the translated initializers.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Proof.encoding.base64.Init
public import Proof.encoding.json.Init
public import Proof.go_etcd_io.raft.v3.Init
public import Proof.k8s_io.apimachinery.pkg.api.errors.Init
public import Proof.k8s_io.apimachinery.pkg.api.meta.Init
public import Proof.k8s_io.apimachinery.pkg.api.validate.content.Init
public import Proof.k8s_io.apimachinery.pkg.apis.meta.v1.Init
public import Proof.k8s_io.apimachinery.pkg.fields.Init
public import Proof.k8s_io.apimachinery.pkg.labels.Init
public import Proof.k8s_io.apimachinery.pkg.runtime.Init
public import Proof.k8s_io.apimachinery.pkg.sharding.Init
public import Proof.k8s_io.apimachinery.pkg.types.Init
public import Proof.k8s_io.apimachinery.pkg.util.validation.field.Init
public import Proof.k8s_io.apimachinery.pkg.watch.Init
public import Proof.k8s_io.apiserver.pkg.features.Init
public import Proof.k8s_io.apiserver.pkg.util.feature.Init
public import Proof.path.Init
public import Perennial.Proof.context.NewErrorString
public import Proof.k8s_io.apimachinery.pkg.labels.Everything
public import Proof.k8s_io.apimachinery.pkg.fields.Everything
public import Proof.runtime.PkgInitExt

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.k8s_io.apiserver.pkg.storage.Assumptions]
variable [_root_.Perennial.context.ErrorStringIsError]
  [_root_.Perennial.context.DeadlineExceededIsError]

namespace k8s_io.apiserver.pkg.storage

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.apiserver.pkg.storage get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := SelectionPredicate) Everything _ as HEverything
  wp_apply wp_GlobalAlloc (V := GoString) RangeStream _ as HRangeStream
  wp_apply wp_GlobalAlloc (V := GoString) RequestWatchProgress _ as HRequestWatchProgress
  wp_apply wp_GlobalAlloc (V := GoString) tooLargeResourceVersionCauseMsg _ as HtooLargeResourceVersionCauseMsg
  wp_apply wp_GlobalAlloc (V := Loc) errCodeToMessage _ as HerrCodeToMessage
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrStorageNotReady _ as HErrStorageNotReady
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrResourceVersionSetOnCreate _ as HErrResourceVersionSetOnCreate
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrUnrecognizedEncodedVersion _ as HErrUnrecognizedEncodedVersion
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrGenericInvalidKey _ as HErrGenericInvalidKey
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrEmptyStartKey _ as HErrEmptyStartKey
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrInvalidStartRV _ as HErrInvalidStartRV
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.api.validate.content.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd23⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync.atomic _root_.Perennial.sync.atomic.initialize'
      EtcdGrove.ExternalInit.sync_atomic _root_.Perennial.sync.atomic.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd22⟩
  wp_apply (_root_.Perennial.k8s_io.apiserver.pkg.util.feature.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd21⟩
  wp_apply (_root_.Perennial.k8s_io.apiserver.pkg.features.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd20⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.sharding.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd19⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.watch.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd18⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.types.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd17⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.labels.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd16⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.fields.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd15⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd14⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd13⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.api.errors.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strings _root_.Perennial.strings.initialize'
      EtcdGrove.ExternalInit.strings _root_.Perennial.strings.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply (_root_.Perennial.path.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (_root_.Perennial.encoding.json.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (_root_.Perennial.encoding.base64.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.util.validation.field.wp_initialize'_lb _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.runtime.wp_initialize'_lb _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.api.«meta».wp_initialize'_lb _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strconv _root_.Perennial.strconv.initialize'
      EtcdGrove.ExternalInit.strconv _root_.Perennial.strconv.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of ErrInvalidStartRV))
  -- translated initializer of ErrEmptyStartKey))
  -- translated initializer of ErrGenericInvalidKey))
  -- translated initializer of ErrUnrecognizedEncodedVersion))
  -- translated initializer of ErrResourceVersionSetOnCreate))
  -- translated initializer of ErrStorageNotReady))
  -- translated initializer of errCodeToMessage))
  -- translated initializer of tooLargeResourceVersionCauseMsg))
  -- translated initializer of RequestWatchProgress))
  -- translated initializer of RangeStream))
  -- translated initializer of Everything))
  try wp_auto
  wp_apply _root_.Perennial.context.wp_New_errorString as %_ -
  try wp_auto
  wp_apply _root_.Perennial.context.wp_New_errorString as %_ -
  try wp_auto
  wp_apply _root_.Perennial.context.wp_New_errorString as %_ -
  try wp_auto
  wp_apply _root_.Perennial.context.wp_New_errorString as %_ -
  try wp_auto
  wp_apply _root_.Perennial.context.wp_New_errorString as %_ -
  try wp_auto
  wp_apply _root_.Perennial.context.wp_New_errorString as %_ -
  try wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := GoString) go.int go.string) as %mref Hmap
  try wp_auto
  repeat (wp_apply (wp_mapInsert (K := w64) (V := GoString) go.int) $$ Hmap as Hmap; try wp_auto)
  wp_apply EtcdGrove.labels.Everything.wp_proof as %_ -
  try wp_auto
  wp_apply EtcdGrove.fields.Everything.wp_proof as %_ -
  try wp_auto
  ipersist HRequestWatchProgress
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  try (isplitl []; · (imodintro; itrivial))
  imodintro
  iexists _
  iexact HRequestWatchProgress

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.apiserver.pkg.storage get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end k8s_io.apiserver.pkg.storage

end init

end Perennial
