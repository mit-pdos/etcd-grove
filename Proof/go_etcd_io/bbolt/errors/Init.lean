/-
Package initialization of `go_etcd_io.bbolt.errors`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`bboltErrorsInit`, `Proof/go_etcd_io/bbolt/PkgInit.lean`): `ErrBucketNotFound`
holds an `errors.New` error, a leaf pointer error without an `Is` method
(`EtcdGrove.ErrorStringLeaf`, of the method set goose emits). Its initializer allocates its
variables and runs their translated initializers, `errors.New` calls (`errors/errors.go`;
Perennial's `errors.wp_New_errorString`); the other variables' errors are pointer errors and
`fmtErrorOk` (`EtcdGrove.errorString_fmtErrorOk`, `Proof/errors/ErrorStringOk.lean`).
-/
module

public import Proof.go_etcd_io.bbolt.PkgInit
public import Perennial.Proof.errors.Link
public import Perennial.Proof.errors.NewVar
public import Proof.errors.NewVar
public import Proof.errors.ErrorStringOk
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.bbolt.errors.Assumptions]
variable [_root_.Perennial.errors.Assumptions]

namespace go_etcd_io.bbolt.errors

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.bbolt.errors get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrDifferentDB _ as HErrDifferentDB
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrSameBuckets _ as HErrSameBuckets
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrIncompatibleValue _ as HErrIncompatibleValue
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrMaxSizeReached _ as HErrMaxSizeReached
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrValueTooLarge _ as HErrValueTooLarge
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrKeyTooLarge _ as HErrKeyTooLarge
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrKeyRequired _ as HErrKeyRequired
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrBucketNameRequired _ as HErrBucketNameRequired
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrBucketExists _ as HErrBucketExists
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrBucketNotFound _ as HErrBucketNotFound
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrFreePagesNotLoaded _ as HErrFreePagesNotLoaded
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrDatabaseReadOnly _ as HErrDatabaseReadOnly
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrTxClosed _ as HErrTxClosed
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrTxNotWritable _ as HErrTxNotWritable
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrTimeout _ as HErrTimeout
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrChecksum _ as HErrChecksum
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrVersionMismatch _ as HErrVersionMismatch
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrInvalidMapping _ as HErrInvalidMapping
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrInvalid _ as HErrInvalid
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrDatabaseNotOpen _ as HErrDatabaseNotOpen
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of ErrDatabaseNotOpen))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrDatabaseNotOpen #MErrDatabaseNotOpen
  -- translated initializer of ErrInvalid))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrInvalid #MErrInvalid
  -- translated initializer of ErrInvalidMapping))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrInvalidMapping #MErrInvalidMapping
  -- translated initializer of ErrVersionMismatch))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrVersionMismatch #MErrVersionMismatch
  -- translated initializer of ErrChecksum))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrChecksum #MErrChecksum
  -- translated initializer of ErrTimeout))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrTimeout #MErrTimeout
  -- translated initializer of ErrTxNotWritable))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrTxNotWritable #MErrTxNotWritable
  -- translated initializer of ErrTxClosed))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrTxClosed #MErrTxClosed
  -- translated initializer of ErrDatabaseReadOnly))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrDatabaseReadOnly #MErrDatabaseReadOnly
  -- translated initializer of ErrFreePagesNotLoaded))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrFreePagesNotLoaded #MErrFreePagesNotLoaded
  -- translated initializer of ErrBucketNotFound))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrBucketNotFound #MErrBucketNotFound
  -- translated initializer of ErrBucketExists))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrBucketExists #MErrBucketExists
  -- translated initializer of ErrBucketNameRequired))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrBucketNameRequired #MErrBucketNameRequired
  -- translated initializer of ErrKeyRequired))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrKeyRequired #MErrKeyRequired
  -- translated initializer of ErrKeyTooLarge))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrKeyTooLarge #MErrKeyTooLarge
  -- translated initializer of ErrValueTooLarge))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrValueTooLarge #MErrValueTooLarge
  -- translated initializer of ErrMaxSizeReached))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrMaxSizeReached #MErrMaxSizeReached
  -- translated initializer of ErrIncompatibleValue))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrIncompatibleValue #MErrIncompatibleValue
  -- translated initializer of ErrSameBuckets))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrSameBuckets #MErrSameBuckets
  -- translated initializer of ErrDifferentDB))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrDifferentDB #MErrDifferentDB
  try wp_auto
  ipersist HErrDatabaseNotOpen
  ipersist HErrInvalid
  ipersist HErrInvalidMapping
  ipersist HErrVersionMismatch
  ipersist HErrChecksum
  ipersist HErrTimeout
  ipersist HErrTxNotWritable
  ipersist HErrTxClosed
  ipersist HErrDatabaseReadOnly
  ipersist HErrFreePagesNotLoaded
  ipersist HErrBucketNotFound
  ipersist HErrBucketExists
  ipersist HErrBucketNameRequired
  ipersist HErrKeyRequired
  ipersist HErrKeyTooLarge
  ipersist HErrValueTooLarge
  ipersist HErrMaxSizeReached
  ipersist HErrIncompatibleValue
  ipersist HErrSameBuckets
  ipersist HErrDifferentDB
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  try (isplitl []; · (imodintro; itrivial))
  imodintro
  iexists _
  iframe HErrBucketNotFound
  isplitr
  · ipureintro
    exact ⟨⟨_, _, rfl, rfl⟩, EtcdGrove.ErrorStringLeaf.leaf _, EtcdGrove.ErrorStringLeaf.noIs⟩
  unfold go_etcd_io.bbolt.errors.bboltErrorsVars go_etcd_io.bbolt.errors.bboltErrVar
  isplitr
  · iexists _; iframe HErrDatabaseNotOpen; isplitr
    · ipureintro; exact ⟨_, _, rfl, rfl⟩
    iapply EtcdGrove.errorString_fmtErrorOk; iexact MErrDatabaseNotOpen
  isplitr
  · iexists _; iframe HErrInvalid; isplitr
    · ipureintro; exact ⟨_, _, rfl, rfl⟩
    iapply EtcdGrove.errorString_fmtErrorOk; iexact MErrInvalid
  isplitr
  · iexists _; iframe HErrInvalidMapping; isplitr
    · ipureintro; exact ⟨_, _, rfl, rfl⟩
    iapply EtcdGrove.errorString_fmtErrorOk; iexact MErrInvalidMapping
  isplitr
  · iexists _; iframe HErrVersionMismatch; isplitr
    · ipureintro; exact ⟨_, _, rfl, rfl⟩
    iapply EtcdGrove.errorString_fmtErrorOk; iexact MErrVersionMismatch
  isplitr
  · iexists _; iframe HErrChecksum; isplitr
    · ipureintro; exact ⟨_, _, rfl, rfl⟩
    iapply EtcdGrove.errorString_fmtErrorOk; iexact MErrChecksum
  isplitr
  · iexists _; iframe HErrTimeout; isplitr
    · ipureintro; exact ⟨_, _, rfl, rfl⟩
    iapply EtcdGrove.errorString_fmtErrorOk; iexact MErrTimeout
  isplitr
  · iexists _; iframe HErrTxNotWritable; isplitr
    · ipureintro; exact ⟨_, _, rfl, rfl⟩
    iapply EtcdGrove.errorString_fmtErrorOk; iexact MErrTxNotWritable
  isplitr
  · iexists _; iframe HErrTxClosed; isplitr
    · ipureintro; exact ⟨_, _, rfl, rfl⟩
    iapply EtcdGrove.errorString_fmtErrorOk; iexact MErrTxClosed
  isplitr
  · iexists _; iframe HErrDatabaseReadOnly; isplitr
    · ipureintro; exact ⟨_, _, rfl, rfl⟩
    iapply EtcdGrove.errorString_fmtErrorOk; iexact MErrDatabaseReadOnly
  isplitr
  · iexists _; iframe HErrFreePagesNotLoaded; isplitr
    · ipureintro; exact ⟨_, _, rfl, rfl⟩
    iapply EtcdGrove.errorString_fmtErrorOk; iexact MErrFreePagesNotLoaded
  isplitr
  · iexists _; iframe HErrBucketExists; isplitr
    · ipureintro; exact ⟨_, _, rfl, rfl⟩
    iapply EtcdGrove.errorString_fmtErrorOk; iexact MErrBucketExists
  isplitr
  · iexists _; iframe HErrBucketNameRequired; isplitr
    · ipureintro; exact ⟨_, _, rfl, rfl⟩
    iapply EtcdGrove.errorString_fmtErrorOk; iexact MErrBucketNameRequired
  isplitr
  · iexists _; iframe HErrKeyRequired; isplitr
    · ipureintro; exact ⟨_, _, rfl, rfl⟩
    iapply EtcdGrove.errorString_fmtErrorOk; iexact MErrKeyRequired
  isplitr
  · iexists _; iframe HErrKeyTooLarge; isplitr
    · ipureintro; exact ⟨_, _, rfl, rfl⟩
    iapply EtcdGrove.errorString_fmtErrorOk; iexact MErrKeyTooLarge
  isplitr
  · iexists _; iframe HErrValueTooLarge; isplitr
    · ipureintro; exact ⟨_, _, rfl, rfl⟩
    iapply EtcdGrove.errorString_fmtErrorOk; iexact MErrValueTooLarge
  isplitr
  · iexists _; iframe HErrMaxSizeReached; isplitr
    · ipureintro; exact ⟨_, _, rfl, rfl⟩
    iapply EtcdGrove.errorString_fmtErrorOk; iexact MErrMaxSizeReached
  isplitr
  · iexists _; iframe HErrIncompatibleValue; isplitr
    · ipureintro; exact ⟨_, _, rfl, rfl⟩
    iapply EtcdGrove.errorString_fmtErrorOk; iexact MErrIncompatibleValue
  isplitr
  · iexists _; iframe HErrSameBuckets; isplitr
    · ipureintro; exact ⟨_, _, rfl, rfl⟩
    iapply EtcdGrove.errorString_fmtErrorOk; iexact MErrSameBuckets
  iexists _; iframe HErrDifferentDB; isplitr
  · ipureintro; exact ⟨_, _, rfl, rfl⟩
  iapply EtcdGrove.errorString_fmtErrorOk; iexact MErrDifferentDB

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.bbolt.errors get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end go_etcd_io.bbolt.errors

end init

end Perennial
