/-
Package initialization of `go_etcd_io.bbolt.errors`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`bboltErrorsInit`, `storage/backend/Base.lean`): `ErrBucketNotFound` holds an
`errors.New` error, a leaf pointer error without an `Is` method (`EtcdGrove.ErrorStringLeaf`, a
premise on the method sets). Its initializer runs its variables' initializers, all untranslated
`errors.New` calls (`errors/errors.go`), which the trust-boundary axiom `errorsNewVarsInit`
states.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Base
public import Proof.errors.NewVar

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

section opaqueInits
namespace go_etcd_io.bbolt.errors
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.bbolt.errors`'s variables initialized by `errors.New`.** Each
listed `X.init` (untranslated) runs Go's `var X = errors.New(msg)`, as its Go source has
it. -/
axiom errorsNewVarsInit :
    ∀ (init : val) (X msg : GoString), (init, X, msg) ∈ ([(ErrDatabaseNotOpen.init, ErrDatabaseNotOpen, go!"database not open"),
        (ErrInvalid.init, ErrInvalid, go!"invalid database"),
        (ErrInvalidMapping.init, ErrInvalidMapping, go!"database isn't correctly mapped"),
        (ErrVersionMismatch.init, ErrVersionMismatch, go!"version mismatch"),
        (ErrChecksum.init, ErrChecksum, go!"checksum error"),
        (ErrTimeout.init, ErrTimeout, go!"timeout"),
        (ErrTxNotWritable.init, ErrTxNotWritable, go!"tx not writable"),
        (ErrTxClosed.init, ErrTxClosed, go!"tx closed"),
        (ErrDatabaseReadOnly.init, ErrDatabaseReadOnly, go!"database is in read-only mode"),
        (ErrFreePagesNotLoaded.init, ErrFreePagesNotLoaded, go!"free pages are not pre-loaded"),
        (ErrBucketNotFound.init, ErrBucketNotFound, go!"bucket not found"),
        (ErrBucketExists.init, ErrBucketExists, go!"bucket already exists"),
        (ErrBucketNameRequired.init, ErrBucketNameRequired, go!"bucket name required"),
        (ErrKeyRequired.init, ErrKeyRequired, go!"key required"),
        (ErrKeyTooLarge.init, ErrKeyTooLarge, go!"key too large"),
        (ErrValueTooLarge.init, ErrValueTooLarge, go!"value too large"),
        (ErrMaxSizeReached.init, ErrMaxSizeReached, go!"database reached maximum size"),
        (ErrIncompatibleValue.init, ErrIncompatibleValue, go!"incompatible value"),
        (ErrSameBuckets.init, ErrSameBuckets, go!"the source and target are the same bucket"),
        (ErrDifferentDB.init, ErrDifferentDB, go!"the source and target buckets are in different database files")] : List (val × GoString × GoString)) →
    EtcdGrove.errorsNewVarInit (GF := GF) init X msg

end go_etcd_io.bbolt.errors
end opaqueInits

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.bbolt.errors.Assumptions]
variable [EtcdGrove.ErrorStringLeaf]

namespace go_etcd_io.bbolt.errors

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.bbolt.errors get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply (errorsNewVarsInit ErrDatabaseNotOpen.init ErrDatabaseNotOpen go!"database not open" (by mem_tac))
    as ⟨%xErrDatabaseNotOpen, HErrDatabaseNotOpen, #MErrDatabaseNotOpen⟩
  wp_apply (errorsNewVarsInit ErrInvalid.init ErrInvalid go!"invalid database" (by mem_tac))
    as ⟨%xErrInvalid, HErrInvalid, #MErrInvalid⟩
  wp_apply (errorsNewVarsInit ErrInvalidMapping.init ErrInvalidMapping go!"database isn't correctly mapped" (by mem_tac))
    as ⟨%xErrInvalidMapping, HErrInvalidMapping, #MErrInvalidMapping⟩
  wp_apply (errorsNewVarsInit ErrVersionMismatch.init ErrVersionMismatch go!"version mismatch" (by mem_tac))
    as ⟨%xErrVersionMismatch, HErrVersionMismatch, #MErrVersionMismatch⟩
  wp_apply (errorsNewVarsInit ErrChecksum.init ErrChecksum go!"checksum error" (by mem_tac))
    as ⟨%xErrChecksum, HErrChecksum, #MErrChecksum⟩
  wp_apply (errorsNewVarsInit ErrTimeout.init ErrTimeout go!"timeout" (by mem_tac))
    as ⟨%xErrTimeout, HErrTimeout, #MErrTimeout⟩
  wp_apply (errorsNewVarsInit ErrTxNotWritable.init ErrTxNotWritable go!"tx not writable" (by mem_tac))
    as ⟨%xErrTxNotWritable, HErrTxNotWritable, #MErrTxNotWritable⟩
  wp_apply (errorsNewVarsInit ErrTxClosed.init ErrTxClosed go!"tx closed" (by mem_tac))
    as ⟨%xErrTxClosed, HErrTxClosed, #MErrTxClosed⟩
  wp_apply (errorsNewVarsInit ErrDatabaseReadOnly.init ErrDatabaseReadOnly go!"database is in read-only mode" (by mem_tac))
    as ⟨%xErrDatabaseReadOnly, HErrDatabaseReadOnly, #MErrDatabaseReadOnly⟩
  wp_apply (errorsNewVarsInit ErrFreePagesNotLoaded.init ErrFreePagesNotLoaded go!"free pages are not pre-loaded" (by mem_tac))
    as ⟨%xErrFreePagesNotLoaded, HErrFreePagesNotLoaded, #MErrFreePagesNotLoaded⟩
  wp_apply (errorsNewVarsInit ErrBucketNotFound.init ErrBucketNotFound go!"bucket not found" (by mem_tac))
    as ⟨%xErrBucketNotFound, HErrBucketNotFound, #MErrBucketNotFound⟩
  wp_apply (errorsNewVarsInit ErrBucketExists.init ErrBucketExists go!"bucket already exists" (by mem_tac))
    as ⟨%xErrBucketExists, HErrBucketExists, #MErrBucketExists⟩
  wp_apply (errorsNewVarsInit ErrBucketNameRequired.init ErrBucketNameRequired go!"bucket name required" (by mem_tac))
    as ⟨%xErrBucketNameRequired, HErrBucketNameRequired, #MErrBucketNameRequired⟩
  wp_apply (errorsNewVarsInit ErrKeyRequired.init ErrKeyRequired go!"key required" (by mem_tac))
    as ⟨%xErrKeyRequired, HErrKeyRequired, #MErrKeyRequired⟩
  wp_apply (errorsNewVarsInit ErrKeyTooLarge.init ErrKeyTooLarge go!"key too large" (by mem_tac))
    as ⟨%xErrKeyTooLarge, HErrKeyTooLarge, #MErrKeyTooLarge⟩
  wp_apply (errorsNewVarsInit ErrValueTooLarge.init ErrValueTooLarge go!"value too large" (by mem_tac))
    as ⟨%xErrValueTooLarge, HErrValueTooLarge, #MErrValueTooLarge⟩
  wp_apply (errorsNewVarsInit ErrMaxSizeReached.init ErrMaxSizeReached go!"database reached maximum size" (by mem_tac))
    as ⟨%xErrMaxSizeReached, HErrMaxSizeReached, #MErrMaxSizeReached⟩
  wp_apply (errorsNewVarsInit ErrIncompatibleValue.init ErrIncompatibleValue go!"incompatible value" (by mem_tac))
    as ⟨%xErrIncompatibleValue, HErrIncompatibleValue, #MErrIncompatibleValue⟩
  wp_apply (errorsNewVarsInit ErrSameBuckets.init ErrSameBuckets go!"the source and target are the same bucket" (by mem_tac))
    as ⟨%xErrSameBuckets, HErrSameBuckets, #MErrSameBuckets⟩
  wp_apply (errorsNewVarsInit ErrDifferentDB.init ErrDifferentDB go!"the source and target buckets are in different database files" (by mem_tac))
    as ⟨%xErrDifferentDB, HErrDifferentDB, #MErrDifferentDB⟩
  ipersist HErrBucketNotFound
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
  ipureintro
  exact ⟨⟨_, _, rfl, rfl⟩, EtcdGrove.ErrorStringLeaf.leaf _, EtcdGrove.ErrorStringLeaf.noIs⟩


end go_etcd_io.bbolt.errors

end init

end Perennial
