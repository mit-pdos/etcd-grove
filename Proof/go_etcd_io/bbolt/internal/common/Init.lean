/-
Package initialization of `go.etcd.io/bbolt/internal/common` and of the packages it
imports that Perennial gives no initialization predicate (`os`, `hash/fnv`, bbolt's
`errors`): being initialized says nothing beyond the imports' initialization.
-/
module

public import GeneratedProof.go_etcd_io.bbolt.internal.common
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.fmt
public import Perennial.Proof.sort_proof.sort_init
public import Perennial.Proof.io
public import Perennial.Proof.runtime
public import Perennial.Proof.time
public import Perennial.Proof.strings
public import Perennial.Proof.unsafe
public import Perennial.Proof.errors

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance os_isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.os :=
  define_is_pkg_init iprop(True)
instance os_get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.os :=
  build_get_is_pkg_init_wf

instance fnv_isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.hash.fnv :=
  define_is_pkg_init iprop(True)
instance fnv_get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.hash.fnv :=
  build_get_is_pkg_init_wf

/-- An `error` value as `errors.New` builds one: an interface holding a pointer (so
comparing it with another error does not get stuck). -/
def IsNewErr (e : GoInterface) : Prop :=
  ∃ (t : go.GoType) (p : Loc), e = interface.mkOk (go.GoType.PointerType t) #p

/-- The package variables of bbolt's `errors`, all `errors.New(..)` (`errors/errors.go`). -/
def bboltErrorNames : List GoString :=
  [go_etcd_io.bbolt.errors.ErrDatabaseNotOpen,
    go_etcd_io.bbolt.errors.ErrInvalid,
    go_etcd_io.bbolt.errors.ErrInvalidMapping,
    go_etcd_io.bbolt.errors.ErrVersionMismatch,
    go_etcd_io.bbolt.errors.ErrChecksum,
    go_etcd_io.bbolt.errors.ErrTimeout,
    go_etcd_io.bbolt.errors.ErrTxNotWritable,
    go_etcd_io.bbolt.errors.ErrTxClosed,
    go_etcd_io.bbolt.errors.ErrDatabaseReadOnly,
    go_etcd_io.bbolt.errors.ErrFreePagesNotLoaded,
    go_etcd_io.bbolt.errors.ErrBucketNotFound,
    go_etcd_io.bbolt.errors.ErrBucketExists,
    go_etcd_io.bbolt.errors.ErrBucketNameRequired,
    go_etcd_io.bbolt.errors.ErrKeyRequired,
    go_etcd_io.bbolt.errors.ErrKeyTooLarge,
    go_etcd_io.bbolt.errors.ErrValueTooLarge,
    go_etcd_io.bbolt.errors.ErrMaxSizeReached,
    go_etcd_io.bbolt.errors.ErrIncompatibleValue,
    go_etcd_io.bbolt.errors.ErrSameBuckets,
    go_etcd_io.bbolt.errors.ErrDifferentDB]

/-- bbolt's `errors` is initialized: each of its variables holds, for good (nothing but
the initializer writes them), a non-nil error made by `errors.New`. As for the other
packages of this repository, nothing proves it from `initialize'`. -/
def bboltErrorsInit : IProp GF :=
  iprop([∗list] x ∈ bboltErrorNames,
    ∃ (e : GoInterface), (globalAddr x ↦□ e : IProp GF) ∗ ⌜IsNewErr e⌝)

instance errors_isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.bbolt.errors :=
  define_is_pkg_init bboltErrorsInit
instance errors_get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.bbolt.errors :=
  build_get_is_pkg_init_wf

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.bbolt.internal.common :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.bbolt.internal.common :=
  build_get_is_pkg_init_wf

/-- One of bbolt's errors, from its package's initialization. -/
theorem bboltError_access (x : GoString) (hx : x ∈ bboltErrorNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors ⊢
      iprop(∃ (e : GoInterface), (globalAddr x ↦□ e : IProp GF) ∗ ⌜IsNewErr e⌝) :=
  (isPkgInit_access (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors).trans
    (BigSepL.bigSepL_mem (Φ := fun x => iprop(∃ (e : GoInterface),
      (globalAddr x ↦□ e : IProp GF) ∗ ⌜IsNewErr e⌝)) hx)

end init

end bbolt
end EtcdGrove
end Perennial
