/-
# `go.etcd.io/bbolt/errors`: the error values (integration I7)

The package declares bbolt's error variables (`var ErrBucketNotFound = errors.New(...)`, ...); its
initializer sets each to a fresh `*errors.errorString`. Its users compare them (`errors.Is`, `==`):
bbolt's public API returns them (batch 4c), `internal/common`'s `Meta.Validate` returns
`ErrInvalid`, `ErrVersionMismatch`, `ErrChecksum` (batch 4d), etcd's backend tests
`ErrBucketNotFound` (batch 4a).

Moved here from `Spec/go_etcd_io/bbolt/Api.lean` at integration (I7): the laws are facts of this
package's initialization, which both `bbolt` and `internal/common` (a dependency of `bbolt`) use;
`Bbolt` re-exports the names (`Bbolt.errIs`, `Bbolt.isErr`, `Bbolt.bboltErrNames`).

* `errIs g err` (transparent): `err` is the value of the variable `g` (read-only after `init`).
* `isErr g err`: and it is non-nil.
* Laws: `errIs_init` (after the package's initialization each listed variable holds some value,
  read-only), `errIs_distinct` (those values are non-nil and pairwise distinct: each is a distinct
  allocation of `errors.New`). Intended proof: the package's initializer's `errors.New` calls
  (Perennial's `errors.New` spec: a fresh pointer), recorded in the package's `pkgInitDef`.
-/
module

public import GeneratedProof.go_etcd_io.bbolt.errors
public import Spec.PkgInit.go_etcd_io.bbolt.errors

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace BboltErrors

open Iris Iris.BI

section contracts
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `err` is the value of `go.etcd.io/bbolt/errors`' variable `g` (`ErrBucketNotFound`, ...). -/
def errIs (g : GoString) (err : GoInterface) : IProp GF :=
  iprop(globalAddr g ↦□ err)

/-- `err` is the (non-nil) error `g` of `go.etcd.io/bbolt/errors`. -/
def isErr (g : GoString) (err : GoInterface) : IProp GF :=
  iprop(⌜err ≠ interface.nil⌝ ∗ errIs g err)

end contracts

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The error variables of `go.etcd.io/bbolt/errors` that bbolt's public API (4c) and
`Meta.Validate` (4d) return. -/
def bboltErrNames : List GoString :=
  [go_etcd_io.bbolt.errors.ErrBucketNotFound, go_etcd_io.bbolt.errors.ErrBucketExists,
   go_etcd_io.bbolt.errors.ErrIncompatibleValue, go_etcd_io.bbolt.errors.ErrTxNotWritable,
   go_etcd_io.bbolt.errors.ErrTxClosed, go_etcd_io.bbolt.errors.ErrDatabaseNotOpen,
   go_etcd_io.bbolt.errors.ErrKeyRequired, go_etcd_io.bbolt.errors.ErrKeyTooLarge,
   go_etcd_io.bbolt.errors.ErrBucketNameRequired, go_etcd_io.bbolt.errors.ErrDatabaseReadOnly,
   go_etcd_io.bbolt.errors.ErrInvalid, go_etcd_io.bbolt.errors.ErrVersionMismatch,
   go_etcd_io.bbolt.errors.ErrChecksum]

/-- **bbolt's error variables hold their values after initialization** (`errors.New`'s in the
package's initializer). The request: `req/go_etcd_io_bbolt_errors.md` (from 4d; answered by 4c). -/
def errIs_init.spec : Prop :=
  ∀ (g : GoString), g ∈ bboltErrNames →
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors ⊢ ∃ e : GoInterface, errIs g e

/-- The values `errIs_init` gives are non-nil and pairwise distinct. -/
def errIs_distinct.spec : Prop :=
  ∀ (g g' : GoString) (e e' : GoInterface), g ∈ bboltErrNames → g' ∈ bboltErrNames →
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors ∗ errIs g e ∗ errIs g' e' ⊢
      ⌜e ≠ interface.nil ∧ (g ≠ g' → e ≠ e')⌝

end laws

end BboltErrors
end EtcdGrove
end Perennial
