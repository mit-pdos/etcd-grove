/-
Package initialization instances for `go.etcd.io/etcd/client/v3/experimental/recipes` (the
counterpart of `Proof/go_etcd_io/etcd/client/v3/concurrency/Base.lean`, whose instances, and the
cache's `Base.lean`'s for `clientv3`, the protobuf packages, grpc and zap, it reuses). Its
standard-library imports (`context`, `errors`, `fmt`, `strings`, `time`) are Perennial's.

The package's facts (`recipesInit`): its four errors `ErrKeyExists`, `ErrWaitMismatch`,
`ErrTooManyClients`, `ErrNoWatcher` hold fixed non-nil errors (`errors.New`), `ErrKeyExists` one
as `errors.Is` sees it (`errNewLeaf`: a pointer error, a leaf without an `Is` method). As in the
cache's `Base.lean`, this is an assumption about package initialization, not proved from
`initialize'`.
-/
module

public import Code.go_etcd_io.etcd.client.v3.experimental.recipes
public import GeneratedProof.go_etcd_io.etcd.client.v3.experimental.recipes
public import Proof.go_etcd_io.etcd.client.v3.concurrency.Base
public import Perennial.Proof.errors

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace go_etcd_io.etcd.client.v3.experimental.recipes

section errNewLeaf
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- **An `errors.New` error, as `errors.Is` sees it**: a pointer error (an `*errorString`,
`errors.IsPointerError`: Go's `==` on it is Lean's equality), a leaf of an error tree without an
`Is` method (`*errorString` has only `Error`; the model's method sets are uninterpreted, so this
is stated, not derived). -/
def errNewLeaf (e : GoInterfaceOk) : Prop :=
  errors.IsPointerError e ∧ errors.isLeafError e ∧
    methodSet e.ty !! go!"Is" ≠ some (go.Signature [go.error] false [go.bool])

end errNewLeaf

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The package's facts: its four errors (`ErrKeyExists`, `ErrWaitMismatch`,
`ErrTooManyClients`, `ErrNoWatcher`) each hold a fixed non-nil error (`errors.New`), for good;
`ErrKeyExists`'s is an `errors.New` error as `errors.Is` sees it (`errNewLeaf`; what
`newUniqueKV`'s `errors.Is(err, ErrKeyExists)` needs). -/
abbrev recipesInit : IProp GF :=
  iprop((∃ e : GoInterfaceOk, globalAddr ErrKeyExists ↦□ GoInterface.ok e ∗ ⌜errNewLeaf e⌝) ∗
    (∃ e : GoInterfaceOk, globalAddr ErrWaitMismatch ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr ErrTooManyClients ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr ErrNoWatcher ↦□ GoInterface.ok e))

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes :=
  define_is_pkg_init recipesInit
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes :=
  build_get_is_pkg_init_wf

end init

end go_etcd_io.etcd.client.v3.experimental.recipes

end Perennial
