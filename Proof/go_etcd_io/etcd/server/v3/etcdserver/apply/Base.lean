/-
Package initialization for etcd's server `apply` package (`server/v3/etcdserver/apply`: the
applier chain between the apply thread and the `txn` package), and the instances of the
packages it reaches that no other `Base` states. Every other package it imports already has its
instance: the txn package's (`txn/Base.lean`), mvcc's (`storage/mvcc/Base.lean`: mvcc,
`traceutil`, `lease`, prometheus), the cache's (`cache/v3/Base.lean`: `zap`, `proto`,
`etcdserverpb`, `membershippb`, `authpb`), the server's (`etcdserver/Base.lean`: `cindex`,
`backend`), `etcdserver/errors/Base.lean`, and Perennial's (`context`, `errors`, `sync`, `time`).

The instances below are `True` (the packages are translated names-only or types-only); until
2026-10-12 they were in the server's `BaseApply.lean`, which now imports this file: the apply
package must not import the server's translation (the server's proofs will import the apply
package's, unit 3 of the apply plan).

As there, the package facts are assumptions about package initialization, not proved from
`initialize'` (the package's initializer runs the axiomatized initializer of `alarms` and its
`init`, `prometheus.MustRegister(alarms)`). `applyInit` states what the translated code reads of
the package variables: its own gauge `alarms` (a `*prometheus.GaugeVec`, read by the backend's
`Alarm`), and one error variable of an imported package it returns, `etcdserver/errors`'
`ErrCorrupt` (the corrupt applier), a fixed non-nil error, stated here rather than in its
package's facts (`ErrNoSpace` only, the server's), as the txn package does for its foreign
errors; `ErrNoSpace` (quota, capped) is `errors`' fact and mvcc's `ErrCompacted` (`dispatch`)
mvcc's.
-/
module

public import Code.go_etcd_io.etcd.server.v3.etcdserver.apply
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.apply
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.errors.Base
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.sync
public import Perennial.Proof.time
public import Perennial.Proof.context
public import Perennial.Proof.errors

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace EtcdGrove

section errIs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- **An `errors.New` error, as `errors.Is` sees it**: a pointer error (an `*errorString`,
`errors.IsPointerError`: Go's `==` on it is Lean's equality), a leaf of an error tree without an
`Is` method (`*errorString` has only `Error`; the model's method sets are uninterpreted, so this
is stated, not derived; as the recipes' `errNewLeaf`). -/
def errLeaf (e : GoInterfaceOk) : Prop :=
  _root_.Perennial.errors.IsPointerError e ∧ _root_.Perennial.errors.isLeafError e ∧
    methodSet e.ty !! go!"Is" ≠ some (go.Signature [go.error] false [go.bool])

end errIs

section errIsIProp
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **An error the applier returns, as `errors.Is` sees it** (persistent): for any target, the
error is in an error tree (`errors.errorIsTree`: the specs of its `Is` and `Unwrap` methods, if
it has them, which return without panicking), whose errors of the target's type hold pointers
if the target does (`errors.TreeTyped`, Go's typing). What `errors.Is(ar.Err, ErrNoSpace)`
(the server's `applyEntryNormal`) and `errors.Is(ar.Err, mvcc.ErrCompacted)` (`dispatch`'s
metrics) need of it (`errors.wp_Is`). As `clientErrIs` for the client's errors. Defined here,
in the apply package's `Base` (moved from the server's `InvApplier.lean`, 2026-10-12, the merge
of the apply package's unit 2), so that the apply package states it and the server's
`resultOk` uses the same. `nil` has it (`applyErrIs_nil`), and so has an `errors.New` error
(`applyErrIs_leaf`). -/
def applyErrIs (err : GoInterface) : IProp GF :=
  iprop(□ ∀ target : GoInterface, ∃ (S : GoInterface → Prop) (M : GoInterfaceOk → Prop),
    _root_.Perennial.errors.errorIsTree (GF := GF) S M target ∗
    ⌜S err ∧ _root_.Perennial.errors.TreeTyped S target⌝)

instance applyErrIs_persistent (err : GoInterface) :
    Persistent (applyErrIs (GF := GF) err) := by
  unfold applyErrIs; infer_instance

/-- `nil` is in the empty tree. -/
theorem applyErrIs_nil : ⊢ applyErrIs (GF := GF) GoInterface.nil := by
  iunfold applyErrIs
  iintro !> %target
  iexists (· = GoInterface.nil), (fun _ => False)
  isplitl
  · iintro !> %ii %h
    cases h
  ipureintro
  refine ⟨rfl, ?_⟩
  intro ii tii h
  cases h

/-- An `errors.New` error is a one-error tree. -/
theorem applyErrIs_leaf [_root_.Perennial.errors.Assumptions] (e : GoInterfaceOk) (h : errLeaf e) :
    ⊢ applyErrIs (GF := GF) (GoInterface.ok e) := by
  iunfold applyErrIs
  iintro !> %target
  iexists (· = GoInterface.ok e), (fun _ => False)
  isplitl
  · iapply _root_.Perennial.errors.errorIsTree_leaf e (fun _ => False) target h.2.1 h.2.2
  ipureintro
  exact ⟨rfl, _root_.Perennial.errors.treeTyped_pointer e target h.1⟩

/-- **The error variable `g` holds an `errors.New` error** (persistent; a package fact). -/
def errVarLeaf (g : GoString) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, globalAddr g ↦□ GoInterface.ok e ∗ ⌜errLeaf e⌝)

instance errVarLeaf_persistent (g : GoString) : Persistent (errVarLeaf (GF := GF) g) := by
  unfold errVarLeaf; infer_instance

/-- The error the variable `g` holds (as the txn package's `errVarIs` states it) is one
`errors.Is` can take, if `g` holds an `errors.New` error. -/
theorem errVar_applyErrIs [_root_.Perennial.errors.Assumptions] (g : GoString) (err : GoInterface) :
    errVarLeaf (GF := GF) g ⊢
      (∃ e : GoInterfaceOk, globalAddr g ↦□ GoInterface.ok e ∗ ⌜err = GoInterface.ok e⌝) -∗
      applyErrIs err := by
  iunfold errVarLeaf
  iintro ⟨%e, #He, %hl⟩ ⟨%e', #He', %heq⟩
  icombine He He' gives %h
  subst heq
  cases h
  iapply applyErrIs_leaf e hl

/-- The variable `g`'s error, one `errors.Is` can take. -/
theorem errVarLeaf_get [_root_.Perennial.errors.Assumptions] (g : GoString) :
    errVarLeaf (GF := GF) g ⊢
      ∃ e : GoInterfaceOk, globalAddr g ↦□ GoInterface.ok e ∗ applyErrIs (GoInterface.ok e) := by
  iunfold errVarLeaf
  iintro ⟨%e, #He, %hl⟩
  iexists e
  iframe He
  iapply applyErrIs_leaf e hl

end errIsIProp

end EtcdGrove

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

-- `github.com/Masterminds/semver/v3` (names only: `MustParse`, `Version.LessThan`/`String`)
namespace github_com.Masterminds.semver.v3

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.Masterminds.semver.v3 :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.Masterminds.semver.v3 :=
  build_get_is_pkg_init_wf

end github_com.Masterminds.semver.v3

-- `etcdserver/api` (names only: `UpdateCapability`, passed as a value)
namespace go_etcd_io.etcd.server.v3.etcdserver.api

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.api

-- `etcdserver/version` (types only: `DowngradeInfo`)
namespace go_etcd_io.etcd.server.v3.etcdserver.version

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.version :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.version :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.version

-- `client/pkg/v3/types` (names only: `ID.String`)
namespace go_etcd_io.etcd.client.pkg.v3.types

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.client.pkg.v3.types

-- `pkg/v3/pbutil` (names only: `MustUnmarshalMessage`)
namespace go_etcd_io.etcd.pkg.v3.pbutil

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.pkg.v3.pbutil

-- `pkg/v3/wait` (names only: the `Wait` interface)
namespace go_etcd_io.etcd.pkg.v3.wait

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.pkg.v3.wait

-- `server/v3/auth` (names only: the `AuthStore` interface, `AuthInfo`)
namespace go_etcd_io.etcd.server.v3.auth

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.auth

-- `api/v3alarm` (names only: `AlarmStore`)
namespace go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm

-- `api/membership` (names only: `RaftCluster`)
namespace go_etcd_io.etcd.server.v3.etcdserver.api.membership

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.api.membership

-- `server/v3/storage` (names only: `Quota`, `BackendQuota`)
namespace go_etcd_io.etcd.server.v3.storage

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.storage

-- raft v3.7's `raftpb` (etcd's own raft dependency; types only)
namespace go_etcd_io.raft.v3.raftpb

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb :=
  build_get_is_pkg_init_wf

end go_etcd_io.raft.v3.raftpb

namespace go_etcd_io.etcd.server.v3.etcdserver.apply

/-- **The error variables the applier returns, or compares its result's error with, hold
`errors.New` errors** (`EtcdGrove.errVarLeaf`: leaves of an error tree, pointer errors): its own
wrappers' `ErrCorrupt` and `ErrNoSpace` (`etcdserver/errors`), the txn package's checks'
`ErrKeyNotFound` (`etcdserver/errors`) and `lease.ErrLeaseNotFound`, mvcc's `ErrFutureRev` and
`ErrCompacted` (the range check's; `ErrCompacted` the target of `dispatch`'s `errors.Is`). An
assumption about the initialization of those packages (each `var X = errors.New(...)`), stated
here rather than in their packages' facts (which state each a fixed non-nil error, and which
their proofs destructure by position), as the txn package states its foreign errors; what
`apply.Apply`'s result needs to be one `errors.Is` can take (`applyErrIs`). -/
abbrev applyErrVars : IProp GF :=
  iprop(EtcdGrove.errVarLeaf go_etcd_io.etcd.server.v3.etcdserver.errors.ErrCorrupt ∗
    EtcdGrove.errVarLeaf go_etcd_io.etcd.server.v3.etcdserver.errors.ErrNoSpace ∗
    EtcdGrove.errVarLeaf go_etcd_io.etcd.server.v3.etcdserver.errors.ErrKeyNotFound ∗
    EtcdGrove.errVarLeaf go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound ∗
    EtcdGrove.errVarLeaf go_etcd_io.etcd.server.v3.storage.mvcc.ErrFutureRev ∗
    EtcdGrove.errVarLeaf go_etcd_io.etcd.server.v3.storage.mvcc.ErrCompacted)

/-- The apply package's facts: its gauge `alarms` holds a fixed `*prometheus.GaugeVec` (whose
`WithLabelValues` is the trust boundary, `Spec/github_com/prometheus/client_golang/prometheus/
GaugeVec__WithLabelValues.lean`), `etcdserver/errors.ErrCorrupt` a fixed non-nil error, and the
error variables it returns `errors.New` errors (`applyErrVars`). -/
abbrev applyInit : IProp GF :=
  iprop((∃ gv : Loc, globalAddr alarms ↦□ gv) ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.server.v3.etcdserver.errors.ErrCorrupt ↦□ GoInterface.ok e) ∗
    applyErrVars)

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply :=
  define_is_pkg_init applyInit
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.apply

end init

namespace EtcdGrove

section errVars
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [_root_.Perennial.errors.Assumptions]

/-- `ErrCorrupt`'s error, one `errors.Is` can take (`applyErrVars`). -/
theorem applyErrVars_corrupt :
    go_etcd_io.etcd.server.v3.etcdserver.apply.applyErrVars (GF := GF) ⊢
      ∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.server.v3.etcdserver.errors.ErrCorrupt ↦□
        GoInterface.ok e ∗ applyErrIs (GoInterface.ok e) := by
  iintro ⟨H, -⟩
  iapply errVarLeaf_get $$ H

/-- `ErrNoSpace`'s error, one `errors.Is` can take (`applyErrVars`). -/
theorem applyErrVars_noSpace :
    go_etcd_io.etcd.server.v3.etcdserver.apply.applyErrVars (GF := GF) ⊢
      ∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.server.v3.etcdserver.errors.ErrNoSpace ↦□
        GoInterface.ok e ∗ applyErrIs (GoInterface.ok e) := by
  iintro ⟨-, H, -⟩
  iapply errVarLeaf_get $$ H

end errVars

end EtcdGrove

end Perennial
