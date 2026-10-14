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
public import Perennial.Proof.log

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

/-- **An error's message**: the error `ei`'s `Error()` returns (a string). What `togRPCError`
needs of a non-nil error it does not map (`status.Error(codes.Unknown, err.Error())`). An
`errors.New` error's (`errors.wp_New`: it returns the message). -/
def errMsgOk (ei : GoInterfaceOk) : IProp GF :=
  iprop({{ True }} (App (Val #(methods ei.ty go!"Error" ei.v)) (Val #()))
    {{ (msg : GoString), RET #msg; True }})

instance errMsgOk_persistent (ei : GoInterfaceOk) : Persistent (errMsgOk (GF := GF) ei) := by
  unfold errMsgOk; infer_instance

/-- **What the gRPC layer needs of an error besides its tree** (persistent): `nil`, or a safe key
of `togRPCError`'s error map (`SafeMapKey`: comparing it with itself does not panic; a pointer
error is one, `safeMapKey_ptrErr`) whose `Error()` returns (`errMsgOk`). -/
def errKeyMsg (err : GoInterface) : IProp GF :=
  iprop(⌜err = GoInterface.nil⌝ ∨
    (⌜SafeMapKey (GF := GF) go.error err⌝ ∗ ∃ ei : GoInterfaceOk, ⌜err = GoInterface.ok ei⌝ ∗
      errMsgOk ei))

instance errKeyMsg_persistent (err : GoInterface) : Persistent (errKeyMsg (GF := GF) err) := by
  unfold errKeyMsg; infer_instance

/-- A target `errors.Is` can compare with by `==` in the model (Perennial's `errors.wp_Is`): `nil`
or a pointer error. -/
def ptrTarget [FfiSyntax] [GoGlobalContext] (target : GoInterface) : Prop :=
  ∀ tii, target = GoInterface.ok tii → _root_.Perennial.errors.IsPointerError tii

/-- **An error the applier returns, as `errors.Is` and the gRPC layer see it** (persistent): for
any target, the error is in an error tree (`errors.errorIsTree`: the specs of its `Is` and
`Unwrap` methods, if it has them, which return without panicking), whose errors of the target's
type hold pointers if the target is a pointer error (`errors.TreeTyped`, Go's typing, for the
targets `errors.wp_Is` takes, `ptrTarget`: 2026-10-13, the request path's unit 4a, so that
`context.DeadlineExceeded`, a struct error, is one; until then for every target, which no
non-pointer error meets at itself); and it is `nil` or a
safe map key whose `Error()` returns (`errKeyMsg`, what `togRPCError` needs: 2026-10-12, the
request path's unit 3a, so that every error the server's request path returns can go to the
gRPC layer). What `errors.Is(ar.Err, ErrNoSpace)` (the server's `applyEntryNormal`) and
`errors.Is(ar.Err, mvcc.ErrCompacted)` (`dispatch`'s metrics) need of it (`errors.wp_Is`,
through `applyErrIs_tree`). As `clientErrIs` for the client's errors. Defined here, in the apply
package's `Base` (moved from the server's `InvApplier.lean`, 2026-10-12, the merge of the apply
package's unit 2), so that the apply package states it and the server reads it
(`apply.resultErrOk`). `nil` has it (`applyErrIs_nil`), and so has an `errors.New` error
(`applyErrIs_leaf`). -/
def applyErrIs (err : GoInterface) : IProp GF :=
  iprop((□ ∀ target : GoInterface, ∃ (S : GoInterface → Prop) (M : GoInterfaceOk → Prop),
    _root_.Perennial.errors.errorIsTree (GF := GF) S M target ∗
    ⌜S err ∧ (ptrTarget target → _root_.Perennial.errors.TreeTyped S target)⌝) ∗ errKeyMsg err)

instance applyErrIs_persistent (err : GoInterface) :
    Persistent (applyErrIs (GF := GF) err) := by
  unfold applyErrIs; infer_instance

/-- The error tree of an `applyErrIs` error (what `errors.wp_Is` takes). -/
theorem applyErrIs_tree (err : GoInterface) :
    applyErrIs (GF := GF) err ⊢ □ ∀ target : GoInterface,
      ∃ (S : GoInterface → Prop) (M : GoInterfaceOk → Prop),
        _root_.Perennial.errors.errorIsTree (GF := GF) S M target ∗
        ⌜S err ∧ (ptrTarget target → _root_.Perennial.errors.TreeTyped S target)⌝ := by
  iunfold applyErrIs
  iintro ⟨#H, -⟩
  iexact H

/-- A pointer error is a safe map key at `error`: Go's `==` on two pointer errors of one type
compares the pointers. -/
theorem safeMapKey_ptrErr (e : GoInterfaceOk) (h : _root_.Perennial.errors.IsPointerError e) :
    SafeMapKey (GF := GF) go.error (GoInterface.ok e) := by
  obtain ⟨T, l, hT, hv⟩ := h
  obtain ⟨ty, v⟩ := e
  simp only at hT hv
  subst hT hv
  exact ⟨fun s E Φ => by iintro H; wp_auto; iapply H⟩

/-- `nil` is in the empty tree. -/
theorem applyErrIs_nil : ⊢ applyErrIs (GF := GF) GoInterface.nil := by
  iunfold applyErrIs
  isplitl
  rotate_left
  · iunfold errKeyMsg; ileft; ipureintro; rfl
  iintro !> %target
  iexists (· = GoInterface.nil), (fun _ => False)
  isplitl
  · iintro !> %ii %h
    cases h
  ipureintro
  refine ⟨rfl, fun _ => ?_⟩
  intro ii tii h
  cases h

/-- An `errors.New` error (whose `Error()` returns) is a one-error tree. -/
theorem applyErrIs_leaf [_root_.Perennial.errors.Assumptions] (e : GoInterfaceOk) (h : errLeaf e) :
    errMsgOk (GF := GF) e ⊢ applyErrIs (GoInterface.ok e) := by
  iintro #Hm
  iunfold applyErrIs
  isplitl
  rotate_left
  · iunfold errKeyMsg; iright
    isplitr
    · ipureintro; exact safeMapKey_ptrErr e h.1
    iexists e; iframe Hm; ipureintro; rfl
  iintro !> %target
  iexists (· = GoInterface.ok e), (fun _ => False)
  isplitl
  · iapply _root_.Perennial.errors.errorIsTree_leaf e (fun _ => False) target h.2.1 h.2.2
  ipureintro
  exact ⟨rfl, fun _ => _root_.Perennial.errors.treeTyped_pointer e target h.1⟩

/-- **A leaf error that is not a pointer** (as `context.DeadlineExceeded`'s
`deadlineExceededError{}`): no `Is`, `As` or `Unwrap` method, a dynamic type that is not a pointer
type (so no pointer target has its type: `TreeTyped` holds of every target `wp_Is` takes), a safe
key of a map (its `==` with itself does not panic), whose `Error()` returns. -/
theorem applyErrIs_valLeaf [_root_.Perennial.errors.Assumptions] (e : GoInterfaceOk) (hleaf : _root_.Perennial.errors.isLeafError e)
    (hIs : methodSet e.ty !! go!"Is" ≠ some (go.Signature [go.error] false [go.bool]))
    (hty : ∀ T, e.ty ≠ go.GoType.PointerType T)
    (hkey : SafeMapKey (GF := GF) go.error (GoInterface.ok e)) :
    errMsgOk (GF := GF) e ⊢ applyErrIs (GoInterface.ok e) := by
  iintro #Hm
  iunfold applyErrIs
  isplitl
  rotate_left
  · iunfold errKeyMsg; iright
    isplitr
    · ipureintro; exact hkey
    iexists e; iframe Hm; ipureintro; rfl
  iintro !> %target
  iexists (· = GoInterface.ok e), (fun _ => False)
  isplitl
  · iapply _root_.Perennial.errors.errorIsTree_leaf e (fun _ => False) target hleaf hIs
  ipureintro
  refine ⟨rfl, fun hpt ii tii hii ht hty' => ?_⟩
  cases hii
  obtain ⟨T, l, hT, -⟩ := hpt tii ht
  exact absurd (hty'.trans hT) (hty T)

/-- **The error variable `g` holds an `errors.New` error** (persistent; a package fact): a leaf
pointer error whose `Error()` returns (`errors.wp_New`; the message part since 2026-10-12, the
request path's unit 3a). -/
def errVarLeaf (g : GoString) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, globalAddr g ↦□ GoInterface.ok e ∗ ⌜errLeaf e⌝ ∗ errMsgOk e)

instance errVarLeaf_persistent (g : GoString) : Persistent (errVarLeaf (GF := GF) g) := by
  unfold errVarLeaf; infer_instance

/-- The error the variable `g` holds (as the txn package's `errVarIs` states it) is one
`errors.Is` can take, if `g` holds an `errors.New` error. -/
theorem errVar_applyErrIs [_root_.Perennial.errors.Assumptions] (g : GoString) (err : GoInterface) :
    errVarLeaf (GF := GF) g ⊢
      (∃ e : GoInterfaceOk, globalAddr g ↦□ GoInterface.ok e ∗ ⌜err = GoInterface.ok e⌝) -∗
      applyErrIs err := by
  iunfold errVarLeaf
  iintro ⟨%e, #He, %hl, #Hm⟩ ⟨%e', #He', %heq⟩
  icombine He He' gives %h
  subst heq
  cases h
  iapply applyErrIs_leaf e hl $$ Hm

/-- The variable `g`'s error, one `errors.Is` can take. -/
theorem errVarLeaf_get [_root_.Perennial.errors.Assumptions] (g : GoString) :
    errVarLeaf (GF := GF) g ⊢
      ∃ e : GoInterfaceOk, globalAddr g ↦□ GoInterface.ok e ∗ applyErrIs (GoInterface.ok e) := by
  iunfold errVarLeaf
  iintro ⟨%e, #He, %hl, #Hm⟩
  iexists e
  iframe He
  iapply applyErrIs_leaf e hl $$ Hm

end errIsIProp

end EtcdGrove

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

-- `github.com/Masterminds/semver/v3`: `server/v3/lease/Base.lean` (2026-10-13)

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

-- `pkg/v3/wait` (the `Wait` interface; with bodies since the request path, 2026-10-12: its
-- package has no variable the code reads)
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

-- `api/membership` (names only: `RaftCluster`; 2026-10-13, the request path's unit 4c: the package
-- variable `ClusterVersionMetrics`, which the server's `start` sets, holds some `*GaugeVec`)
namespace go_etcd_io.etcd.server.v3.etcdserver.api.membership

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership :=
  define_is_pkg_init iprop(∃ gv : Loc,
    globalAddr go_etcd_io.etcd.server.v3.etcdserver.api.membership.ClusterVersionMetrics ↦□ gv)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.api.membership

-- `etcdserver/api` (names only: `UpdateCapability`, passed as a value; the `Cluster` interface type,
-- whose methods name `types`, `membership` and `semver`: after their instances)
namespace go_etcd_io.etcd.server.v3.etcdserver.api

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.api

-- raft v3.7's `raftpb` (etcd's own raft dependency; types only)
namespace go_etcd_io.raft.v3.raftpb

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb :=
  build_get_is_pkg_init_wf

end go_etcd_io.raft.v3.raftpb

-- `server/v3/storage` (names only: `Quota`, `BackendQuota`)
namespace go_etcd_io.etcd.server.v3.storage

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.storage

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
