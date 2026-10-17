/-
**The downgrade API's contracts** (`v3_server.go`'s `Downgrade` and its three actions; etcd-io/etcd
PR #22575, 2026-10-16). Lean-first (no Rocq counterpart).

* `clusterVersionAt s γcv` (persistent): `s.ClusterVersion()` (names-only: `s.cluster.Version()`, a
  copy of the cluster's version under its mutex) returns `nil` until the cluster's version is
  known and non-`nil` from then on, the witness being `monoNatLbOwn γcv 1`: the contract
  `clusterVersionOk` of the server's `start` (`InvStart.lean`) with its ghost name exposed, so that
  the manager's `Server` (`version.serverOk`, the same cluster) is stated at the same name
  (`clusterVersionAt_ok`: it is `clusterVersionOk`). That the version, once set, is never `nil`
  again is the assumption: `RaftCluster.SetVersion` sets a non-`nil` version, and `Recover` (a
  snapshot's backend) reads it back from a backend in which it was saved.
* `srvVersionOk s γcv` (persistent): `s.Version()` (names-only: `serverversion.NewManager(s.Logger(),
  NewServerVersionAdapter(s))`) returns a manager over a `Server` meeting `version.serverOk` at
  `γcv`.
* `srvDgErrVars` (persistent): the errors the downgrade API returns itself
  (`ErrClusterVersionUnavailable`, `ErrUnknownMethod`, `ErrWrongDowngradeVersionFormat` of
  `etcdserver/errors`) hold non-`nil` errors (each `var X = errors.New(...)`: an assumption about that
  package's initialization, as `srvErrVars`).
* `dgErrIs g err`: `err` is the error variable `g`'s; `dgRequestIs r act ver`: the request's fields;
  `dgResp resp`: the response `resp`, owned.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvStart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.version.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.ClusterVersion()`, at the ghost name `γcv`** (persistent; see the file header). -/
def clusterVersionAt (s : Loc) (γcv : GName) : IProp GF :=
  iprop(□ (∀ known : Bool,
    {{ if known then monoNatLbOwn γcv 1 else True }}
      (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"ClusterVersion")) (Val #()))
    {{ (v : Loc), RET #v; ⌜v = null ∧ known = false⌝ ∨ ⌜v ≠ null⌝ ∗ monoNatLbOwn γcv 1 }}))

instance clusterVersionAt_persistent (s : Loc) (γcv : GName) :
    Persistent (clusterVersionAt (GF := GF) s γcv) := by
  unfold clusterVersionAt; infer_instance

/-- `clusterVersionAt` is the server's `clusterVersionOk` (`start`'s premise), at a name. -/
theorem clusterVersionAt_ok (s : Loc) (γcv : GName) :
    clusterVersionAt (GF := GF) s γcv ⊢ clusterVersionOk s := by
  iintro #H
  iunfold clusterVersionOk
  iexists γcv
  iunfold clusterVersionAt at H
  iexact H

/-- **`s.Version()`** (persistent; see the file header). -/
def srvVersionOk (s : Loc) (γcv : GName) : IProp GF :=
  iprop(□ ({{ True }}
      (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Version")) (Val #()))
    {{ (m : Loc), RET #m; ∃ si : GoInterface, version.managerIs m si ∗ version.serverOk si γcv }}))

instance srvVersionOk_persistent (s : Loc) (γcv : GName) :
    Persistent (srvVersionOk (GF := GF) s γcv) := by
  unfold srvVersionOk; infer_instance

/-- The error variable `g` holds a non-`nil` error. -/
def dgErrVar (g : GoString) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, globalAddr g ↦□ GoInterface.ok e)

instance dgErrVar_persistent (g : GoString) : Persistent (dgErrVar (GF := GF) g) := by
  unfold dgErrVar; infer_instance

/-- `err` is the error variable `g`'s (a non-`nil` error). -/
def dgErrIs (g : GoString) (err : GoInterface) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, globalAddr g ↦□ GoInterface.ok e ∗ ⌜err = GoInterface.ok e⌝)

instance dgErrIs_persistent (g : GoString) (err : GoInterface) :
    Persistent (dgErrIs (GF := GF) g err) := by
  unfold dgErrIs; infer_instance

/-- **The downgrade API's own errors** (persistent; see the file header). -/
def srvDgErrVars : IProp GF :=
  iprop(dgErrVar go_etcd_io.etcd.server.v3.etcdserver.errors.ErrClusterVersionUnavailable ∗
    dgErrVar go_etcd_io.etcd.server.v3.etcdserver.errors.ErrUnknownMethod ∗
    dgErrVar go_etcd_io.etcd.server.v3.etcdserver.errors.ErrWrongDowngradeVersionFormat)

instance srvDgErrVars_persistent : Persistent (srvDgErrVars (GF := GF)) := by
  unfold srvDgErrVars; infer_instance

/-- The request `r`'s fields the downgrade API reads, read-only: the action `act` and the target
version `ver`. -/
def dgRequestIs (r : Loc) (act : go_etcd_io.etcd.api.v3.etcdserverpb.DowngradeRequest_DowngradeAction)
    (ver : GoString) : IProp GF :=
  iprop(structFieldRef go_etcd_io.etcd.api.v3.etcdserverpb.DowngradeRequest go!"Action" r ↦□ act ∗
    structFieldRef go_etcd_io.etcd.api.v3.etcdserverpb.DowngradeRequest go!"Version" r ↦□ ver)

instance dgRequestIs_persistent (r : Loc) act (ver : GoString) :
    Persistent (dgRequestIs (GF := GF) r act ver) := by
  unfold dgRequestIs; infer_instance

/-- The response `resp`, owned. -/
def dgResp (resp : Loc) : IProp GF :=
  iprop(∃ dr : go_etcd_io.etcd.api.v3.etcdserverpb.DowngradeResponse, resp ↦ dr)

/-- **A downgrade action's outcome**, for a caller that knew the cluster version was known
(`known`: it held the witness) or not: `ErrClusterVersionUnavailable` with no response, only if
the caller did not know it; another error, with no response (`ek`: only once the version is known,
the witness); or a response, owned, once the version is known. -/
def dgOutcome (γcv : GName) (known ek : Bool) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜resp = null ∧ known = false⌝ ∗
      dgErrIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrClusterVersionUnavailable err) ∨
    (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ (if ek then monoNatLbOwn γcv 1 else True)) ∨
    (⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ dgResp resp ∗ monoNatLbOwn γcv 1))

/-- Forgetting that an error came once the version was known. -/
theorem dgOutcome_forget (γcv : GName) (known : Bool) (resp : Loc) (err : GoInterface) :
    dgOutcome (GF := GF) γcv known true resp err ⊢ dgOutcome γcv known false resp err := by
  iunfold dgOutcome
  iintro (H | ⟨%H, -⟩ | H)
  · ileft; iexact H
  · iright; ileft; isplitr
    · ipureintro; exact H
    · simp only [Bool.false_eq_true, ite_false]; itrivial
  · iright; iright; iexact H

end defs

end EtcdGrove
end Perennial
