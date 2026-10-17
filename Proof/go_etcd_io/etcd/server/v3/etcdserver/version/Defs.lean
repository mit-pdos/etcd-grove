/-
The downgrade manager's predicates (`server/v3/etcdserver/version`, `version.go`; the downgrade
API, etcd-io/etcd#22575, 2026-10-16). Lean-first (no Rocq counterpart).

* `version.serverOk si γcv` (persistent): the contract of the manager's `Server` interface value
  `si` (the server's `serverVersionAdapter`, names-only: its methods are calls of the server and
  its `*RaftCluster`), for the methods the downgrade API calls:
  - `LinearizableReadNotify(ctx)` returns some error (the read loop's wait);
  - `GetClusterVersion()` returns the cluster's version: `nil` only before the version is known,
    and non-`nil` once the caller holds the witness `monoNatLbOwn γcv 1` (the cluster version
    goes from `nil` to non-`nil` once and stays so: the contract the server's `start` already
    rests on, `clusterVersionOk`, here for the adapter's `s.cluster.Version()`);
  - `GetDowngradeInfo()` returns a fresh `*DowngradeInfo`, not `nil` (`RaftCluster.DowngradeInfo`
    copies its field, or returns `&DowngradeInfo{Enabled: false}` when it is unset);
  - `DowngradeEnable(ctx, tv)`, `tv` not `nil` (the adapter calls `tv.String()`), and
    `DowngradeCancel(ctx)` return some error (a raft proposal of the downgrade info).
* `version.managerIs m si` (persistent): the manager `m`'s `Server` field holds `si`.
* `version.dgErrVars` (persistent): the three error variables the manager returns hold some value
  (the package's facts are `True`, `apply/Base.lean`: an assumption about the package's
  initialization, as the server's `srvErrVars`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Perennial.Ghost.MonoNat

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The manager's `Server`** (persistent; a trust-boundary contract, see the file header). -/
def version.serverOk (si : GoInterface) (γcv : GName) : IProp GF :=
  iprop(∃ sv : GoInterfaceOk, ⌜si = GoInterface.ok sv⌝ ∗
    □ (∀ ctx : GoInterface,
      {{ True }} (App (Val #(methods sv.ty go!"LinearizableReadNotify" sv.v)) (Val #ctx))
      {{ (err : GoInterface), RET #err; True }}) ∗
    □ (∀ known : Bool,
      {{ if known then monoNatLbOwn γcv 1 else True }}
        (App (Val #(methods sv.ty go!"GetClusterVersion" sv.v)) (Val #()))
      {{ (v : Loc), RET #v; ⌜v = null ∧ known = false⌝ ∨ ⌜v ≠ null⌝ ∗ monoNatLbOwn γcv 1 }}) ∗
    □ ({{ True }} (App (Val #(methods sv.ty go!"GetDowngradeInfo" sv.v)) (Val #()))
      {{ (d : Loc), RET #d; ⌜d ≠ null⌝ ∗
          ∃ di : go_etcd_io.etcd.server.v3.etcdserver.version.DowngradeInfo, d ↦ di }}) ∗
    □ (∀ (ctx : GoInterface) (tv : Loc),
      {{ ⌜tv ≠ null⌝ }} (App (App (Val #(methods sv.ty go!"DowngradeEnable" sv.v)) (Val #ctx)) (Val #tv))
      {{ (err : GoInterface), RET #err; True }}) ∗
    □ (∀ ctx : GoInterface,
      {{ True }} (App (Val #(methods sv.ty go!"DowngradeCancel" sv.v)) (Val #ctx))
      {{ (err : GoInterface), RET #err; True }}))

instance version.serverOk_persistent (si : GoInterface) (γcv : GName) :
    Persistent (version.serverOk (GF := GF) si γcv) := by
  unfold version.serverOk; infer_instance

/-- The manager `m`'s `s` field holds `si` (read-only). -/
def version.managerIs (m : Loc) (si : GoInterface) : IProp GF :=
  iprop(structFieldRef go_etcd_io.etcd.server.v3.etcdserver.version.Manager go!"s" m ↦□ si)

instance version.managerIs_persistent (m : Loc) (si : GoInterface) :
    Persistent (version.managerIs (GF := GF) m si) := by
  unfold version.managerIs; infer_instance

/-- **The manager's error variables hold some value** (persistent; see the file header). -/
def version.dgErrVars : IProp GF :=
  iprop((∃ e : GoInterface, globalAddr
      go_etcd_io.etcd.server.v3.etcdserver.version.ErrInvalidDowngradeTargetVersion ↦□ e) ∗
    (∃ e : GoInterface, globalAddr
      go_etcd_io.etcd.server.v3.etcdserver.version.ErrDowngradeInProcess ↦□ e) ∗
    (∃ e : GoInterface, globalAddr
      go_etcd_io.etcd.server.v3.etcdserver.version.ErrNoInflightDowngrade ↦□ e))

instance version.dgErrVars_persistent : Persistent (version.dgErrVars (GF := GF)) := by
  unfold version.dgErrVars; infer_instance

end defs

end EtcdGrove
end Perennial
