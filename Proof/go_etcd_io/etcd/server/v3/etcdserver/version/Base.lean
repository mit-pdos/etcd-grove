/-
The version manager's downgrade API (`server/v3/etcdserver/version`, `version.go`; pr-verify
etcd#22589): the vocabulary of its specs. Lean-first (no Rocq counterpart).

* `dgErrVar g` / `dgErrIs g err`: the package variable `g` holds a fixed non-nil error / `err` is
  it. `versionFacts` states it of the error variables the manager returns (`errors.go`:
  `ErrInvalidDowngradeTargetVersion`, `ErrDowngradeInProcess`, `ErrNoInflightDowngrade`, each
  `errors.New(...)` at init) and of `etcdserver/errors`' `ErrClusterVersionUnavailable`, which the
  PR makes `DowngradeValidate` return. An assumption about package initialization, not proved from
  `initialize'` (as the other packages' facts), taken as a premise of the specs rather than put in
  the package's `isPkgInit` (stated `True` in `apply/Base.lean`, which the apply chain relies on).
* `version.isServer vs RE CVR EP CP`: the contract of the manager's `Server` interface value `vs`
  (`monitor.go`), the methods the downgrade API calls:
  - `LinearizableReadNotify(ctx)` returns an error satisfying `RE`;
  - `GetClusterVersion()` returns a `*semver.Version` satisfying `CVR` (`nil` while the cluster
    version is not decided: nothing more is assumed, so every result may be `nil`, independently
    of the earlier ones);
  - `GetDowngradeInfo()` returns a non-nil `*DowngradeInfo` the caller owns (the adapter's
    `RaftCluster.DowngradeInfo()` returns a fresh copy, `&DowngradeInfo{Enabled: false}` when
    there is none);
  - `DowngradeEnable(ctx, tv)` (a non-nil `tv`: the adapter calls `tv.String()`) consumes `EP`,
    `DowngradeCancel(ctx)` consumes `CP`: the right to propose a downgrade enable / cancel. A spec
    whose postcondition gives `EP` (`CP`) back states that the call proposed nothing.
  `RE`, `CVR`, `EP`, `CP` are the caller's: the server's adapter meets the contract with `RE`,
  `CVR` trivial and any `EP`, `CP` (`EtcdServer.Version`'s postulate); a test's mock with others
  (`Proof/.../version/Manager__DowngradeValidate.lean`, the nil-version corollary).
-/
module

public import Code.go_etcd_io.etcd.server.v3.etcdserver.version
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.version
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.version

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.version.Assumptions]

/-- The package variable `g` holds a fixed non-nil error (persistent). -/
def dgErrVar (g : GoString) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, globalAddr g ↦□ GoInterface.ok e)

/-- `err` is the error the package variable `g` holds (persistent). -/
def dgErrIs (g : GoString) (err : GoInterface) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, globalAddr g ↦□ GoInterface.ok e ∗ ⌜err = GoInterface.ok e⌝)

instance version_dgErrVar_persistent (g : GoString) : Persistent (dgErrVar (GF := GF) g) := by
  unfold dgErrVar; infer_instance
instance version_dgErrIs_persistent (g : GoString) (err : GoInterface) :
    Persistent (dgErrIs (GF := GF) g err) := by
  unfold dgErrIs; infer_instance

theorem dgErrIs_ne_nil (g : GoString) (err : GoInterface) :
    dgErrIs (GF := GF) g err ⊢ ⌜err ≠ GoInterface.nil⌝ := by
  unfold dgErrIs
  iintro ⟨%e, -, %h⟩
  ipureintro
  subst h
  intro h; cases h

/-- **The downgrade API's error variables** (persistent; a premise, see the header). -/
def version.versionFacts : IProp GF :=
  iprop(dgErrVar ErrInvalidDowngradeTargetVersion ∗ dgErrVar ErrDowngradeInProcess ∗
    dgErrVar ErrNoInflightDowngrade ∗
    dgErrVar go_etcd_io.etcd.server.v3.etcdserver.errors.ErrClusterVersionUnavailable)

instance version_versionFacts_persistent : Persistent (version.versionFacts (GF := GF)) := by
  unfold version.versionFacts; infer_instance

/-- **The manager's `Server`** (persistent; see the header). -/
def version.isServer (vs : GoInterface) (RE : GoInterface → IProp GF) (CVR : Loc → IProp GF)
    (EP CP : IProp GF) : IProp GF :=
  iprop(∃ si : GoInterfaceOk, ⌜vs = GoInterface.ok si⌝ ∗
    □ (∀ ctx : GoInterface, {{ True }}
        (App (Val #(methods si.ty go!"LinearizableReadNotify" si.v)) (Val #ctx))
      {{ (err : GoInterface), RET #err; RE err }}) ∗
    □ ({{ True }} (App (Val #(methods si.ty go!"GetClusterVersion" si.v)) (Val #()))
      {{ (cv : Loc), RET #cv; CVR cv }}) ∗
    □ ({{ True }} (App (Val #(methods si.ty go!"GetDowngradeInfo" si.v)) (Val #()))
      {{ (di : Loc), RET #di; ⌜di ≠ null⌝ ∗ ∃ d : DowngradeInfo, di ↦ d }}) ∗
    □ (∀ (ctx : GoInterface) (tv : Loc), {{ EP ∗ ⌜tv ≠ null⌝ }}
        (App (App (Val #(methods si.ty go!"DowngradeEnable" si.v)) (Val #ctx)) (Val #tv))
      {{ (err : GoInterface), RET #err; True }}) ∗
    □ (∀ ctx : GoInterface, {{ CP }}
        (App (Val #(methods si.ty go!"DowngradeCancel" si.v)) (Val #ctx))
      {{ (err : GoInterface), RET #err; True }}))

instance version_isServer_persistent (vs : GoInterface) (RE : GoInterface → IProp GF)
    (CVR : Loc → IProp GF) (EP CP : IProp GF) :
    Persistent (version.isServer vs RE CVR EP CP) := by
  unfold version.isServer; infer_instance

/-- **What `DowngradeValidate` returns** (`err`), with the trace of the calls that decide it:
- the linearizable read failed (`RE err`, `err` not nil);
- the read succeeded and the cluster version was `nil`: `ErrClusterVersionUnavailable` (the PR);
- the read succeeded, the cluster version `cv` was not nil, and then: the target is not
  `allowedDowngradeVersion(cv)` (`ErrInvalidDowngradeTargetVersion`), or a downgrade is enabled
  (`ErrDowngradeInProcess`), or `nil`. -/
def version.validateOutcome (RE : GoInterface → IProp GF) (CVR : Loc → IProp GF)
    (err : GoInterface) : IProp GF :=
  iprop((⌜err ≠ GoInterface.nil⌝ ∗ RE err) ∨
    (dgErrIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrClusterVersionUnavailable err ∗
      RE GoInterface.nil ∗ CVR null) ∨
    (∃ cv : Loc, ⌜cv ≠ null⌝ ∗ RE GoInterface.nil ∗ CVR cv ∗
      (dgErrIs ErrInvalidDowngradeTargetVersion err ∨ dgErrIs ErrDowngradeInProcess err ∨
        ⌜err = GoInterface.nil⌝)))

/-- A `nil` result of `DowngradeValidate`: the read succeeded and a non-nil cluster version was
seen. -/
theorem version.validateOutcome_nil (RE : GoInterface → IProp GF) (CVR : Loc → IProp GF) :
    version.validateOutcome RE CVR GoInterface.nil ⊢
      ∃ cv : Loc, ⌜cv ≠ null⌝ ∗ RE GoInterface.nil ∗ CVR cv := by
  unfold version.validateOutcome dgErrIs
  iintro (⟨%h, -⟩ | ⟨⟨%e, -, %h⟩, -, -⟩ | ⟨%cv, %hcv, Hre, Hcv, Hor⟩)
  · exact absurd rfl h
  · cases h
  · iexists cv
    iframe Hre Hcv
    ipureintro; exact hcv

end defs

end EtcdGrove
end Perennial
