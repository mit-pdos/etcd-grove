/-
The downgrade RPC's handlers (`v3_server.go`: `downgradeValidate`, `downgradeEnable`,
`downgradeCancel`; pr-verify etcd#22589): the vocabulary of their specs. Lean-first (no Rocq
counterpart).

* `convertibleVersion v`: `convertToClusterVersion(v)` succeeds (semver's `NewVersion` parses `v`
  or `v + ".0"`). Opaque: semver is names-only, so the specs only distinguish the two cases.
* `srvVersionOk s γcv EP CP`: the contract of `s.Version()` (`server.go`:
  `serverversion.NewManager(s.Logger(), NewServerVersionAdapter(s))`; names-only): a new manager
  whose `Server` is the server's adapter, meeting `version.isServer` with no promise on the
  linearizable read's error, its cluster-version reads `srvCVR γcv` (`nil`, or non-nil with
  `clusterVersionOk`'s witness that the version stays known: both read `s.cluster.Version()`), and
  the proposal rights `EP`, `CP` fixed by the premise (sound for any: the adapter's
  `DowngradeEnable` and `DowngradeCancel` need neither). A premise of the handlers' specs
  (`srvDowngradeOk`), as `clusterVersionOk` (`InvStart.lean`) is of `start`'s: a property of a
  server built by `NewServer` (the adapter's methods read its cluster, its read loop and its raft
  node), which no verified caller discharges yet. Until review (2026-10-16) the rights were
  quantified inside the contract (`∀ EP CP`), which let a handler's proof pick its own and made
  "nothing proposed" vacuous at the handler level.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.version.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvStart

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

/-- `convertToClusterVersion(v)` succeeds (see the header). -/
opaque convertibleVersion : GoString → Prop

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **What the adapter's `GetClusterVersion()` returns** (`s.cluster.Version()`, the read
`s.ClusterVersion()` makes): `nil`, or a non-nil version with the witness that the cluster version
is known from now on (`monoNatLbOwn γcv 1`, `clusterVersionOk`'s). -/
def srvCVR (γcv : GName) (cv : Loc) : IProp GF :=
  iprop(⌜cv = null⌝ ∨ (⌜cv ≠ null⌝ ∗ monoNatLbOwn γcv 1))

/-- **`s.ClusterVersion()`'s contract at `γcv`** (persistent): `clusterVersionOk`'s, with its ghost
name exposed so that the adapter's reads share it. -/
def srvClusterVersionAt (s : Loc) (γcv : GName) : IProp GF :=
  iprop(□ (∀ known : Bool,
    {{ if known then monoNatLbOwn γcv 1 else True }}
      (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"ClusterVersion")) (Val #()))
    {{ (v : Loc), RET #v; ⌜v = null ∧ known = false⌝ ∨ ⌜v ≠ null⌝ ∗ monoNatLbOwn γcv 1 }}))

instance srvClusterVersionAt_persistent (s : Loc) (γcv : GName) :
    Persistent (srvClusterVersionAt (GF := GF) s γcv) := by
  unfold srvClusterVersionAt; infer_instance

theorem srvClusterVersionAt_ok (s : Loc) (γcv : GName) :
    srvClusterVersionAt (GF := GF) s γcv ⊢ clusterVersionOk s := by
  unfold srvClusterVersionAt clusterVersionOk
  iintro #H
  iexists γcv
  iexact H

/-- **`s.Version()`'s contract** (persistent; see the header), for the proposal rights `EP`, `CP`
fixed by the premise (`srvDowngradeOk`): a handler can propose an enable only by spending `EP`,
a cancel only by spending `CP`, so a postcondition that gives one back states that nothing was
proposed. The adapter's cluster-version reads are `srvCVR γcv`. -/
def srvVersionOk (s : Loc) (γcv : GName) (EP CP : IProp GF) : IProp GF :=
  iprop(□ ({{ srvLgReader s }}
      (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Version")) (Val #()))
    {{ (m : Loc), RET #m; srvLgReader s ∗
        ∃ vs : GoInterface,
          structFieldRef go_etcd_io.etcd.server.v3.etcdserver.version.Manager go!"s" m ↦□ vs ∗
          version.isServer vs (fun _ => iprop(True)) (srvCVR γcv) EP CP }}))

instance srvVersionOk_persistent (s : Loc) (γcv : GName) (EP CP : IProp GF) :
    Persistent (srvVersionOk (GF := GF) s γcv EP CP) := by
  unfold srvVersionOk; infer_instance

/-- **The handlers' server premise** (persistent), at the proposal rights `EP`, `CP`: the logger
(`s.lg`, set at construction, not nil: `downgradeCancel` reads the field without `s.lgMu`, as
`Logger()` does under it), the cluster version's contract (`clusterVersionOk`, at a ghost name
`γcv` the manager's adapter shares), the manager's (`srvVersionOk`), and the error variables
(`version.versionFacts`: `ErrClusterVersionUnavailable` among them). -/
def srvDowngradeOk (s l : Loc) (EP CP : IProp GF) : IProp GF :=
  iprop(∃ γcv : GName, srvLgAddr s ↦□ l ∗ ⌜l ≠ null⌝ ∗ srvClusterVersionAt s γcv ∗
    srvVersionOk s γcv EP CP ∗ version.versionFacts)

instance srvDowngradeOk_persistent (s l : Loc) (EP CP : IProp GF) :
    Persistent (srvDowngradeOk (GF := GF) s l EP CP) := by
  unfold srvDowngradeOk; infer_instance

/-- **What `downgradeValidate(ctx, v)` returns** (`resp`, `err`): a target that does not convert
gives `ErrWrongDowngradeVersionFormat` first; a `nil` cluster version `ErrClusterVersionUnavailable`;
the manager's other errors are returned; else a response and `nil`. -/
def dgValidatePost (v : GoString) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜¬ convertibleVersion v ∧ resp = null⌝ ∗
      dgErrIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrWrongDowngradeVersionFormat err) ∨
    (⌜convertibleVersion v ∧ resp = null⌝ ∗ dgErrIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrClusterVersionUnavailable err) ∨
    ⌜convertibleVersion v ∧ resp = null ∧ err ≠ GoInterface.nil⌝ ∨
    (⌜convertibleVersion v ∧ resp ≠ null ∧ err = GoInterface.nil⌝ ∗
      ∃ r : go_etcd_io.etcd.api.v3.etcdserverpb.DowngradeResponse, resp ↦ r))

/-- **What `downgradeEnable(ctx, r)` returns**, with the proposal right `EP` given back when nothing
was proposed: a target that does not convert, `ErrWrongDowngradeVersionFormat` (before anything
else); the manager's validation failed, its error; the enable was proposed and failed, its error;
else a response and `nil`. -/
def dgEnablePost (ver : GoString) (EP : IProp GF) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜¬ convertibleVersion ver ∧ resp = null⌝ ∗
      dgErrIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrWrongDowngradeVersionFormat err ∗ EP) ∨
    (⌜convertibleVersion ver ∧ resp = null ∧ err ≠ GoInterface.nil⌝ ∗ EP) ∨
    ⌜convertibleVersion ver ∧ resp = null ∧ err ≠ GoInterface.nil⌝ ∨
    (⌜convertibleVersion ver ∧ resp ≠ null ∧ err = GoInterface.nil⌝ ∗
      ∃ v : go_etcd_io.etcd.api.v3.etcdserverpb.DowngradeResponse, resp ↦ v))

/-- **What `downgradeCancel(ctx)` returns**, with the proposal right `CP` given back when nothing
was proposed: a `nil` cluster version, `ErrClusterVersionUnavailable`; otherwise a response and
`nil`, whatever the cancel returned. -/
def dgCancelPost (CP : IProp GF) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜resp = null⌝ ∗ dgErrIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrClusterVersionUnavailable err ∗ CP) ∨
    (⌜resp ≠ null ∧ err = GoInterface.nil⌝ ∗ ∃ v : go_etcd_io.etcd.api.v3.etcdserverpb.DowngradeResponse, resp ↦ v))

end defs

end EtcdGrove
end Perennial
