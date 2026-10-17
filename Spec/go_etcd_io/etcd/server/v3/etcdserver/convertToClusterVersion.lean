/-
`convertToClusterVersion(v)` (`cluster_util.go`, names-only; pr-verify etcd#22589): the trust boundary. Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/BaseDowngrade.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseDowngrade

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`convertToClusterVersion(v)`**: semver's `NewVersion` of `v`, or of `v + ".0"`, cut to its
major and minor (`semver.New(major, minor, 0, "", "")`, not nil); if neither parses, `nil` and
`ErrWrongDowngradeVersionFormat` (`convertibleVersion` is which case it is). -/
abbrev convertToClusterVersion.spec : Prop :=
  ∀ (v : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.convertToClusterVersion)) (Val #v))
  {{ (tv : Loc) (err : GoInterface), RET (PairV #tv #err);
      ⌜convertibleVersion v ∧ tv ≠ null ∧ err = GoInterface.nil⌝ ∨
      (⌜¬ convertibleVersion v ∧ tv = null⌝ ∗ dgErrIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrWrongDowngradeVersionFormat err) }}

end spec

end EtcdGrove
end Perennial
