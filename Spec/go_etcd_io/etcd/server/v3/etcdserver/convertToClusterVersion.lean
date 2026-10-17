/-
`convertToClusterVersion(v)` (`cluster_util.go`). Lean-first (the downgrade API, etcd-io/etcd#22575, 2026-10-16).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvDowngrade

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `convertToClusterVersion(v)` returns a version, not nil, with a nil error, or no version
with `ErrWrongDowngradeVersionFormat` (when neither `v` nor `v + ".0"` parses). -/
abbrev convertToClusterVersion.spec : Prop :=
  ∀ (v : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvDgErrVars }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.convertToClusterVersion)) (Val #v))
  {{ (ver : Loc) (err : GoInterface), RET (PairV #ver #err);
      ⌜err = GoInterface.nil ∧ ver ≠ null⌝ ∨
      ⌜ver = null⌝ ∗ dgErrIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrWrongDowngradeVersionFormat err }}

end spec

end EtcdGrove
end Perennial
