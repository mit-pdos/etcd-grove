/-
`firstCompareKey(c)` (`tracing.go`): the first non-empty key of the comparisons (a trace attribute).
Lean-first (no Rocq counterpart); the request path's unit 3b (2026-10-12).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead

@[expose] public section

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

/-- `firstCompareKey(c)` on the comparisons of a request (`comparesIs`) returns some key. -/
abbrev firstCompareKey.spec : Prop :=
  ∀ (sl : GoSlice) (ps : List Loc) (cs : List CmpModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      sl ↦*□ ps ∗ txn.comparesIs ps cs }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.firstCompareKey)) (Val #sl))
  {{ (k : GoString), RET #k; True }}

end spec

end EtcdGrove
end Perennial
