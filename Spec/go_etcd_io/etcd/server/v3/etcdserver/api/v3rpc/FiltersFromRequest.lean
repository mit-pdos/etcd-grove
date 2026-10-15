/-
`v3rpc.FiltersFromRequest` (`watch.go`). Lean-first (no Rocq counterpart); the
vocabulary is `v3rpc/InvWatchStream.lean` and `v3rpc/InvWatch.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`FiltersFromRequest(creq)`**: a slice of filter functions, at most one per filter type of
the request, none for a request with no filters. -/
abbrev v3rpc.FiltersFromRequest.spec : Prop :=
  ∀ (cr : Loc) (fs : GoSlice) (filters : List w32) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      structFieldRef etcdserverpb.WatchCreateRequest go!"Filters" cr ↦{dq} fs ∗ fs ↦*□ filters }}
    (App (Val (@! v3rpc.FiltersFromRequest)) (Val #cr))
  {{ (sl : GoSlice), RET #sl;
      structFieldRef etcdserverpb.WatchCreateRequest go!"Filters" cr ↦{dq} fs ∗
      ∃ fl : List GoFunc, sl ↦* fl ∗ ⌜fl.length ≤ filters.length ∧ (filters = [] → fl = [])⌝ }}

end spec

end EtcdGrove
end Perennial
