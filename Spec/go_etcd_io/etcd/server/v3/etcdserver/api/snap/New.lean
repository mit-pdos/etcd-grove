/-
`snap.New(lg, dir)` (`server/etcdserver/api/snap/snapshotter.go`), as etcd PR #22046 changes it
(it now also makes the empty `pendingDBs` map). Lean-first (no Rocq counterpart); branch
`pr-verify/etcd-22046` only. See `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/snap/Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `snap.New(lg, dir)`: a snapshotter of `dir`, with no pending marks (the abstract state `∅`,
returned to the caller). -/
abbrev snap.New.spec : Prop :=
  ∀ (lg : Loc) (dir : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.snap.New)) (Val #lg)) (Val #dir))
  {{ (s : Loc), RET #s; ∃ γ : GName, isSnapshotter s γ dir ∗ snapPending γ ∅ }}

end spec

end EtcdGrove
end Perennial
