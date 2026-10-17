/-
`membership.RaftCluster.Member(id)` (`cluster.go`: under `c`'s mutex, a clone of `c.members[id]`,
`nil` if there is none). Names-only: the trust boundary (etcd-io/etcd#22525, the snapshot check
`hasPublishedAttributes` of `publishV3`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `c.Member(id)` (`c` a cluster, `isRaftCluster`) returns `nil` (no member `id`) or a fresh
clone of the member, owned: its name `nm` and client URLs `cus` (a fresh slice, `Clone` copies
it), which the cluster held for `id` (`attrsHeld`: read under `c`'s mutex). -/
abbrev membership.RaftCluster.Member.spec : Prop :=
  ∀ (c : Loc) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      membership.isRaftCluster c }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"Member")) (Val #id))
  {{ (m : Loc), RET #m; ⌜m = null⌝ ∨
      ∃ (nm : GoString) (cu : GoSlice) (cus : List GoString),
        ⌜m ≠ null⌝ ∗ membership.mNameAddr m ↦ nm ∗ membership.mClientURLsAddr m ↦ cu ∗
        cu ↦* cus ∗ ⌜membership.attrsHeld c id nm cus⌝ }}

end spec

end EtcdGrove
end Perennial
