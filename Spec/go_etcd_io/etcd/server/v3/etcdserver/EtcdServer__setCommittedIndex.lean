/-
`(*EtcdServer).setCommittedIndex(v)` (`server.go:1706`): an atomic store.

**Users**: the ready handler's `updateCommittedIndex` (`server.go:802-806`), from the `Ready` loop's
`updateCommittedIndex` (`raft.go:357`). Snippet: none (no client observes it but the request path's
gap check).

**Proof sketch**: the store, with `s.committedIndex`'s invariant (its value a committed index:
`committedLb γ.raft l` with `v ≤ |l|`). **Changes** from `specs-ref`'s spec (the read names'
commit lower bound): over R1's `committedLb`. **Margin**: none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply

set_option autoImplicit false
set_option linter.iris.dupNamespace false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

def EtcdServer.setCommittedIndex.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat) (c v : w64) (l : List Raft.LogEntry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ committedW s c ∗ Raft.committedLb γ.raft l ∗ ⌜uint.nat v ≤ l.length⌝ }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"setCommittedIndex")) (Val #v))
  {{ RET #(); committedW s v }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
