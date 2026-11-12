/-
## `needStorageAppendRespMsg(r, rd)` (internal)

`acceptReady` (`rawnode.go:420`). Mirrors the code: unstable entries (in progress or next, R3's
`hasNextOrInProgressUnstableEnts`), or a non-empty snapshot in the `Ready`. **Changes.** New;
round 1: exact, over the opened struct (`acceptReady` runs with the realization open).
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.ApiCore

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal) Whether the batch needs a storage-append acknowledgement. -/
def needStorageAppendRespMsg.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen) (rd : go_etcd_io.raft.v3.Ready) (os : Option Snapshot),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftOpen r γ id o ∗ snapOpt rd.Snapshot' os }}
    (App (App (Val (@! go_etcd_io.raft.v3.needStorageAppendRespMsg)) (Val #r)) (Val #rd))
  {{ (b : Bool), RET #b; raftOpen r γ id o ∗
      ⌜b = decide (o.log.us.ents ≠ [] ∨ ∃ s, os = some s ∧ s.index ≠ W64 0)⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
