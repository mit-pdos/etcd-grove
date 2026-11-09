/-
## `needStorageAppendMsg(r, rd)` (internal)

`readyWithoutAccept`'s asynchronous branch (`rawnode.go:200`), unreachable under `ConfigOk`.
Mirrors the code. **Changes.** New (round 1, R1's request). **Margin.** One direction only.
-/
module

public import Spec.go_etcd_io.raft.v3.ApiCore

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

/-- (internal) Whether a batch needs a storage-append message (with entries or a snapshot, yes). -/
def needStorageAppendMsg.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen) (rd : go_etcd_io.raft.v3.Ready) (oh : Option HardState) (os : Option Snapshot),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftOpen r γ id o ∗ hsOpt rd.HardState' oh ∗ snapOpt rd.Snapshot' os }}
    (App (App (Val (@! go_etcd_io.raft.v3.needStorageAppendMsg)) (Val #r)) (Val #rd))
  {{ (b : Bool), RET #b; raftOpen r γ id o ∗
      ⌜(rd.Entries'.len ≠ W64 0 ∨ ∃ s, os = some s ∧ s.index ≠ W64 0) → b = true⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
