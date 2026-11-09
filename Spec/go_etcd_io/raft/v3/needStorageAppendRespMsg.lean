/-
## `needStorageAppendRespMsg(r, rd)` (internal)

`acceptReady`. Mirrors the code: unstable entries (in progress or next, R3), or a snapshot in the
`Ready`. **Changes.** New (no old spec). **Margin.** Only the snapshot's case is stated.
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

/-- (internal) Whether the batch needs a storage-append acknowledgement (always with a snapshot). -/
def needStorageAppendRespMsg.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (ρ : CoreView) (rd : go_etcd_io.raft.v3.Ready)
    (o : Option Snapshot),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftCore r γ id ρ ∗ snapOpt rd.Snapshot' o }}
    (App (App (Val (@! go_etcd_io.raft.v3.needStorageAppendRespMsg)) (Val #r)) (Val #rd))
  {{ (b : Bool), RET #b; raftCore r γ id ρ ∗ ⌜o.isSome → b = true⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
