/-
## `newStorageApplyRespMsg(r, ents)` (internal)

`acceptReady` (and the asynchronous `newStorageApplyMsg`, unreachable: `ConfigOk`). Mirrors the code:
a fresh `MsgStorageApplyResp` to the node from the local apply thread, of term 0, carrying the
entries (shared, read-only). **Changes.** New (no old spec).
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

/-- (internal) The apply acknowledgement of committed entries `es`. -/
def newStorageApplyRespMsg.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (ρ : CoreView) (sl : GoSlice) (j : Nat) (es : List LogEntry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftCore r γ id ρ ∗ entriesRO sl j es }}
    (App (App (Val (@! go_etcd_io.raft.v3.newStorageApplyRespMsg)) (Val #r)) (Val #sl))
  {{ (p : Loc), RET #p; ∃ mm, raftCore r γ id ρ ∗ msgPts p (DFrac.own 1) mm ∗
      ⌜mm.type = MsgStorageApplyResp ∧ mm.to = id ∧ mm.src = localApplyThread ∧
        mm.term = W64 0 ∧ mm.entries = es⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
