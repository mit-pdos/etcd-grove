/-
**A peer's status** (`peer_status.go`; rafthttp stage 4d): the mutex `mu` guards whether the peer
is active and since when; the logger and the two ids are fixed. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Pipe

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- What the peer status's mutex guards. -/
def peerStatusInv (s : Loc) : IProp GF :=
  iprop(∃ (a : Bool) (t : time.Time),
    s.[rafthttp.peerStatus, go!"active"] ↦ a ∗ s.[rafthttp.peerStatus, go!"since"] ↦ t)

/-- **A peer status** (persistent): its logger (not `nil`: `newPeerStatus` makes a no-op one for
`nil`), its local and peer ids, and its mutex. -/
def peerStatusOk (s : Loc) : IProp GF :=
  iprop(∃ (lg : Loc) (lid id : go_etcd_io.etcd.client.pkg.v3.types.ID),
    s.[rafthttp.peerStatus, go!"lg"] ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
    s.[rafthttp.peerStatus, go!"local"] ↦□ lid ∗ s.[rafthttp.peerStatus, go!"id"] ↦□ id ∗
    sync.isMutex (s.[rafthttp.peerStatus, go!"mu"]) (peerStatusInv s))

instance peerStatusOk_persistent (s : Loc) : Persistent (peerStatusOk (GF := GF) s) := by
  unfold peerStatusOk; infer_instance

end defs

end EtcdGrove
end Perennial
