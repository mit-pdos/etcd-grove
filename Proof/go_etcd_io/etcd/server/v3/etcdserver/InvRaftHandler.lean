/-
**Serving a member's raft handler** (D21 stage M5, 2026-10-19; the user's (A), `notes/decisions.md`,
"D21 M5"). Lean-first (no Rocq counterpart). The terms of two trust-boundary axioms,
`EtcdServer.RaftHandler` and `net/http.Serve`, which state D21b's deployment fact where the program
serves the handler: every peer URL of member `id` (`γn.dir id`) is served by the raft handler of
the transport holding `id`'s slot, so `rafthttp.Transport.Start`'s promise (`Process` only with
messages sent to its member, nothing on `ErrorC`) holds of the program.

* `srvNetMember γn s id` (persistent): the server `s` is member `id` of the network `γn`:
  what its inbound path reads (`srvProcOk`, its member id among it) and its raft wrapper's
  transport `t`, started in `γn` (`transportStarted`) -- `NewServer` started it with `id`'s slot
  (`NewServer.spec`'s `netSlot γn id`) -- with no remote (`transportRemotes t []`: a new cluster's
  bootstrap has none, `bootOk`'s `Hrms0`; what `CutPeer`/`MendPeer` need, the partition plan's S2,
  2026-10-20). `NewServer` gives it.
* `raftHandlerOf γn id h` (persistent, opaque): `h` is an `http.Handler` of the transport holding
  `id`'s slot in `γn` (`rafthttp.Transport.Handler()`: a mux of the transport's pipeline, stream
  and snapshot handlers, which hand what they receive to that transport's `Raft`). Only
  `EtcdServer.RaftHandler`'s axiom gives it.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvNet

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The server `s` is member `id` of the network `γn`** (persistent; see the file header). -/
def srvNetMember (γn : NetNames GF) (s : Loc) (id : w64) : IProp GF :=
  iprop(srvProcOk γn s id ∗ ∃ t : Loc, rnTransportAddr (srvRAddr s) ↦□ transportIface t ∗
    transportStarted γn t ∗ transportRemotes t [])

instance srvNetMember_persistent (γn : NetNames GF) (s : Loc) (id : w64) :
    Persistent (srvNetMember (GF := GF) γn s id) := by
  unfold srvNetMember; infer_instance

/-- The opaque core of `raftHandlerOf`. -/
opaque raftHandlerOfCore (γn : NetNames GF) (id : w64) (h : GoInterface) : IProp GF

/-- **`h` is a raft handler of member `id`'s transport in `γn`** (persistent, opaque; see the file
header). -/
def raftHandlerOf (γn : NetNames GF) (id : w64) (h : GoInterface) : IProp GF :=
  iprop(□ raftHandlerOfCore γn id h)

instance raftHandlerOf_persistent (γn : NetNames GF) (id : w64) (h : GoInterface) :
    Persistent (raftHandlerOf (GF := GF) γn id h) := by
  unfold raftHandlerOf; infer_instance

end defs

end EtcdGrove
end Perennial
