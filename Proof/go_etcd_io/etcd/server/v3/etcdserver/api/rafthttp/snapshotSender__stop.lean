/-
The trust boundary: `snapshotSender.stop` (untranslated; D34).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.snapshotSender__stop

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (rafthttp stage 6b, D34): `stop` (`snapshot_sender.go`) closes `stopc`, once
(the right). -/
axiom rafthttp.snapshotSender.stop.wp_proof :
  rafthttp.snapshotSender.stop.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
