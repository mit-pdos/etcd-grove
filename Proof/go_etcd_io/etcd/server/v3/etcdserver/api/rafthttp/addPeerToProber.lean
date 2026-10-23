/-
The trust boundary: `addPeerToProber` (untranslated; D34).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.addPeerToProber

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

/-- **Trust boundary** (rafthttp stage 6c, D34, the user's choice): `addPeerToProber`
(`probing_status.go`) builds the probe URLs (`us[i] + ProbingPrefix`, reading `us`), adds them to the
prober `p` (`github.com/xiang90/probing`, untranslated: its goroutine `GET`s them on the transport's
round tripper and records round trips), and, if the prober has the peer, starts
`monitorProbingStatus`, a goroutine that logs and observes `rttSec`: neither touches anything the
proofs track (no call into `Raft`, no message), and neither panics. -/
axiom rafthttp.addPeerToProber.wp_proof :
  rafthttp.addPeerToProber.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
