/-
The trust boundary: `(*membershipBackend).MustSaveMemberToBackend` (names-only; D43 M5b′, 2026-10-26, the user's
decision: the member backend's writers and read are contract axioms over the tracked buckets).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.membershipBackend__MustSaveMemberToBackend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

axiom schema.membershipBackend.MustSaveMemberToBackend.wp_proof :
  schema.membershipBackend.MustSaveMemberToBackend.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
