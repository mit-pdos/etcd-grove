/-
The trust boundary: `(*membershipBackend).MustDeleteMemberFromBackend` (names-only; D43 M5b′, 2026-10-26, the user's
decision: the member backend's writers and read are contract axioms over the tracked buckets).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.membershipBackend__MustDeleteMemberFromBackend

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
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

axiom schema.membershipBackend.MustDeleteMemberFromBackend.wp_proof :
  schema.membershipBackend.MustDeleteMemberFromBackend.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
