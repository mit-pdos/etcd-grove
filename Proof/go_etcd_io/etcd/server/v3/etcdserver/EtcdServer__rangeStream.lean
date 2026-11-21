/-
The trust boundary: `(*EtcdServer).rangeStream` (names only; auth-mediation M3, option (B), the user's
choice 2026-11-21): the pages of a streamed range, sent on the stream it is given, each chunk of the
range under the caller's check. Reviewed independently: `notes/axiom-review/rangestream.md`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__rangeStream

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

axiom EtcdServer.rangeStream.wp_proof : EtcdServer.rangeStream.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
