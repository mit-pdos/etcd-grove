/-
The trust boundary: `httputil.GracefulClose` (`go.etcd.io/etcd/pkg/v3/httputil` is names-only).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.httputil.GracefulClose

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

/-- **Trust boundary** (rafthttp stage 5e-3): etcd's `GracefulClose` (`pkg/httputil/httputil.go`)
is `io.Copy(io.Discard, resp.Body)` (reads to the end, any error ignored) then `resp.Body.Close()`
(an error ignored): a response body's reads and close, which the HTTP boundary allows of its
reader (`respRead_spec`, `RespClose_spec`); (2026-10-24, stage 7d) of a body read without a
guarantee (`respReadAny`), whose reads return any bytes. -/
axiom httputil.GracefulClose.wp_proof : httputil.GracefulClose.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
