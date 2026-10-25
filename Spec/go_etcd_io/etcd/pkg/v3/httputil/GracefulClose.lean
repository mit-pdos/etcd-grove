/-
`httputil.GracefulClose`: the trust boundary (`go.etcd.io/etcd/pkg/v3/httputil` is names-only;
rafthttp stage 5e-3, `streamReader.dial`). Lean-first.
-/
module

public import Proof.net.http.Boundary
public import Code.go_etcd_io.etcd.pkg.v3.httputil

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `httputil.GracefulClose(resp)` of a received response, its body read without a guarantee
(`respReadAny`; 2026-10-24, rafthttp stage 7d, was its exclusive reader: the snapshot sender's
timer drains the body while the sender reads it): drains the body (`io.Copy(io.Discard,
resp.Body)`) and closes it, then returns. -/
abbrev httputil.GracefulClose.spec : Prop :=
  ∀ (resp : Loc) (st : w64) (rd : GoInterface) (Hd : List (GoString × GoString) → Prop),
  {{ http.respAt (GF := GF) resp st rd Hd ∗ http.respReadAny rd }}
    (App (Val (@! go_etcd_io.etcd.pkg.v3.httputil.GracefulClose)) (Val #resp))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
