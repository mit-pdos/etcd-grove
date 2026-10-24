/-
The trust boundary: `probing.NewHandler` (`github.com/xiang90/probing` is names-only).
-/
module

public import Spec.github_com.xiang90.probing.NewHandler

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

/-- **Trust boundary** (rafthttp stage 6c, D34, the user's choice: the prober an axiom):
`probing.NewHandler()` (`server.go`) returns an `*httpHealth` as an `http.Handler`. Its
`ServeHTTP(w, r)` reads nothing of the request, sets no header and JSON-encodes
`Health{OK: true, Now: time.Now()}` to `w` (`json.NewEncoder(w).Encode`): the first write commits
the response with status `200` and the handler's (empty) header map, and a failed write only ends
the encoding. It does not panic, keeps no resource and returns the writer committed. -/
axiom probing.NewHandler.wp_proof : probing.NewHandler.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
