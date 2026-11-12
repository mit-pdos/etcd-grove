/-
The trust boundary: `types.NewURLs` (`go.etcd.io/etcd/client/pkg/v3/types` is names-only).
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.types.NewURLs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (rafthttp stage 6a): etcd's `NewURLs` (`client/pkg/types/urls.go`) makes a
slice of `len(strs)` URLs; for each string, `strings.TrimSpace` (none here: no space), `url.Parse`
(of `http://host:port`, host bytes letters, digits, `.`, `-`: no error, a URL with scheme `http`
and that host, its other fields empty, no user, `ForceQuery` and `OmitHost` false), the
`host:port` check (`net.SplitHostPort`: one `:`) and the no-path check pass; then it sorts the
slice in place and returns it with no error. -/
axiom types.NewURLs.wp_proof : types.NewURLs.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
