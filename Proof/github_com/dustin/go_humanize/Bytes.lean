/-
The trust boundary: `go_humanize.Bytes` (`github.com/dustin/go-humanize` is names-only).
-/
module

public import Spec.github_com.dustin.go_humanize.Bytes

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
variable [package_sem : github_com.dustin.go_humanize.Assumptions]

axiom go_humanize.Bytes.wp_proof : go_humanize.Bytes.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
