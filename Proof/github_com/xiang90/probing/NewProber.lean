/-
The trust boundary: `probing.NewProber` (`github.com/xiang90/probing` is names-only).
-/
module

public import Spec.github_com.xiang90.probing.NewProber

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

/-- **Trust boundary** (rafthttp stage 6c, D39, the user's choice: the prober an axiom):
`probing.NewProber(tr)` (`prober.go`) allocates a `*prober` (an empty map of targets, its mutex,
the round tripper kept for the probes) and returns it as a `Prober`, without a goroutine. Its
`RemoveAll()` takes the mutex, stops every target's ticker goroutine (closing its stop channel)
and empties the map: it returns, touching nothing the proofs track. -/
axiom probing.NewProber.wp_proof : probing.NewProber.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
