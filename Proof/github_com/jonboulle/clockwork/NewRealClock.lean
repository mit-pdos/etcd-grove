/-
The trust boundary: `clockwork.NewRealClock` (`github.com/jonboulle/clockwork` is names-only).
-/
module

public import Spec.github_com.jonboulle.clockwork.NewRealClock

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

axiom clockwork.NewRealClock.wp_proof : clockwork.NewRealClock.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
