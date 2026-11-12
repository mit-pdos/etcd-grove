/-
The trust boundary: `context.WithTimeout(context.Background(), d)`'s outgoing metadata
(`Spec/context/WithTimeoutBackgroundMd.lean`; the auth-mode merge's 5b, 2026-10-29). Perennial's
context model does not describe values at other packages' keys (`ContextDesc.Values` holds the
`context` package's own), and `metadata.outgoingOf` is opaque, so the fact is assumed.
-/
module

public import Spec.context.WithTimeoutBackgroundMd

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
variable [package_sem : context.Assumptions]

axiom context.WithTimeoutBackgroundMd.wp_proof :
  context.WithTimeoutBackgroundMd.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
