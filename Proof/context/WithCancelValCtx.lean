/-
The trust boundary: `context.WithCancel(&valCtx{inctx})` (etcd's never-done parent of the watch
client's stream context) returns a cancellable context and its `cancel` (Perennial proves
`WithCancel` for a `*cancelCtx`-chain parent only; see the spec's file).
-/
module

public import Spec.context.WithCancelValCtx

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

axiom context.WithCancelValCtx.wp_proof :
  context.WithCancelValCtx.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
