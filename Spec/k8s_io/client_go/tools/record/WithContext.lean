/-
`record.WithContext(ctx)` (`tools/record`, names only): a broadcaster option (a function value
`NewBroadcaster` applies). The trust boundary; Lean-first, track C of the DaemonSet run.
-/
module

public import Proof.k8s_io.kubernetes.Base
public import GeneratedProof.k8s_io.client_go.tools.record

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]


/-- `record.WithContext(ctx)`: some option. -/
abbrev record.WithContext.spec : Prop :=
  ∀ (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.record }}
    (App (Val (@! k8s_io.client_go.tools.record.WithContext)) (Val #ctx))
  {{ (o : GoFunc), RET #o; True }}

end spec

end EtcdGrove
end Perennial
