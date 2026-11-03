/- Lean-first (no Rocq counterpart).

`newclientOperation(op, numClients, id)` (dag.go, PR #46): the operation, with its id, no
`firstUnk` and not visited.
-/
module

public import PorcupineDag.Proof.github_com.anishathalye.porcupine.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- See the file header. -/
abbrev newclientOperation.spec : Prop :=
  ∀ (op : Operation) (nc id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine }}
    (App (App (App (Val (@! github_com.anishathalye.porcupine.newclientOperation)) (Val #op))
      (Val #nc)) (Val #id))
  {{ RET #(clientOperation.mk op id id slice.nil false); True }}

end spec

end porcupine
end EtcdGrove
end Perennial
