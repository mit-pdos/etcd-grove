/- Lean-first (no Rocq counterpart).

`resOf(o)` (linkvtxn.go): a new slice, the output's results (`resOfL`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.linkvtxn


section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

/-- See the file header. -/
abbrev resOf.spec : Prop :=
  ∀ (x : Output),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkvtxn }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkvtxn.resOf)) (Val #x))
  {{ (out : GoSlice), RET #out; out ↦* resOfL x ∗ ownSliceCap TRes out (DFrac.own 1) }}

end spec

end linkvtxn
end EtcdGrove
end Perennial
