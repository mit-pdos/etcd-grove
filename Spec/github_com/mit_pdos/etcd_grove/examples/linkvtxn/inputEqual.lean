/- Lean-first (no Rocq counterpart).

`inputEqual(a, b)` (linkvtxn.go): `a = b` (Go's `==` on the struct).
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
abbrev inputEqual.spec : Prop :=
  ∀ (a b : Input),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkvtxn }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkvtxn.inputEqual)) (Val #a)) (Val #b))
  {{ RET #(decide (a = b)); True }}

end spec

end linkvtxn
end EtcdGrove
end Perennial
