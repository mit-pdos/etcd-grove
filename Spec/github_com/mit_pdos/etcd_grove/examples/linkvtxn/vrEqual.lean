/- Lean-first (no Rocq counterpart).

`vrEqual(a, b)` (linkvtxn.go): `a = b`.
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
abbrev vrEqual.spec : Prop :=
  ∀ (a b : VR),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkvtxn }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkvtxn.vrEqual)) (Val #a)) (Val #b))
  {{ RET #(decide (a = b)); True }}

end spec

end linkvtxn
end EtcdGrove
end Perennial
