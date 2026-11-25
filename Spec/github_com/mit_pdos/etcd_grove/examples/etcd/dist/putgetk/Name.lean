/-
`Name(i)` (`examples/etcd/dist/putgetk/putgetk.go`): member `i`'s name, `"putgetk-"` and `i` in decimal
(`strconv.FormatUint(i, 10)`). Lean-first (no Rocq counterpart).

**The triple:** it returns `nameOf i` (`Proof/.../dist/putgetk/Defs.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_putgetk_dist

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev Name.spec : Prop :=
  ∀ (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Name)) (Val #i))
  {{ RET #(nameOf (uint.nat i)); True }}

end spec

end etcd_putgetk_dist
end EtcdGrove
end Perennial

end
