/- Lean-first (no Rocq counterpart).

`d.Done()` (`examples/etcd/dist/enc`): true only if every read succeeded and no byte is left.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Assumptions]

/-- See the file header. -/
abbrev Dec.Done.spec : Prop :=
  ∀ (d : Loc) (bs : List w8) (ok : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc ∗ ownDec d bs ok }}
    (App (d @!! go.GoType.PointerType Dec.ty @!! go!"Done") (Val #()))
  {{ (r : Bool), RET #r; ⌜r = true → ok = true ∧ bs = []⌝ }}

end spec

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc
end Perennial
