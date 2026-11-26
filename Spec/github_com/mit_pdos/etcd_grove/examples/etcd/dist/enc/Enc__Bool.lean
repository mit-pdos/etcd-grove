/- Lean-first (no Rocq counterpart).

`e.Bool(x)` (`examples/etcd/dist/enc`): appends one byte, 0 or 1 (`encBool`) to the encoder's bytes.
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
abbrev Enc.Bool.spec : Prop :=
  ∀ (e : Loc) (bs : List w8) (x : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc ∗ ownEnc e bs }}
    (App (e @!! go.GoType.PointerType Enc.ty @!! go!"Bool") (Val #x))
  {{ RET #(); ownEnc e (bs ++ encBool x) }}

end spec

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc
end Perennial
