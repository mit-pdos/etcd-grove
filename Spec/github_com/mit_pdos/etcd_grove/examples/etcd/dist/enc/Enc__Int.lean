/- Lean-first (no Rocq counterpart).

`e.Int(x)` (`examples/etcd/dist/enc`): appends `x` as an `int64`, as `U64` (`encU64`) to the encoder's bytes.
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
abbrev Enc.Int.spec : Prop :=
  ∀ (e : Loc) (bs : List w8) (x : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc ∗ ownEnc e bs }}
    (App (e @!! go.GoType.PointerType Enc.ty @!! go!"Int") (Val #x))
  {{ RET #(); ownEnc e (bs ++ encU64 x) }}

end spec

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc
end Perennial
