/- Lean-first (no Rocq counterpart).

`d.Bool()` (`examples/etcd/dist/enc`): reads a bool (one byte, 0 or 1): the decoder's bytes were its encoding (`encBool`) followed by
the rest, which it keeps, every read so far having succeeded; or its flag is false (`decPost`).
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
abbrev Dec.Bool.spec : Prop :=
  ∀ (d : Loc) (bs : List w8) (ok : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc ∗ ownDec d bs ok }}
    (App (d @!! go.GoType.PointerType Dec.ty @!! go!"Bool") (Val #()))
  {{ (x : Bool), RET #x; decPost d bs ok encBool x }}

end spec

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc
end Perennial
