/- Lean-first (no Rocq counterpart).

`d.Str()` (`examples/etcd/dist/enc`): reads a string (its length, then its bytes): the decoder's bytes were its encoding (`encStr`) followed by
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
abbrev Dec.Str.spec : Prop :=
  ∀ (d : Loc) (bs : List w8) (ok : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc ∗ ownDec d bs ok }}
    (App (d @!! go.GoType.PointerType Dec.ty @!! go!"Str") (Val #()))
  {{ (x : GoString), RET #x; decPost d bs ok encStr x }}

end spec

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc
end Perennial
