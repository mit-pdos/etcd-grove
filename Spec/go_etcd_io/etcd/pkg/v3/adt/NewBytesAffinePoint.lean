/-
`NewBytesAffinePoint(b)`: the point interval `[b, b + "\x00")`, its end a fresh slice.

**Users.** `getMergedPerms`, `checkKeyPoint` (3d). **Proof sketch.** `make([]byte, len(b)+1)` (the
premise: `len(b) + 1` does not wrap, else `make` panics), `copy`, a store. **Changes.** Unchanged.
**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Adt

open Iris Iris.BI go_etcd_io.etcd.pkg.v3.adt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

def NewBytesAffinePoint.spec : Prop :=
  ∀ (b : GoSlice) (bs : GoString) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ b ↦*{dq} bs ∗ ⌜sint.Z b.len < 2 ^ 63 - 1⌝ }}
    (App (Val (@! go_etcd_io.etcd.pkg.v3.adt.NewBytesAffinePoint)) (Val #b))
  {{ (e : GoSlice), RET #(Cmp.bytes.ivl #b #e); b ↦*{dq} bs ∗ e ↦* (bs ++ [W8 0]) }}

end spec

end Adt
end EtcdGrove
end Perennial
