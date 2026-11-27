/-
`binary.BigEndian.AppendUint32(b, v)`, of Go's `encoding/binary` (Perennial translates `bigEndian`
with its bodies, and has no spec of this method): `b` with `v`'s four bytes, big-endian, after it (a
slice with its capacity, owned whole). Proved in `Proof/encoding/binary/bigEndian__AppendUint32.lean`
from the translated body (a candidate for Perennial: `notes/perennial-changes.md`).
-/
module

public import Perennial.Proof.encoding.binary.PtrMethods

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.binary.Assumptions]

/-- See the file header. -/
abbrev binary.bigEndian.AppendUint32.spec : Prop :=
  ∀ (b : GoSlice) (vs : List w8) (v : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗ b ↦* vs ∗
      ownSliceCap w8 b (DFrac.own 1) }}
    (App (App (Val (globalAddr encoding.binary.BigEndian @!!
      go.GoType.PointerType encoding.binary.bigEndian.ty @!! go!"AppendUint32")) (Val #b)) (Val #v))
  {{ (r : GoSlice), RET #r; r ↦* (vs ++ (u32Le v).reverse) ∗ ownSliceCap w8 r (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
