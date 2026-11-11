/-
`f.Truncate(sz)` on an open `*os.File` (this repository's `os`, project `bboltfs`), growing or
shrinking it, through a non-negative fd (`OpenFile` gives one; the model panics on a closed file's
-1): with the whole of the file's `OsMeta` (no change in flight on it), the bytes it cuts off
(`[sz, size)`, whole; none if it grows the file) and the client's halves of the cells of every
mapping over the range where the sizes part. The model (`TrustedCode/os.lean`) is the extension's
two steps (`wp_osFtruncateStart`, `wp_osFtruncateFinish`, a resize to `sz`), retried on `EINTR`.
On success the resize landed (`os.ftDone`: the `OsMeta` it leaves, the bytes it grew the file
over, zeros, and the cells showing the new contents); on failure it landed or did not
(`os.ftUndone`: the `OsMeta` as its first step left it, the bytes it would have cut off). Proved
in `Proof/os/File__Truncate.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.os.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- See the file header. -/
abbrev os.File.Truncate.spec : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sz : w64) (dq : DFrac) (d : OsFd)
    (m : OsMeta) (xs : List ByteG),
  0 ≤ fd.toInt → d.writable = true → 0 ≤ sz.toInt → xs.length = m.size - sz.toNat →
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ osFd (GF := GF) fd dq d ∗
      osMeta (GF := GF) d.ino (DFrac.own 1) m ∗
      osBytes (GF := GF) d.ino (min m.size sz.toNat) (DFrac.own 1) xs ∗
      mcellsAny (GF := GF) m.maps (min m.size sz.toNat) (max m.size sz.toNat) }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Truncate")) (Val #sz))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d ∗
      ((⌜err = interface.nil⌝ ∗ os.ftDone d.ino m sz.toNat) ∨
       (⌜err ≠ interface.nil⌝ ∗
         (os.ftDone d.ino m sz.toNat ∨ os.ftUndone d.ino m sz.toNat xs))) }}

end spec

end EtcdGrove
end Perennial
