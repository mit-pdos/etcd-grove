/-
`f.Truncate(sz)` growing an open `*os.File` (this repository's `os`, project `bboltfs`), as
minibolt's `grow` does, through a non-negative fd (`OpenFile` gives one; the model panics on a
closed file's -1): with the whole of the file's `OsMeta` (no change in flight on it), the
new size at least the size, and the client's halves of the cells of every mapping over `[size,
sz)` (holes, which the new bytes fill). The model (`TrustedCode/os.lean`) is the extension's two
steps (`wp_FtruncateStart`, `wp_FtruncateFinish`), retried on `EINTR`. On success the file is
grown (`osGrown`: size `sz`, the new bytes zeros, dirty, and the cells show them); on failure it
is grown or unchanged. Proved in `Proof/os/File__Truncate.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.os.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- See the file header. -/
abbrev os.File.Truncate.spec : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sz : w64) (dq : DFrac) (d : OsFd)
    (m : OsMeta),
  0 ≤ fd.toInt → d.writable = true → 0 ≤ sz.toInt → m.size ≤ sz.toNat →
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ osFd (GF := GF) fd dq d ∗
      osMeta (GF := GF) d.path (DFrac.own 1) (some m) ∗
      mcellsAny (GF := GF) m.maps m.size sz.toNat }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Truncate")) (Val #sz))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d ∗
      ((⌜err = interface.nil⌝ ∗ osGrown d.path m sz.toNat) ∨
       (⌜err ≠ interface.nil⌝ ∗
         (osGrown d.path m sz.toNat ∨
          (osMeta d.path (DFrac.own 1) (some m) ∗ mcellsAny m.maps m.size sz.toNat)))) }}

end spec

end EtcdGrove
end Perennial
