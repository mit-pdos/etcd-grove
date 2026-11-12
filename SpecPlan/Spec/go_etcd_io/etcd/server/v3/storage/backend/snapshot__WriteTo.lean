/-
## `(*snapshot).WriteTo(w)` (bbolt's `(*Tx).WriteTo`, promoted): trusted (names only)

**Users.** 2d's `newSnapshotReaderCloser` (`snapshot_merge.go:66`, into a pipe), the maintenance
server (`maintenance.go`). Snippet `snapshot.go`.

**Why it is true.** bbolt's `Tx.WriteTo` (4c) writes the read transaction's database file: two meta
pages for this transaction, then the file's data pages read from the file (the read transaction
keeps them from being reused), through `w.Write`; those bytes are some image of `I` of the
transaction's size `n` (`imgBytes I bs`, `bs.length = n`), not the same on every call (A11-completeness
F5: free pages below the high-water mark may be rewritten by a concurrent commit). A write error
stops it, after a prefix of such bytes.

**Changes** (from `specs-ref`'s): over the writer's contract `writeOk` (the caller's record of the
bytes written). verify-round (A11-completeness F5): over the size `n` (`beSnapN`), each call some
bytes of `I` of that length, in place of fixed bytes `bs`. **Margin.** The count on error is not stated.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.backend.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Backend

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **`s.WriteTo(w)`**: some bytes `bs` of the snapshot's image, of its size `n`, written to `w`
(all of them, or a prefix and an error). -/
def snapshot.WriteTo.spec : Prop :=
  ∀ (γ : BeNames) (s : Loc) (I : Image) (n : Nat) (w : GoInterface) (W : List w8 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ beSnapN γ s I n ∗ writeOk w W ∗ W [] }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.snapshot.ty @!! go!"WriteTo")) (Val #w))
  {{ (m : w64) (err : GoInterface), RET (PairV #m #err); beSnapN γ s I n ∗ ∃ bs : List w8,
      ⌜imgBytes I bs ∧ bs.length = n⌝ ∗
      ((⌜err = interface.nil ∧ uint.nat m = bs.length⌝ ∗ W bs) ∨
       (⌜err ≠ interface.nil⌝ ∗ ∃ j, ⌜j ≤ bs.length⌝ ∗ W (bs.take j))) }}

end spec

end Backend
end EtcdGrove
end Perennial
