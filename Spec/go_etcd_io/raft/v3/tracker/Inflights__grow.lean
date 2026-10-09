/-
Port of election_proof/spec_Inflights__grow.v (feb5c73d4).

Lean notes:
* Rocq's three-argument `own_inflights l iv buf` (the internal predicate, indexed by
  the Goose value and the ring buffer) is `ownInflightsRaw l r` (`InvTracker.lean`),
  indexed by the pure record `r : InflightsRing` the two denote; the Lean name
  `ownInflights` is the public, record-indexed `own_Inflights`.
* The reference `Inflights__growⁱᵐᵖˡ` is to the Lean generated code
  `tracker.Inflights.grow.impl`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `in.grow()` doubles the ring buffer, capped at `in.size`
(`tracker.Inflights.grow.impl`, `Code/go_etcd_io/raft/v3/tracker.lean`):

    newSize := len(in.buffer) * 2
    if newSize == 0 { newSize = 1 } else if newSize > in.size { newSize = in.size }
    newBuffer := make([]inflight, newSize)
    copy(newBuffer, in.buffer)
    in.buffer = newBuffer

Stated on `ownInflightsRaw` at the buffer's length `r.buflen`: the premise and the
conclusion are both about it, which is why `InflightsRing` has it. The new buffer is a
new slice holding the old contents and zeroes, but no spec needs either, so the
postcondition says only that the length changes and nothing else does
(`{ r with buflen := … }`). (Until 2026-09-23 this was stated over the predicate's raw
pieces; until 2026-10-08 on the Goose value and the buffer's contents, with the new
slice `sl` in `{ iv with buffer' := sl }` and the new contents spelled out.) The only
caller is `Inflights.Add`.

The premise `len(buffer) < size` is the "grow on demand" contract, and it is necessary
rather than convenient: with `size = 0` (hence `len(buffer) = 0`, by `InflightsOk`) the
code takes the `newSize == 0` branch and allocates **one** slot, i.e. a buffer longer
than the ring, breaking `0 ≤ len(buffer) ≤ size`. `InflightsOk`'s `size < 2^62` -- a
premise here until 2026-10-08, but the predicate already has it -- is what keeps
`len(buffer) * 2` from overflowing `go.int`.

Both premises together give `size ≥ 1`, so the new length is
`max 1 (min (2 * len(buffer)) size)`; in particular it is *strictly* greater than the
old one, which is what `Add` needs in order to know that the slot it is about to write
is now in range. -/
abbrev tracker.Inflights.grow.spec : Prop :=
  ∀ (l : Loc) (r : InflightsRing),
  r.buflen < r.win.size →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗
      "Hin" ∷ ownInflightsRaw l r }}
    (App (Val (l @!! go.GoType.PointerType tracker.Inflights.ty @!! go!"grow")) (Val #()))
  {{ RET #();
      "Hin" ∷ ownInflightsRaw l { r with buflen := max 1 (min (2 * r.buflen) r.win.size) } }}

end spec

end EtcdGrove
end Perennial
