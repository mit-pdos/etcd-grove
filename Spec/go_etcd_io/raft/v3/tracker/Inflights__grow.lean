/-
Port of election_proof/spec_Inflights__grow.v (feb5c73d4).

Lean notes:
* Rocq's three-argument `own_inflights l iv buf` (the internal predicate, indexed by
  the Goose value and the ring buffer) is `ownInflightsRaw` (`InvTracker.lean`): the
  Lean name `ownInflights` is the public, record-indexed `own_Inflights`.
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

Stated on `ownInflightsRaw` at the exact buffer contents: the premise and the
conclusion are both about the **length of the buffer**, which is why `ownInflightsRaw`
is indexed by the buffer and not only by the value. (Until 2026-09-23 this was stated
over the predicate's raw pieces.) The only caller is `Inflights.Add`.

The premise `len(buffer) < size` is the "grow on demand" contract, and it is necessary
rather than convenient: with `size = 0` (hence `len(buffer) = 0`, by `InflightsOk`) the
code takes the `newSize == 0` branch and allocates **one** slot, i.e. a buffer longer
than the ring, breaking `0 ≤ len(buffer) ≤ size`. The `size < 2^62` premise -- also an
`InflightsOk` conjunct -- is what keeps `len(buffer) * 2` from overflowing `go.int`.

Both premises together give `size ≥ 1`, so the new length is
`max 1 (min (2 * len(buffer)) size)`; in particular it is *strictly* greater than the
old one, which is what `Add` needs in order to know that the slot it is about to write
is now in range. -/
abbrev tracker.Inflights.grow.spec : Prop :=
  ∀ (l : Loc) (iv : tracker.Inflights) (buf : List tracker.inflight),
  (buf.length : Int) < sint.Z iv.size' →
  sint.Z iv.size' < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗
      "Hin" ∷ ownInflightsRaw l iv buf }}
    (App (Val (l @!! go.GoType.PointerType tracker.Inflights.ty @!! go!"grow")) (Val #()))
  {{ (sl : GoSlice) (buf' : List tracker.inflight), RET #();
      "Hin" ∷ ownInflightsRaw l { iv with buffer' := sl } buf' ∗
      "%Hlen" ∷ ⌜(buf'.length : Int)
                  = max 1 (min (2 * (buf.length : Int)) (sint.Z iv.size'))⌝ ∗
      "%Hcontents" ∷ ⌜buf' = buf ++ List.replicate (buf'.length - buf.length)
                                       (zero_val tracker.inflight)⌝ }}

end spec

end EtcdGrove
end Perennial
