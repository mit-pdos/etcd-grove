/-
Port of election_proof/spec_unstable__truncateAndAppend.v (857d09190).

Lean notes:
* Rocq's `bool_decide (P)` in the two `if`s is `decide (P)` (Lean's `if` on a
  decidable proposition); `DfracDiscarded` is `DFrac.discard`; `is_Logger` is
  `isLogger` (`InvLogger.lean`); `take (Z.to_nat x) l` is `l.take x.toNat`; Rocq's
  `` `min` `` on `Z` is `min`.
* `trunc_offsetInProgress` is `truncOffsetInProgress`.
* The reference `unstable__truncateAndAppendⁱᵐᵖˡ, new/code/go_etcd_io/raft/v3.v:1650`
  is to the Lean generated code `unstable.truncateAndAppend.impl`.
-/
import EtcdGrove.Raft.InvRaftPhys

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-- `offsetInProgress` after the call, by arm (2026-10-05, for `Ready`): kept by arm 1,
the new offset `fromIndex` in arm 2, `min(offsetInProgress, fromIndex)` in arm 3. A
definition so that the proof's case splits on the arms do not reach into it. -/
def truncOffsetInProgress [FfiSyntax] (uv : unstable) (n : Nat) (f : w64) : w64 :=
  if uint.Z f = uint.Z uv.offset' + (n : Int) then uv.offsetInProgress'
  else if uint.Z f ≤ uint.Z uv.offset' then f
  else w64Min uv.offsetInProgress' f

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `u.truncateAndAppend(ents)`: splice a non-empty batch into the unstable suffix
(`unstable.truncateAndAppend.impl`, `EtcdRaft/Code/go_etcd_io/raft/v3.lean`).

The body switches on where the batch starts, `fromIndex = ents[0].Index`:

  1. `fromIndex == u.offset+len(u.entries)`: it continues the suffix,
     `u.entries = append(u.entries, ents...)`;
  2. `fromIndex <= u.offset`: `Infof`, then the suffix is *replaced*:
     `u.entries = ents`, `u.offset = fromIndex`, `u.offsetInProgress = u.offset`;
  3. otherwise: `Infof`, then `keep := u.slice(u.offset, fromIndex)`,
     `u.entries = append(keep, ents...)`,
     `u.offsetInProgress = min(u.offsetInProgress, fromIndex)`.

All three are specified (since 2026-10-01; before, only arm 1). One statement covers
them: the new suffix is `take (fromIndex - u.offset) uents ++ ents` (`take 0` in arm 2,
where the difference is `<= 0`; `take len` in arm 1) and the new offset is `fromIndex`
if that is below `u.offset`, else `u.offset`. The premise
`fromIndex <= u.offset + len` is what keeps arm 3's `u.slice` inside the suffix (its
`mustCheckOutOfBounds` `Panicf`s otherwise); the no-wrap premise is `u.slice`'s.
`u.logger` is a `Logger` for the two `Infof`s.

**Ownership of the batch.** Arms 1 and 3 copy the entry values (`append`), so the
batch is lent and comes back. Arm 2 *adopts the caller's slice*: `u.entries` then
aliases it, and a later arm-1 `append` may write into its capacity slack
(notes/raft-implementation-facts.md, "Which slices raft hands out uncapped"). So in
that arm -- exactly when `fromIndex <= u.offset` and the batch does not continue the
suffix -- the caller must hand the batch over read-only (`dq = DFrac.discard`) together
with its capacity, and gets nothing back. The condition is computed in the spec, so a
caller that knows its batch continues the suffix (`appendEntry`) owes nothing extra.

The new `unstable` value is existential, with the three fields `ownRaftLog` tracks
pinned: `offset` as above, `snapshot` and `logger` unchanged. `offsetInProgress` is not
tracked by anything. -/
abbrev unstable.truncateAndAppend.spec : Prop :=
  ∀ (u : Loc) (uv : unstable) (uents ents : List raftpb.Entry)
    (e0 : raftpb.Entry) (es : GoSlice) (dq : DFrac) (ulg : GoInterfaceOk),
  ents[0]? = some e0 →
  uint.Z e0.Index' ≤ uint.Z uv.offset' + (uents.length : Int) →
  uint.Z uv.offset' + (uents.length : Int) < 2 ^ 64 →
  uv.logger' = interface.ok ulg →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hun" ∷ ownUnstable u uv uents ∗
      "Hes" ∷ es ↦*{dq} ents ∗
      "#Hlg" ∷ isLogger ulg ∗
      "Hadopt" ∷ (if uint.Z e0.Index' ≤ uint.Z uv.offset' ∧
                     uint.Z e0.Index' ≠ uint.Z uv.offset' + (uents.length : Int)
                  then iprop(⌜dq = DFrac.discard⌝ ∗
                             ownSliceCap raftpb.Entry es (DFrac.own 1))
                  else True) }}
    (App (Val (u @!! go.GoType.PointerType unstable.ty @!! go!"truncateAndAppend"))
      (Val #es))
  {{ (uv' : unstable), RET #();
      ownUnstable u uv'
        (uents.take (uint.Z e0.Index' - uint.Z uv.offset').toNat ++ ents) ∗
      ⌜uint.Z uv'.offset' = min (uint.Z e0.Index') (uint.Z uv.offset') ∧
        uv'.snapshot' = uv.snapshot' ∧
        uv'.logger' = uv.logger' ∧
        -- `offsetInProgress`, by arm (2026-10-05, for `Ready`)
        uv'.offsetInProgress' = truncOffsetInProgress uv uents.length e0.Index'⌝ ∗
      (if uint.Z e0.Index' ≤ uint.Z uv.offset' ∧
          uint.Z e0.Index' ≠ uint.Z uv.offset' + (uents.length : Int)
       then True else es ↦*{dq} ents) }}

end spec

end EtcdGrove
end Perennial
