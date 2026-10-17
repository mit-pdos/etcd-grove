/-
Lean-first (etcd-io/raft#96, which replaces `shrinkEntriesArray` by this function and moves the
re-slicing of `stableTo` into it).
-/
module

public import Proof.go_etcd_io.raft.v3.InvReadylog

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

/-- `u.shrinkEntriesSlice(k)` (`log_unstable.go:169`, raft#96): drops the first `k` entries of
`u.entries` -- `nil` when that is all of them, a copy of the rest into a fresh array of exactly
their length when `doEntriesNeedCompaction(k)` says so, a re-slice otherwise. Only `u.entries` is
written; the state is the old one less its first `k` entries, with `offset` (and everything
else) untouched -- the caller (`stableTo`) moves `offset` afterwards. `0 ≤ k ≤ len(u.entries)`,
as `stableTo` guarantees on a hit (`k = id.index + 1 - offset ≥ 1`); outside it the re-slice (or
`compactEntriesSlice`'s `make`) panics.

The old `shrinkEntriesArray.spec` (the state unchanged, the slice already re-sliced by the
caller) is this one at `k = 0`, but nothing calls it that way any more: the two specs describe the
same functional effect of `stableTo`, which is unchanged (`unstable.stableTo.spec`). Which branch
is taken -- the memory the PR is about -- is not observable in the state (the model has no
notion of retained memory), so this spec, like the old one, does not distinguish them. -/
abbrev unstable.shrinkEntriesSlice.spec : Prop :=
  ∀ (u : Loc) (us : UnstableSt) (k : w64),
  0 ≤ sint.Z k → sint.Z k ≤ (us.ents.length : Int) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hun" ∷ ownUnstable u us }}
    (App (Val (u @!! go.GoType.PointerType unstable.ty @!! go!"shrinkEntriesSlice")) (Val #k))
  {{ RET #(); ownUnstable u { us with ents := us.ents.drop (sint.Z k).toNat } }}

end spec

end EtcdGrove
end Perennial
