/-
The state of a freelist (`internal/freelist`), and the predicates of its two
implementations (`array`, `hashMap`).

A freelist's state (`FLState`) is what the specs speak of:
* `free`: the free page ids (`array` keeps them sorted; `hashMap` as spans: its `free` is the
  sorted list of the pages of its spans);
* `pending`: for each transaction id, the pages it freed (not reusable until no reader can see
  them), each with the id of the transaction that allocated it (`alloctx`, `0` if unknown),
  and the start of the last `releaseRange` that looked at it;
* `allocs`: the transaction that allocated each page (as far as it is known);
* `readonly`: the ids of the open read-only transactions.

The `cache` map is a function of the state (every free or pending id), so it is not part of
it: `ownShared` says that the map holds exactly those keys.

`shared` embeds the freelist interface (`shared.Interface`), and its methods call back
through it (`t.FreeCount()`, `t.Init(..)`): `ownShared s iface σ` is about the `shared` at
`s` whose interface field is `iface`; `ownArray a σ` is the whole freelist at `a`, an `array`
whose `shared` points back to it.
-/
module

public import Proof.go_etcd_io.bbolt.Init
public import GeneratedProof.go_etcd_io.bbolt.internal.freelist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.freelist

/-- A transaction's pending pages (`txPending`). -/
structure Pending where
  ids : List w64
  alloctx : List w64
  lastReleaseBegin : w64

/-- The state of a freelist. -/
structure FLState where
  free : List w64
  pending : GMap w64 Pending
  allocs : GMap w64 w64
  readonly : List w64

/-- `id` is free or pending in `σ`. -/
def FLState.cached (σ : FLState) (id : w64) : Prop :=
  id ∈ σ.free ∨ ∃ t p, σ.pending !! t = some p ∧ id ∈ p.ids

section preds
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- A `*txPending` at `p` holding `pd`. -/
def ownPending (p : Loc) (pd : Pending) : IProp GF :=
  iprop(∃ (tv : txPending),
    "Hp" ∷ p ↦ tv ∗
    "Hids" ∷ tv.ids' ↦* pd.ids ∗ "Hids_cap" ∷ ownSliceCap w64 tv.ids' (DFrac.own 1) ∗
    "Hatx" ∷ tv.alloctx' ↦* pd.alloctx ∗
    "Hatx_cap" ∷ ownSliceCap w64 tv.alloctx' (DFrac.own 1) ∗
    "%Hpd" ∷ ⌜tv.lastReleaseBegin' = pd.lastReleaseBegin ∧ pd.ids.length = pd.alloctx.length⌝)

/-- The `shared` at `s`, with interface field `iface`, in state `σ` (all but `free`, which
the implementation keeps). -/
def ownShared (s : Loc) (iface : GoInterface) (σ : FLState) : IProp GF :=
  iprop(∃ (sv : shared) (c : GMap w64 Unit) (pp : GMap w64 Loc),
    "Hs" ∷ s ↦ sv ∗ "%Hiface" ∷ ⌜sv.Interface' = iface⌝ ∗
    "Hro" ∷ sv.readonlyTXIDs' ↦* σ.readonly ∗
    "Hro_cap" ∷ ownSliceCap w64 sv.readonlyTXIDs' (DFrac.own 1) ∗
    "Hallocs" ∷ sv.allocs' ↦$ σ.allocs ∗
    "Hcache" ∷ sv.cache' ↦$ c ∗ "%Hc" ∷ ⌜∀ id, (c !! id).isSome ↔ σ.cached id⌝ ∗
    "Hpending" ∷ sv.pending' ↦$ pp ∗
    "%Hpp" ∷ ⌜∀ t, (pp !! t).isSome ↔ (σ.pending !! t).isSome⌝ ∗
    "Hpds" ∷ [∗map] t ↦ p ∈ pp, ∃ pd, ⌜σ.pending !! t = some pd⌝ ∗ ownPending p pd)

/-- The `array` freelist at `a` in state `σ`: its `shared` points back to it, and it keeps
the free ids, sorted. -/
def ownArray (a : Loc) (σ : FLState) : IProp GF :=
  iprop(∃ (av : array'),
    "Ha" ∷ a ↦ av ∗
    "Hshared" ∷ ownShared av.shared' (interface.mkOk (go.GoType.PointerType array'.ty) #a) σ ∗
    "Hids" ∷ av.ids' ↦* σ.free ∗ "Hids_cap" ∷ ownSliceCap w64 av.ids' (DFrac.own 1))

end preds

end bbolt
end EtcdGrove
end Perennial
