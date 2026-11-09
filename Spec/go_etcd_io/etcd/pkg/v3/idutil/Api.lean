/-
# `pkg/idutil`: the request id generator (batch 2c), vocabulary

`Generator.Next()` returns `prefix | lowbit(suffix, 48)` for an atomically incremented `suffix`
(`id.go`); `NewGenerator(memberID, now)` sets the prefix to the member id's low 16 bits shifted to
the top and the suffix to the 40 low bits of `now` in milliseconds, shifted by 8. The server uses one
generator per run for its request ids (`processInternalRaftRequestOnce`: the wait registry's key and
the entry's `Header.ID`, by which every member's apply thread delivers results), its read contexts
(`read.Read.requestCurrentIndex` through `NextRequestID`: raft's `readCtx_register` needs a context
fresh in the whole raft cluster) and the ids of leases granted with `ID = 0` (`LeaseGrant`).

## Vocabulary

* `IdSpace` (opaque ghost names): one cluster's id space, shared by the generators of all its
  members and all their runs.
* `idSpaceAuth γi ps` (exclusive): the prefixes taken so far (the initial members' and each added
  member's: `idSpaceAuth_add` takes a fresh, non-zero prefix for a member a `MemberAdd` added; 2e
  holds it).
* `idPrefixes γi p` (exclusive): the stock of generator tokens of the 16-bit prefix `p`, one per run
  of the member owning `p` (`idPrefixes_take`). Allocated for the cluster's initial prefixes, which
  must be distinct and non-zero (`idSpace_alloc`), and one per added member.
* `idPrefix γi p` (exclusive): one run's generator token of prefix `p`, consumed by `NewGenerator`.
* `idGen g γi` (persistent): `g` is a generator of `γi`.
* `idFresh γi id` (exclusive): **`id` was issued once in the whole id space**, and is not `0`. The
  one law that matters, `idFresh_excl`: two tokens are two different ids. A client turns its tokens
  into whatever registry it keeps (the server's wait registry, raft's read contexts).

## Intended realization

A ghost set of the ids issued in `γi` (`ghost_map` of `w64`): `idFresh γi id` its element; the
generator's invariant holds its prefix's issued count; distinct prefixes give distinct ids, and the
`0` id is never issued (prefix non-zero). Within one run the `2 ^ 48` wrap is excluded by Perennial's
time receipts (one per `atomic.AddUint64`, the receipt bound `≤ 2 ^ 48` fixed by the adequacy
theorem: the bound at its owner). **Across the runs of one member** (`idPrefixes_take` gives a fresh
token per run) freshness is a trust-boundary assumption of `Next`'s model (the `IdIssue`
extension, as before this branch): **`Generator.Next.spec` is an assumed contract, false across runs
in general**: a run whose predecessor issued more than `256` ids per millisecond on average since its
start, or with the clock gone back, can reissue an id
(`nonissues/etcd-request-id-restart-reuse.md`). Across members it rests on the allocation's
distinct prefixes, a premise etcd does not ensure (`nonissues/etcd-request-id-member-prefix.md`);
the non-zero prefix excludes the bootstrap conf changes' id `0`
(`nonissues/etcd-request-id-zero-bootstrap-confchange.md`).

## Requirement snippets

`examples/specreq/wait/idutil.go` (`ReqIdsDistinct`, `ReqIdNonZero`).
-/
module

public import GeneratedProof.go_etcd_io.etcd.pkg.v3.idutil
public import Spec.PkgInit.go_etcd_io.etcd.pkg.v3.idutil

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace IdUtil

open Iris Iris.BI

/-- One cluster's id space (opaque ghost names). -/
opaque IdSpace : Type := Unit

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- The prefixes taken so far. Exclusive. -/
opaque idSpaceAuth [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γi : IdSpace) (ps : List w16) : IProp GF := iprop(True)

/-- The stock of generator tokens of prefix `p` (one per run). Exclusive. -/
opaque idPrefixes [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γi : IdSpace) (p : w16) : IProp GF := iprop(True)

/-- One run's generator token of prefix `p`. Exclusive. -/
opaque idPrefix [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γi : IdSpace) (p : w16) : IProp GF := iprop(True)

/-- `g` is a generator of the id space `γi`. Persistent. -/
opaque idGen [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (g : Loc) (γi : IdSpace) : IProp GF := iprop(True)

/-- **`id` was issued once in `γi`** (and is not `0`). Exclusive. -/
opaque idFresh [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γi : IdSpace) (id : w64) : IProp GF := iprop(True)

/-- Allocation of an id space for a cluster whose members own the prefixes `ps` (distinct, non-zero:
etcd's member ids truncated to 16 bits; see the header). -/
def idSpace_alloc.spec : Prop := ∀ (ps : List w16), ps.Nodup → (∀ p ∈ ps, p ≠ W16 0) →
  ⊢ |==> ∃ γi : IdSpace, idSpaceAuth (GF := GF) γi ps ∗ [∗list] p ∈ ps, idPrefixes γi p

/-- A prefix for a member added later (fresh, non-zero). -/
def idSpaceAuth_add.spec : Prop := ∀ (γi : IdSpace) (ps : List w16) (p : w16), p ∉ ps → p ≠ W16 0 →
  idSpaceAuth (GF := GF) γi ps ⊢ |==> idSpaceAuth γi (p :: ps) ∗ idPrefixes γi p

/-- A run's token, the stock kept (for the member's later runs). -/
def idPrefixes_take.spec : Prop := ∀ (γi : IdSpace) (p : w16),
  idPrefixes (GF := GF) γi p ⊢ |==> idPrefixes γi p ∗ idPrefix γi p

def idGen_persistent.spec : Prop := ∀ g γi, Persistent (idGen (GF := GF) g γi)
def idFresh_timeless.spec : Prop := ∀ γi id, Timeless (idFresh (GF := GF) γi id)

/-- **Issued ids are distinct.** -/
def idFresh_excl.spec : Prop := ∀ (γi : IdSpace) (id : w64),
  idFresh (GF := GF) γi id ∗ idFresh γi id ⊢ iprop(False)

/-- Issued ids are not `0` (the id of raft's bootstrap conf changes). -/
def idFresh_ne_zero.spec : Prop := ∀ (γi : IdSpace) (id : w64),
  idFresh (GF := GF) γi id ⊢ ⌜id ≠ W64 0⌝

end vocab

end IdUtil
end EtcdGrove
end Perennial
