/-
etcd's consistent index (`server/v3/etcdserver/cindex/cindex.go`) and its reads and writes of
the backend (`server/v3/storage/schema/cindex.go`): the shared vocabulary of
`Spec/consistentIndex__*.lean`, `Spec/NewConsistentIndex.lean` and the `schema` specs.
Lean-first (no Rocq counterpart).

A `consistentIndex` caches the backend's `consistent_index` key: the index of the last raft
entry whose effects the backend holds. Its four `uint64`s are atomics; `be` is the backend
it lazily loads the index from, under `mutex`.

**The index and its term.** `consistentIndex`/`term` are read and written by several
goroutines (the apply thread sets them; a backend commit, under the batch transaction's lock,
saves them with `UnsafeSave`), so they live in an invariant (`ciInv`) with half of a ghost
variable mirroring the index; the client holds the other half (`ciIdx γ k`), which it
keeps in its own invariant. The specs of the operations that read or write the index are
logically atomic, in Perennial's style for `sync/atomic`: the caller passes a fancy update
that, at the moment the index is read or stored, hands over `ciIdx γ k` and gets it back
(updated). The term is not mirrored: it is whatever was last stored, and only the
backend's copy of it is ever read back. `SetConsistentIndex` stores the index, *then* the
term: two atomic steps, so a concurrent `UnsafeSave` can save a new index with the old term
(see notes/decisions.md); the specs say nothing about the term for that reason.

**The applying index** (`applyingIndex`/`applyingTerm`) is only ever accessed by the apply
thread, which owns the two fields outright (`ciApplying`).

**The backend field.** `be` is written by `SetBackend` under `mutex`, read by
`ConsistentIndex` under `mutex`, and read by `UnsafeConsistentIndex` *without* it. So half
of `ci.be ↦ b` is the mutex's, the other half the owner's (`ciOwner ci b`, the apply
thread's): writing needs both, reading either. Every caller of `ConsistentIndex` in etcd is
on the apply path (the apply loop, the entry applier's deferred update, the auth applier,
`snapshot`), so its spec asks for `ciOwner` too.

**The backend's meta keys** are an abstract view `View : MetaCI → IProp`, chosen by the
client: `metaReader r E View` is the contract of an `UnsafeReader` whose `UnsafeRange` on the
two keys is a linearizable read of the view (a fancy update at mask `E`), `metaReadTx` that
of a `ReadTx` (`RLock`/`RUnlock` too), `isMetaBackend b E View` that of a `Backend` whose
`ReadTx()` returns one; `metaWriter tx TM` is the contract of the batch transaction (an
`UnsafeReadWriter`) the lock holder writes through, whose meta keys are `TM m`, owned. These
are definitions: a client supplies the triples with its backend, as raft's clients do with
`Storage`. A stored value is the 8-byte big-endian encoding of a non-zero `uint64`; an absent
key reads as 0 (`schema` never stores 0).

**Slices read under a resource** (2026-10-13, unit 7): a read's value slice is readable with
`Acc m` (`metaValsA`): the real batch transaction's slices are bbolt's, valid while its lock is
held (`Acc := TM`, the lock holder's meta keys: `metaWriter`); a `ReadTx`'s are the assumed
contract's, `Acc := True`. **Puts with tokens**: `metaWriter tx TM PTi PTt`'s puts of the index and
of the term each spend a token (`PTi`, `PTt`): the real backend's pre-commit hook may put at most
`hookMax` entries, so the hook's batch transaction hands out one token per key
(`CindexBackend.lean`); the puts store non-zero values only.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.cindex
  go_etcd_io.etcd.server.v3.storage

/-! ## Big-endian encoding -/

/-- The big-endian encoding of `x` (`binary.BigEndian.PutUint64`). -/
def u64Be (x : w64) : List w8 := (u64Le x).reverse

/-! ## The meta keys -/

-- The field addresses of a `consistentIndex`.
section addrs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

end addrs

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-! ## The backend's contracts -/

end defs

/-! ## Atomics on owned fields -/

section atomics
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.atomic.Assumptions]

end atomics

end EtcdGrove
end Perennial
