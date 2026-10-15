/- `MemoryStorage.Append` (`storage.go:280`), specified 2026-10-10 (Lean-first: no
Rocq counterpart), for the application's side of the pending append
(notes/decisions.md, "Storage: a pending append, for node.go").
-/
module

public import Raft37.Proof.go_etcd_io.raft.v3.InvMemstorage

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

/-- `ms.Append(entries)`: with the right to append `p` (`memAppendTok`, which the
storage's owner handed out at the state `σ` with nothing pending: raft's `Ready`), the
storage takes the batch the way `storApp` says -- everything from the batch's first
index on is replaced -- under its lock, so concurrently with the owner's reads, and
returns the receipt (`memAppendedTok`) and no error.

The premise bounds the batch: its last index is below `2^61`, which is what the
storage's bound (`isStorage`'s `Hbounded`) needs once the batch is in -- a client
assumption, as that clause is (no raft log comes near). The token's `PendOk` makes the
two `Append` exits that drop or cut the batch, and its `Panicf` on a gap, unreachable:
the batch starts above the compaction boundary and at most one past the stored
entries.

An empty batch needs no token (2026-10-10): `Append` returns at once, as the empty
case of a `Ready`'s `appendRight`/`appendReceipt` (`InvStorage.lean`) has it.

raft v3.7 (stage R3, 2026-10-15): `entries` is a `[]*pb.Entry` and `Append` keeps the caller's
pointers (`append(ms.ents[:offset:offset], entries...)`, `storage.go:318-321`), so the batch
comes as `entsPts s dq p` -- each entry a read-only log entry (`entRO`), which the storage then
shares. Until the retarget the batch's values were copied and only the slice was lent; now
the entries must be frozen before they are appended (they are: a `Ready`'s entries are the
log's, `entRO` since raft appended them). The slice itself comes back. -/
abbrev MemoryStorage.Append.spec : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (σ : StorState) (p : List EntryM) (s : GoSlice)
    (dq : DFrac),
  (∀ e0, p.head? = some e0 → uint.Z e0.Index' + (p.length : Int) ≤ 2^61) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Htok" ∷ (⌜p = []⌝ ∨ memAppendTok ms γs σ p) ∗
      "Hs" ∷ entsPts s dq p }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"Append")) (Val #s))
  {{ RET #interface.nil; (⌜p = []⌝ ∨ memAppendedTok ms γs σ p) ∗ entsPts s dq p }}

end spec

end EtcdGrove
end Perennial
