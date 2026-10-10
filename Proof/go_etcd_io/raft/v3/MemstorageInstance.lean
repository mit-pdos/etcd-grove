/-
Port of `election_proof/memstorage_instance.v` (at feb5c73d4).

### `MemoryStorage` meets the `Storage` contract

`isStorageWith (ownMemoryStorage ms) st` for `st` the interface value holding
`ms : *MemoryStorage` -- the contract `InvStorage.lean` states of a client-supplied
`Storage`, against raft's own implementation of it.

This is not in `InvMemstorage.lean`, where the predicate lives, because it is built from
the five method collections, which import that file; it is a file of its own, below the
links (`Link.lean`), with no triple of its own to state (the Hoare statements are
`isStorageWith`'s, and the proofs are the collections').

Lean notes: the method clauses of `isStorageWith` call `methods i.ty go!"M" i.v`, and the
collections' specs call `ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"M"`; for
`i = interface.mk (go.GoType.PointerType MemoryStorage.ty) #ms` the two are the same term
up to unfolding, so `wp_apply` of the collection's result closes each clause directly (as
Perennial's `sync.Mutex_is_Locker` does).
-/
module

public import Proof.go_etcd_io.raft.v3.Link

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A `MemoryStorage` with a snapshot meets the contract, with its own hand-out and
receipt (`memAppendTok`, `memAppendedTok`, `InvMemstorage.lean`). The snapshot premise
(`ss.index ≠ 0`, until 2026-10-10 a conjunct of `ownMemoryStorage`) is the contract's
`Snapshot` clause, which promises a non-empty snapshot: a new storage
(`NewMemoryStorage`) has none, and raft's `maybeSendSnapshot` panics on an empty one.
It is reached only after a storage query failed, which `ErrCompacted` does only once the
storage has compacted -- but also after an `ErrUnavailable` for a peer's `Next` past the
log, which nothing proved here bounds (notes/decisions.md, "Storage: a pending append,
for node.go"). Both laws keep `ss`. -/
theorem is_Storage_MemoryStorage (ms : Loc) (γs : MemStorNames) :
    ⊢ isStorageWith (GF := GF) (fun σ => iprop(ownMemoryStorage ms γs σ ∗ ⌜σ.ss.index' ≠ W64 0⌝))
        (memAppendTok ms γs) (memAppendedTok ms γs)
        (interface.mkOk (go.GoType.PointerType MemoryStorage.ty) #ms) := by
  unfold isStorageWith
  simp only []
  iexists (interface.mk (go.GoType.PointerType MemoryStorage.ty) #ms)
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro %σ
    imodintro
    iintro %Φ ⟨⟨Hown, %Hss⟩, %Hpn⟩ HΦ
    ihave ⟨#Hinit, Hown⟩ := ownMemoryStorage_init $$ Hown
    wp_apply MemoryStorage.wp_LastIndex $$ [$Hown] as %li ⟨%Hli, Hown⟩
    · ipureintro; exact Hpn
    iapply HΦ
    iframe
    ipureintro; exact ⟨Hli, Hss⟩
  isplitr
  · iintro %σ
    imodintro
    iintro %Φ ⟨Hown, %Hss⟩ HΦ
    ihave ⟨#Hinit, Hown⟩ := ownMemoryStorage_init $$ Hown
    wp_apply MemoryStorage.wp_FirstIndex $$ [$Hown] as %fi ⟨%Hfi, Hown⟩
    iapply HΦ
    iframe
    ipureintro; exact ⟨Hfi, Hss⟩
  isplitr
  · iintro %σ %i0
    imodintro
    iintro %Φ ⟨⟨Hown, %Hss⟩, %Hr, %Hpf⟩ HΦ
    ihave ⟨#Hinit, Hown⟩ := ownMemoryStorage_init $$ Hown
    wp_apply MemoryStorage.wp_Term $$ [$Hown] as %t ⟨%Ht, Hown⟩
    · ipureintro; exact ⟨Hr, Hpf⟩
    iapply HΦ
    iframe
    ipureintro; exact ⟨Ht, Hss⟩
  isplitr
  · iintro %σ %lo %hi %maxSize
    imodintro
    iintro %Φ ⟨⟨Hown, %Hss⟩, %Hr, %Hpf⟩ HΦ
    ihave ⟨#Hinit, Hown⟩ := ownMemoryStorage_init $$ Hown
    wp_apply MemoryStorage.wp_Entries $$ [$Hown] as %s %es ⟨Hs, %Hp, Hown⟩
    · ipureintro; exact ⟨Hr, Hpf⟩
    iapply HΦ
    iframe
    ipureintro; exact ⟨Hp, Hss⟩
  isplitr
  · imodintro
    iintro %σ ⟨Hown, %Hss⟩
    icases ownMemoryStorage_bounded $$ Hown with ⟨%Hb, Hown⟩
    iframe
    ipureintro; exact ⟨Hb, Hss⟩
  isplitr
  · iintro %σ %esu
    imodintro
    iintro %Φ ⟨⟨Hown, %Hss⟩, #Hesu⟩ HΦ
    ihave ⟨#Hinit, Hown⟩ := ownMemoryStorage_init $$ Hown
    wp_apply MemoryStorage.wp_Snapshot $$ [$Hown $Hesu] as %snap %err ⟨Hown, Hr⟩
    iapply HΦ
    iframe Hown
    isplitr
    · ipureintro; exact Hss
    icases Hr with (%Herr | ⟨%Herr, Hv⟩)
    · ileft; ipureintro; exact Herr
    iright
    iframe Hv
    ipureintro
    refine ⟨Herr.1, Herr.2, ?_⟩
    have H := congrArg entryID.index' Herr.2
    simp only [snapId] at H
    rw [H]; exact Hss
  isplitr
  · imodintro
    iintro %σ %p ⟨Hown, %Hss⟩ %Hpo
    imod memStorage_handout ms γs σ p Hpo $$ Hown with ⟨Hown, Htok⟩
    imodintro
    iframe
    ipureintro; exact Hss
  imodintro
  iintro %σ1 %σ %p ⟨Hown, %Hss⟩ Ht
  imod memStorage_absorb ms γs σ1 σ p $$ Hown Ht with ⟨%Heq, Hown⟩
  imodintro
  iframe
  ipureintro; exact ⟨Heq, Hss⟩

end proof

end EtcdGrove
end Perennial
