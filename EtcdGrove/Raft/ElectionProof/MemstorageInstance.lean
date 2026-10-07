/-
Port of `election_proof/memstorage_instance.v` (at feb5c73d4).

### `MemoryStorage` meets the `Storage` contract

`isStorageWith (ownMemoryStorage ms) st` for `st` the interface value holding
`ms : *MemoryStorage` -- the contract `InvStorage.lean` states of a client-supplied
`Storage`, against raft's own implementation of it.

This is not in `InvMemstorage.lean`, where the predicate lives, because it is built from
the five method collections, which import that file; it is a file of its own, below the
links (`Election.lean`), with no triple of its own to state (the Hoare statements are
`isStorageWith`'s, and the proofs are the collections').

Lean notes: the method clauses of `isStorageWith` call `methods i.ty go!"M" i.v`, and the
collections' specs call `ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"M"`; for
`i = interface.mk (go.GoType.PointerType MemoryStorage.ty) #ms` the two are the same term
up to unfolding, so `wp_apply` of the collection's result closes each clause directly (as
Perennial's `sync.Mutex_is_Locker` does).
-/
import EtcdGrove.Raft.ElectionProof.Election

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem is_Storage_MemoryStorage (ms : Loc) :
    ⊢ isStorageWith (GF := GF) (ownMemoryStorage ms)
        (interface.mkOk (go.GoType.PointerType MemoryStorage.ty) #ms) := by
  unfold isStorageWith
  iexists (interface.mk (go.GoType.PointerType MemoryStorage.ty) #ms)
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro %prev %ents %ss
    imodintro
    iintro %Φ Hown HΦ
    ihave ⟨#Hinit, Hown⟩ := ownMemoryStorage_init $$ Hown
    wp_apply MemoryStorage.wp_LastIndex $$ [$Hown] as %li ⟨%Hli, Hown⟩
    iapply HΦ
    iframe
    ipureintro; exact Hli
  isplitr
  · iintro %prev %ents %ss
    imodintro
    iintro %Φ Hown HΦ
    ihave ⟨#Hinit, Hown⟩ := ownMemoryStorage_init $$ Hown
    wp_apply MemoryStorage.wp_FirstIndex $$ [$Hown] as %fi ⟨%Hfi, Hown⟩
    iapply HΦ
    iframe
    ipureintro; exact Hfi
  isplitr
  · iintro %prev %ents %ss %i0
    imodintro
    iintro %Φ ⟨Hown, %Hr⟩ HΦ
    ihave ⟨#Hinit, Hown⟩ := ownMemoryStorage_init $$ Hown
    wp_apply MemoryStorage.wp_Term $$ [$Hown] as %t ⟨%Ht, Hown⟩
    · ipureintro; exact Hr
    iapply HΦ
    iframe
    ipureintro; exact Ht
  isplitr
  · iintro %prev %ents %ss %lo %hi %maxSize
    imodintro
    iintro %Φ ⟨Hown, %Hr⟩ HΦ
    ihave ⟨#Hinit, Hown⟩ := ownMemoryStorage_init $$ Hown
    wp_apply MemoryStorage.wp_Entries $$ [$Hown] as %s %es ⟨Hs, %Hp, Hown⟩
    · ipureintro; exact Hr
    iapply HΦ
    iframe
    ipureintro; exact Hp
  isplitr
  · imodintro
    iintro %prev %ents %ss Hown
    iapply ownMemoryStorage_bounded $$ Hown
  iintro %prev %ents %ss %esu
  imodintro
  iintro %Φ ⟨Hown, #Hesu⟩ HΦ
  ihave ⟨#Hinit, Hown⟩ := ownMemoryStorage_init $$ Hown
  wp_apply MemoryStorage.wp_Snapshot $$ [$Hown $Hesu] as %snap %err ⟨Hown, Hr⟩
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
