Require Export New.proof.go_etcd_io.raft.election_proof.link_MemoryStorage__LastIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.link_MemoryStorage__FirstIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.link_MemoryStorage__Term.
Require Export New.proof.go_etcd_io.raft.election_proof.link_MemoryStorage__Entries.
Require Export New.proof.go_etcd_io.raft.election_proof.link_MemoryStorage__Snapshot.

(** * [MemoryStorage] meets the [Storage] contract

    [is_Storage_with (own_MemoryStorage ms) st] for [st] the interface value
    holding [ms : *MemoryStorage] -- the contract [inv_storage.v] states of a
    client-supplied [Storage], against raft's own implementation of it.

    This is not in [inv_memstorage.v], where the predicate lives, because it
    is built from the five method collections, which Require that file; it
    is a file of its own, below the links, with no triple of its own to state
    (the [Hoare] statements are [is_Storage_with]'s, and the proofs are the
    collections'). *)

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Lemma is_Storage_MemoryStorage (ms : loc) :
  ⊢ is_Storage_with (own_MemoryStorage ms)
      (interface.mk_ok (go.PointerType raft.MemoryStorage) #ms).
Proof.
  iExists (interface.mk (go.PointerType raft.MemoryStorage) #ms).
  iSplit; first done.
  (** One clause per method, each the collection's spec with the package
      initializer read out of [own_MemoryStorage]. *)
  iSplit.
  { iIntros (prev ents ss). iIntros "!#" (Φ) "Hown HΦ".
    iDestruct (own_MemoryStorage_init with "Hown") as "[#Hinit Hown]".
    wp_apply (MemoryStoragePublicLastIndex.wp_MemoryStorage__LastIndex ms prev ents ss with "[$Hown]").
    iIntros "%li [%Hli Hown]". iApply "HΦ". iFrame. done. }
  iSplit.
  { iIntros (prev ents ss). iIntros "!#" (Φ) "Hown HΦ".
    iDestruct (own_MemoryStorage_init with "Hown") as "[#Hinit Hown]".
    wp_apply (MemoryStoragePublicFirstIndex.wp_MemoryStorage__FirstIndex ms prev ents ss with "[$Hown]").
    iIntros "%fi [%Hfi Hown]". iApply "HΦ". iFrame. done. }
  iSplit.
  { iIntros (prev ents ss i0). iIntros "!#" (Φ) "[Hown %Hr] HΦ".
    iDestruct (own_MemoryStorage_init with "Hown") as "[#Hinit Hown]".
    wp_apply (MemoryStoragePublicTerm.wp_MemoryStorage__Term ms prev ents ss i0 with "[$Hown]").
    { iPureIntro. exact Hr. }
    iIntros "%t [%Ht Hown]". iApply "HΦ". iFrame. done. }
  iSplit.
  { iIntros (prev ents ss lo hi maxSize). iIntros "!#" (Φ) "[Hown %Hr] HΦ".
    iDestruct (own_MemoryStorage_init with "Hown") as "[#Hinit Hown]".
    wp_apply (MemoryStoragePublicEntries.wp_MemoryStorage__Entries ms prev ents ss lo hi maxSize with "[$Hown]").
    { iPureIntro. exact Hr. }
    iIntros "%s %es (Hs & %Hp & Hown)". iApply "HΦ". iFrame. done. }
  iSplit.
  { iIntros "!#" (prev ents ss) "Hown".
    iApply (own_MemoryStorage_bounded with "Hown"). }
  iIntros (prev ents ss esu). iIntros "!#" (Φ) "[Hown #Hesu] HΦ".
  iDestruct (own_MemoryStorage_init with "Hown") as "[#Hinit Hown]".
  wp_apply (MemoryStoragePublicSnapshot.wp_MemoryStorage__Snapshot ms prev ents ss esu with "[$Hown $Hesu]").
  iIntros "%snap %err [Hown Hr]". iApply "HΦ". iFrame.
Qed.

End proof.
