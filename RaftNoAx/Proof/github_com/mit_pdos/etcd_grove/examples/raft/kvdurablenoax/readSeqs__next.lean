-- The copy for the part `RaftNoAx/` of `Proof/github_com/mit_pdos/etcd_grove/examples/raft/kvdurable/readSeqs__next.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurablenoax/readSeqs__next.lean`. Lean-first (no
Rocq counterpart).

Under the lock, `last` is at least every replica's last read sequence number (`readSeqsInv`); the
number issued, `last + 1`, is fresh for the caller's id (nothing was minted at `(id, last + 1)`:
the minting discipline, `MintOk`, keeps every minted number at most its id's last one), so it is
minted in the store's invariant (`mintOk_next`) and becomes the id's last one.

It commits the context, once, to the read seeing at least the reader's committed log
(`readCtx_commit_after`): the context is fresh among the used ones because nothing was minted at its
number (kvreconf's `mintOk_read`, at `last + 1` for the id's last number `ns ≤ last`).
-/
module

public import RaftNoAx.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.readSeqs__next
public import RaftNoAx.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.ApplyLemmas
public import RaftNoAx.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.ClientLemmas
public import RaftNoAx.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.readSeqs__nextLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvdurable

open raft_kvreconf (MintOk readCtxB MintedRead freshIds)
open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]

attribute [local instance] kdStorageModel

theorem readSeqs.next.wp_proof : readSeqs.next.spec (GF := GF) (hG := hG) := by
  intro γ vs s id key l0 Hid1 Hid9 Hk
  wp_start as ⟨#Hseqs, #Hcl, #Hl0⟩
  iunfold isReadSeqs at Hseqs
  ihave #Hcl' := Hcl
  iunfold kdCluster at Hcl'
  icases Hcl' with ⟨-, -, -, -, #Hinv, -⟩
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply (lc := 1) sync.Mutex.wp_Lock _ _ $$ [$Hseqs] as ⟨Hlocked, HL⟩
  iunfold readSeqsInv at HL
  icases HL with ⟨%last, Hlast, Hids⟩
  try wp_auto
  wp_if_destruct
  · -- used up
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hseqs $Hlocked Hlast Hids]
    · inext
      iunfold readSeqsInv
      iexists _
      iframe
    try wp_auto
    iapply HΦ
    iintro %Hf
    cases Hf
  -- `last + 1`, minted for `id`
  have Hl : uint.Z last + 1 < 2 ^ 64 := by
    word
  icases BigSepL.bigSepL_lookup_acc_impl (freshIds_get γ.max id Hid1 Hid9) $$ Hids
    with ⟨⟨%ns, Hfr, %Hns⟩, Hback⟩
  imod kd_mint_next γ id ns last key l0 Hns Hl Hk $$ Hinv Hfr Hl0 with ⟨Hfr, #Hmint, #Hrc, #Hra⟩
  have Hl1 : uint.Z (last + W64 1) = uint.Z last + 1 := by word
  ihave Hids : iprop([∗list] i ∈ raft_kvreconf.freshIdsM γ.max 0, ∃ ns : w64, i ↪[γ.r.rseq] ns ∗
      ⌜uint.Z ns ≤ uint.Z (last + W64 1)⌝) $$ [Hback Hfr]
  · iapply Hback
    · imodintro
      iintro %k %y %_ %_ ⟨%ns', H, %Hle⟩
      iexists ns'
      iframe H
      ipureintro; omega
    iexists last + W64 1
    iframe Hfr
    ipureintro; omega
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hseqs $Hlocked Hlast Hids]
  · inext
    iunfold readSeqsInv
    iexists last + W64 1
    iframe
  try wp_auto
  iapply HΦ
  iintro -
  iframe Hmint Hrc Hra

end proof

end raft_kvdurable
end EtcdGrove
end Perennial
