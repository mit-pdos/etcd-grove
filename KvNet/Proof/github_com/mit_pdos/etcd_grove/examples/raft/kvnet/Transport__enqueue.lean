/-
The proof of `KvNet/Spec/.../kvnet/Transport__enqueue.lean`: a `select` with a send case on the
peer's queue and a default (Perennial's `wp_select_nonblocking`): the send case's update from the
bag channel (`queue_nb_send_au`, the message's `qElem` going into the channel), the default
`dropped` (the message kept by the caller's `qElem`, shared with the case by `∧`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Transport__enqueue
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Transport__dropped

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem Transport.enqueue.wp_proof (wp_dropped : Transport.dropped.spec (GF := GF) (hG := hG)) :
    Transport.enqueue.spec (GF := GF) (hG := hG) := by
  intro F t γ N id n p pid a m
  wp_start as ⟨#Ht, #Hp, Hq⟩
  iunfold isPeer at Hp
  icases Hp with ⟨#Hpa, %ch, %γq, #Hch, #Hbag⟩
  try wp_auto
  ihave #Hisch := is_bag_is_chan γq ch (qElem F pid) $$ Hbag
  wp_bind (App (Val (GoInstruction SelectStmt)) _)
  iapply chan.wp_select_nonblocking
  isplit
  · iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.nonblockingClausePre]
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, ch, γq, m
      isplit
      · ipureintro; exact ⟨rfl, rfl⟩
      isplit
      · iexact Hisch
      unfold nonblockingSendAu
      isplit
      · iapply queue_nb_send_au γq ch (qElem F pid) m $$ Hbag Hq
        try wp_auto
        iapply HΦ
        itrivial
      · itrivial
    · iapply BigAndL.bigAndL_nil.2
      itrivial
  · iunfold qElem at Hq
    icases Hq with ⟨%dq, %dqe, %cap, %st, %src, Hm, -, -⟩
    try wp_auto
    wp_apply wp_dropped F t γ N id n m dq dqe cap st $$ [$Hpkg $Ht $Hm] as -
    try wp_auto
    iapply HΦ
    itrivial

end proof

end raft_kvnet
end EtcdGrove
end Perennial
