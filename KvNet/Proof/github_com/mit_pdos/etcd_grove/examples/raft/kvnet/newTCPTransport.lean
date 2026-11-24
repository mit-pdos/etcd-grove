/-
The proof of `KvNet/Spec/.../kvnet/newTCPTransport.lean` (2026-11-24, G5): `newTransport`, as an
interface value over `*Transport`, a fresh transport of the peer-transport contract (`ptFresh`): its
`start` is `Transport.start` (the net globals its senders need from `net`'s initialization, which
`kvnet`'s implies: `TopPkg.lean`), and then its `Send` is `Transport.Send` (`ptSend`) and its `stop`
is `Transport.stop`, with the stop channel's closer `newTransport` gave (`ptStop`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.newTCPTransport
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.newTransport
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Transport__start
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Transport__Send
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Transport__stop
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.TopPkg

@[expose] public section

set_option linter.iris.style.nameCheck false

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
variable [net_sem : net.Assumptions] [net_field_sem : net.FieldAssumptions]

theorem newTCPTransport.wp_proof
    (wp_newTransport : newTransport.spec (GF := GF) (hG := hG))
    (wp_start : Transport.start.spec (GF := GF) (hG := hG))
    (wp_Send : Transport.Send.spec (GF := GF) (hG := hG))
    (wp_stop : Transport.stop.spec (GF := GF) (hG := hG)) :
    newTCPTransport.spec (GF := GF) (hG := hG) := by
  intro F γ N id am M sts Htr
  wp_start as ⟨#HM, #Hsts, #Hpr⟩
  try wp_auto
  wp_apply wp_newTransport F id am M sts $$ [$Hpkg $HM $Hpr]
    as %t ⟨#Htid, #Htst, Htnode, #HtPeers, %sc, %γsc, #Hstop, Hpend⟩
  try wp_auto
  iapply HΦ
  unfold ptFresh
  iexists (⟨go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Transport.ty, #t⟩ :
    GoInterfaceOk)
  isplitr
  · ipureintro; rfl
  iintro %n %Φ' #Hpkg' #HisNode HΦ'
  ihave ⟨#Hnet, -⟩ := kvnet_pkg_deps $$ Hpkg'
  ihave #Hg := connGlobals_of_net $$ Hnet
  iunfold raft_kvcheck.connGlobals at Hg
  icases Hg with ⟨%eof, %ed, %et, -, #Hed, #Het⟩
  wp_apply wp_start F t γ N id n sts et ed
    $$ [$Hpkg' $Htid $Htst $Htnode $Hsts $HtPeers $HisNode $Hed $Het] as #Htc
  · isplitr
    · ipureintro; exact Htr
    iexists sc, γsc
    iexact Hstop
  iapply HΦ'
  unfold ptRunning
  isplitr
  · unfold ptSend
    iexists (⟨go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Transport.ty, #t⟩ :
      GoInterfaceOk)
    isplitr
    · ipureintro; rfl
    iintro !> %msl %dqs %ms %Φs !> ⟨Hpk, Hsl, Hms⟩ HΦs
    iapply wp_Send F t γ N id n msl dqs ms $$ [$Hpk $Htc $HtPeers $Hsl $Hms]
    iexact HΦs
  · unfold ptStop
    iexists (⟨go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Transport.ty, #t⟩ :
      GoInterfaceOk)
    isplitr
    · ipureintro; rfl
    iintro %Φs HΦs
    iapply wp_stop t sc γsc $$ [$Hpkg' $Hstop $Hpend]
    inext
    iintro -
    iexact HΦs

end proof

end raft_kvnet
end EtcdGrove
end Perennial
