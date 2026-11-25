/-
The proof of `KvNet/Spec/.../kvnet/listen.lean`: a loop over `net.Listen` (its update from the
address's protocols, `listen_au`) and `time.Sleep`.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.listen
public import KvNet.Spec.net.Listen
public import Perennial.Proof.time.Link
public import KvNet.Proof.net.AtAddr

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [package_sem' : net.Assumptions]

theorem listen.wp_proof (wp_Listen : net.Listen.spec (GF := GF) (hG := hG)) :
    listen.spec (GF := GF) (hG := hG) := by
  intro a P Q
  wp_start as #Ha
  ihave #Ht := addrProto_tok _ _ _ $$ Ha
  ihave %Hok := addrTok_ok _ $$ Ht
  try wp_auto
  wp_for
  ihave #HnetPk : isPkgInit (PROP := IProp GF) pkg_id.net $$ []
  · solve_pkg_init
  wp_apply (net.Listen.spec_addrOk wp_Listen) go!"tcp" net.tcpNet_tcp a $$ [] as %li %err
    (⟨%Herr, %l, #Hli, Hlis, #Hla⟩ | ⟨%x, -, #Herr⟩)
  · (try iframe HnetPk)
    iframe %Hok
    iapply listen_au a P Q $$ Ha
  · subst Herr
    try wp_auto
    wp_for_post
    try wp_auto
    iapply HΦ
    iexists l
    iframe Hli Hlis Hla
  · icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hne
    obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
    try wp_auto
    wp_apply time.wp_Sleep
    try wp_auto
    wp_for_post
    iframe

end proof

end raft_kvnet
end EtcdGrove
end Perennial
