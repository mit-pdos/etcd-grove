/-
The proof of `KvNet/Spec/.../kvnet/Node__serve.lean`: the hello byte (`readFull` into a one-byte
array, the reader's token `recvTokL`), then the dispatch.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Node__serve
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Node__serveClient
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Transport__servePeer
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.readFull
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.closeAfter
public import KvNet.Spec.net.Conn__Close

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
variable [package_sem' : net.Assumptions]

theorem Node.serve.wp_proof (F : KvFacts GF) (rep : Loc → w64 → IProp GF)
    (cf : GoInterface → List w8 → IProp GF)
    (wp_serveClient : Node.serveClient.spec (GF := GF) (hG := hG) F rep cf)
    (wp_servePeer : Transport.servePeer.spec (GF := GF) (hG := hG))
    (wp_readFull : readFull.spec (GF := GF) (hG := hG))
    (wp_closeAfter : closeAfter.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG)) :
    Node.serve.spec (GF := GF) (hG := hG) F rep cf := by
  intro nd γ N id n c cn a eof ed
  wp_start as ⟨#Hnd, #Hcl, #Hc, #Heof, #Hed, #Hcc, Hce⟩
  unfold connEnd
  icases Hce with ⟨HW, HR⟩
  ihave HR := recvTok_L _ _ _ _ $$ HR
  icases recvTokL_connIs _ _ _ _ $$ HR with ⟨HR, #Hci⟩
  ihave #Hca := cAcc_of_connIs cn true $$ Hci
  ihave #Hc' := Hc
  iunfold net.isConn at Hc'
  icases Hc' with ⟨%tc, %la, %ra, %Hct, #Hcat⟩
  subst Hct
  try wp_auto
  wp_apply wp_closeAfter _ cn true a _ iprop(True) $$ [] as %disarm #Hdis
  · iframe Hc
    isplitl []
    · itrivial
    imodintro
    iintro -
    iunfold cAcc at Hca
    iexact Hca
  try wp_auto
  ihave Hh := slice_array (GF := GF) hello_ptr _ _ (by decide) $$ hello
  rw [show (zero_val (GoArray w8 1)).arr = [W8 0] from rfl]
  simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
    show W64 1 - W64 0 = W64 1 from rfl]
  wp_apply wp_readFull _ cn true a _ [W8 0]
      (fun got => recvTokL cn true (kvP F id) ([] ++ got)) eof ed
    $$ [HR Hh] as %ok ⟨%got, %bs', HR, Hh, %Hgot⟩
  · iframe Hc Heof Hed Hh
    isplitl [HR]
    · rw [List.append_nil]; iexact HR
    ihave #Hacc := rAcc_of_recvTokL cn true (kvP F id) []
    iunfold rAcc at Hacc
    iexact Hacc
  try wp_auto
  wp_bind (App (Val #disarm) (Val #()))
  iapply Hdis
  iintro %inTime -
  cases inTime
  · try wp_auto
    wp_apply wp_Close tc cn true a la ra (fun _ => iprop(True)) $$ [] as %err' -
    · iframe Hcat
      iunfold cAcc at Hca
      iexact Hca
    try wp_auto
    iapply HΦ
    itrivial
  cases ok
  · try wp_auto
    wp_apply wp_Close tc cn true a la ra (fun _ => iprop(True)) $$ [] as %err' -
    · iframe Hcat
      iunfold cAcc at Hca
      iexact Hca
    try wp_auto
    iapply HΦ
    itrivial
  obtain ⟨Hbl, -, Hg⟩ := Hgot
  have Hg := Hg rfl
  subst Hg
  obtain ⟨x, rfl⟩ : ∃ x, got = [x] := by
    match got, Hbl with
    | [x], _ => exact ⟨x, rfl⟩
  try wp_auto
  rw [show arrayIndexRef w8 (sint.Z (W64 0)) hello_ptr =
    sliceIndexRef w8 (sint.Z (W64 0)) (slice.mk hello_ptr (W64 1) (W64 1)) from rfl]
  wp_apply wp_load_slice_index _ (sint.Z (W64 0)) [x] (DFrac.own 1) x (by decide) $$ [$Hh] as Hh
  · ipureintro; rfl
  try wp_auto
  ihave #Hnd' := Hnd
  iunfold isNodeS at Hnd'
  icases Hnd' with ⟨%r, %t, %sp, #Hr, #Ht, #Hsp, #Hs, #Hrn, #Hrep, #Htc⟩
  rw [List.nil_append] at *
  wp_if_destruct
  · -- a peer
    try wp_auto
    wp_apply wp_servePeer F t γ N id n _ cn a eof ed $$ [$Hpkg $Htc $Hc $Heof $Hed $Hcc HR]
    · unfold helloPeerB; iexact HR
    try wp_auto
    iapply HΦ
    itrivial
  wp_if_destruct
  · -- a client
    try wp_auto
    wp_apply wp_serveClient nd γ N id n _ cn a eof ed $$ [$Hpkg $Hnd $Hcl $Hc $Heof $Hed $Hcc HR $HW]
    · unfold helloClientB; iexact HR
    try wp_auto
    iapply HΦ
    itrivial
  try wp_auto
  wp_apply wp_Close tc cn true a la ra (fun _ => iprop(True)) $$ [] as %err' -
  · iframe Hcat
    iunfold cAcc at Hca
    iexact Hca
  try wp_auto
  iapply HΦ
  itrivial

end proof

end raft_kvnet
end EtcdGrove
end Perennial
