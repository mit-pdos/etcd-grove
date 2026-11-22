/-
The proof of `KvNet/Spec/.../kvnet/Transport__servePeer.lean`: a loop whose invariant is the reader's
token after whole frames (`recvTokL cn true (kvP F id) (helloPeerB :: rawFrames bs)`); each frame
read (`readFrame`, its accessor `rAcc_of_recvTokL`) is a message's encoding with its fact
(`server_peer`, the token's fact a step later: a later credit), read back (`getMsg`), checked to be
for `id`, and stepped (`stepLaw`, `node.Step`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Transport__servePeer
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Stats__add
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.readFrame
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.getMsg
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.withTimeout
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import KvNet.Spec.go_etcd_io.raft.v3.node__Step
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
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]

theorem Transport.servePeer.wp_proof (wp_add : Stats.add.spec (GF := GF) (hG := hG))
    (wp_readFrame : readFrame.spec (GF := GF) (hG := hG))
    (wp_getMsg : getMsg.spec (GF := GF) (hG := hG))
    (wp_withTimeout : withTimeout.spec (GF := GF) (hG := hG))
    (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (wp_Step : node.Step.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG)) :
    Transport.servePeer.spec (GF := GF) (hG := hG) := by
  intro F t γ N id n c cn a eof ed
  wp_start as ⟨#Ht, #Hc, #Heof, #Hed, #Hcc, HR⟩
  ihave #Ht' := Ht
  iunfold isTransportCore at Ht'
  icases Ht' with ⟨%sp, #Hid, #Hnode, #Hstats, #Hs, #Hn, #Hstep, %Htr⟩
  icases recvTokL_connIs _ _ _ _ $$ HR with ⟨HR, #Hci⟩
  ihave #Hca := cAcc_of_connIs cn true $$ Hci
  ihave #Hc' := Hc
  iunfold net.isConn at Hc'
  icases Hc' with ⟨%tc, %la, %ra, %Hct, #Hcat⟩
  subst Hct
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  try wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  ihave HI : (∃ (bs : List (List w8)),
      "HR" ∷ recvTokL cn true (kvP F id) (helloPeerB :: rawFrames bs) ∗
      "%Hbs" ∷ ⌜∀ x ∈ bs, x.length ≤ 2 ^ 26⌝ : IProp GF) $$ [HR]
  · iexists []
    simp only [rawFrames, List.map_nil, List.flatten_nil]
    iframe HR
    ipureintro; simp
  wp_for HI
  try simp only [decide_true, ↓reduceIte]
  wp_apply wp_readFrame _ cn true a
      (fun got => recvTokL cn true (kvP F id) ((helloPeerB :: rawFrames bs) ++ got)) eof ed
    $$ [HR] as %b %ok ⟨%got, HR, Hans⟩
  · iframe Hc Heof Hed
    isplitl [HR]
    · rw [List.append_nil]; iexact HR
    ihave #Hacc := rAcc_of_recvTokL cn true (kvP F id) (helloPeerB :: rawFrames bs)
    iunfold rAcc at Hacc
    iexact Hacc
  icases Hans with (%Hf | ⟨%l, %Hl, Hb⟩)
  · -- no frame: the connection is done
    subst Hf
    try wp_auto
    wp_for_post
    wp_apply wp_Close tc cn true a la ra (fun _ => iprop(True)) $$ [] as %err' -
    · iframe Hcat
      iunfold cAcc at Hca
      iexact Hca
    try wp_auto
    iapply HΦ
    itrivial
  obtain ⟨rfl, rfl, Hl26⟩ := Hl
  -- the frame: a message's encoding, with its fact (a step later)
  wp_auto_lc 1
  ihave HR := recvTokL_later _ _ _ _ $$ HR
  imod lc_fupd_elim_later $$ Hlc1 HR with HR
  icases server_peer F id cn bs l (fun x hx => by have := Hbs x hx; omega) (by omega) $$ HR
    with ⟨HR, %src, %st, %Hst, #Hmsg⟩
  subst Hst
  ihave %Hwf := F.msgOk_wf src st $$ Hmsg
  wp_apply wp_getMsg b st Hwf $$ [$Hpkg $Hb] as %ml Hm
  try wp_auto
  wp_apply wp_GetTo.1 ml _ _ _ _ $$ [$Hpb $Hm] as Hm
  try wp_auto
  wp_if_destruct
  · -- (`wp_if_destruct` substituted the node's id by the message's destination)
    try wp_auto
    wp_apply wp_add sp (W64 18) (by decide) (by decide) $$ [$Hpkg $Hs]
    try wp_auto
    wp_apply wp_withTimeout _ $$ [$Hpkg $Hcc] as %ctx' %cd %cancel ⟨#Hcancel, #Hctx, -⟩
    try wp_auto
    ihave #Hnc : nodeCtx ctx' cd $$ []
    · unfold nodeCtx; iright; iexact Hctx
    iunfold stepLaw at Hstep
    imod Hstep $$ %src %st %ml %rfl Hmsg Hm with Hin
    wp_apply wp_Step n γ N _ ml ctx' cd $$ [$Hraft $Hn $Hnc $Hin] as %err -
    try wp_auto
    wp_apply Hcancel
    try wp_auto
    wp_for_post
    iframe
    iexists bs ++ [encMsg st]
    ihave HR := recvTok_L _ _ _ _ $$ HR
    simp only [rawFrames, List.map_append, List.map_cons, List.map_nil, List.flatten_append,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append] at *
    iframe HR
    ipureintro
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact Hbs x h
    · simp at h; subst h; exact Hl26
  · -- not for this node: the connection ends
    try wp_auto
    wp_apply wp_add sp (W64 22) (by decide) (by decide) $$ [$Hpkg $Hs]
    try wp_auto
    wp_for_post
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
