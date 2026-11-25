/-
The proof of `KvRaft/Spec/.../kvraft/Node__serveClient.lean`: the request frame (`readFrame`, the
reader's token after the hello byte), its fact (`server_request`, the token's fact a step later: a
later credit), `getUint64` of the timeout, `Node.handle`, then the reply frame (`writeFrame`, its
accessor `write_acc` of the protocol `kvQ`: `server_reply` / `server_noans`).
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Node__serveClient
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Node__handle
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.readFrame
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.writeFrame
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.closeAfter
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.getUint64
public import KvRaft.Spec.net.Conn__Close

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [package_sem' : net.Assumptions]

theorem Node.serveClient.wp_proof (F : KvFacts GF) (rep : Loc → w64 → IProp GF) (stp : NodeStopper GF)
    (cf : GoInterface → List w8 → IProp GF)
    (wp_handle : Node.handle.spec (GF := GF) (hG := hG) F rep stp cf)
    (wp_readFrame : readFrame.spec (GF := GF) (hG := hG))
    (wp_writeFrame : writeFrame.spec (GF := GF) (hG := hG))
    (wp_closeAfter : closeAfter.spec (GF := GF) (hG := hG))
    (wp_getUint64 : getUint64.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG)) :
    Node.serveClient.spec (GF := GF) (hG := hG) F rep stp cf := by
  intro nd γ N id c cn a eof ed
  wp_start as ⟨#Hnd, #Hcl, #Hc, #Heof, #Hed, #Hcc, HR, HW⟩
  icases recvTokL_connIs _ _ _ _ $$ HR with ⟨HR, #Hci⟩
  ihave #Hca := cAcc_of_connIs cn true $$ Hci
  ihave #Hc' := Hc
  iunfold net.isConn at Hc'
  icases Hc' with ⟨%tc, %la, %ra, %Hct, #Hcat⟩
  subst Hct
  try wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
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
  wp_apply wp_readFrame _ cn true a
      (fun got => recvTokL cn true (kvP F id) ([helloClientB] ++ got)) eof ed
    $$ [HR] as %b %ok ⟨%got, HR, Hans⟩
  · iframe Hc Heof Hed
    isplitl [HR]
    · rw [List.append_nil]; iexact HR
    ihave #Hacc := rAcc_of_recvTokL cn true (kvP F id) [helloClientB]
    iunfold rAcc at Hacc
    iexact Hacc
  try wp_auto
  wp_bind (App (Val #disarm) (Val #()))
  iapply Hdis
  iintro %inTime -
  icases Hans with (%Hf | ⟨%l, %Hl, Hb⟩)
  · subst Hf
    cases inTime
    all_goals
      try wp_auto
      wp_apply wp_Close tc cn true a la ra (fun _ => iprop(True)) $$ [] as %err' -
      · iframe Hcat
        iunfold cAcc at Hca
        iexact Hca
      try wp_auto
      iapply HΦ
      itrivial
  obtain ⟨rfl, rfl, Hl26⟩ := Hl
  ihave %Hbl := ownSlice_len _ _ _ $$ Hb
  cases inTime
  · try wp_auto
    wp_apply wp_Close tc cn true a la ra (fun _ => iprop(True)) $$ [] as %err' -
    · iframe Hcat
      iunfold cAcc at Hca
      iexact Hca
    try wp_auto
    iapply HΦ
    itrivial
  wp_auto_lc 1
  wp_if_destruct
  · try wp_auto
    wp_apply wp_Close tc cn true a la ra (fun _ => iprop(True)) $$ [] as %err' -
    · iframe Hcat
      iunfold cAcc at Hca
      iexact Hca
    try wp_auto
    iapply HΦ
    itrivial
  -- the request frame: its fact (a step later) and the `sentLb` the reply cites
  ihave HR := recvTokL_later _ _ _ _ $$ HR
  imod lc_fupd_elim_later $$ Hlc1 HR with HR
  rw [List.singleton_append]
  icases server_request F id cn l (by omega) $$ HR with ⟨HR, %kind, %tmo, %pl, %Hreq, #Hok, #Hlb⟩
  obtain ⟨rfl, Hrl⟩ := Hreq
  imod ownSlice_persist b _ _ $$ Hb with #Hb
  ihave %Hbw := ownSlice_wf _ _ _ $$ Hb
  have H9 : 9 ≤ sint.Z b.len := by have := Hif; word
  rw [if_pos ⟨by decide, by word, Hbw.2⟩]
  icases (ownSlice_split_all (W64 1) b DFrac.discard _ ⟨by decide, by word⟩).1 $$ Hb
    with ⟨#Hb0, #Hb1⟩
  simp only [reqBytes, show sint.nat (W64 1) = 1 from rfl, List.take_succ_cons, List.take_zero,
    List.drop_succ_cons, List.drop_zero]
  wp_apply wp_getUint64 _ DFrac.discard _ pl $$ [$Hpkg $Hb1] as %rest ⟨#Hrest, -⟩
  try wp_auto
  wp_if_destruct
  all_goals
    try wp_auto
    try simp only [github_com.mit_pdos.etcd_grove.examples.raft.kvraft.maxReqTimeout]
    try wp_auto
    try rw [if_pos ⟨by decide, by word⟩]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ DFrac.discard kind (by decide) $$ [$Hb]
      as #Hbx
    · ipureintro; rfl
    try wp_auto
    wp_apply wp_handle nd γ N id kind rest pl DFrac.discard _ (by simp [reqBytes] at Hrl; omega)
        $$ [$Hpkg $Hnd $Hcl $Hcc $Hrest $Hok]
      as %ans %good Hans
    try wp_auto
    wp_apply wp_slice_literal (V := w8) [W8 0]
    isplitr
    · ipureintro; rfl
    iintro %r0 ⟨Hr0, Hr0c⟩
    rw [show go.arrayLiteralSize [KeyedElement none (ElementExpression go.byte #(W8 0))] = 1 from rfl]
    try wp_auto
    icases Hans with (%Hg | ⟨%v, %Hv, Hv, #Ha⟩)
    · -- no answer: `putB [0]`
      subst Hg
      try wp_auto
      ihave Hresp : (∃ (rs : GoSlice) (xs : List w8), "resp" ∷ resp_ptr ↦ rs ∗ "Hrs" ∷ rs ↦* xs ∗
          "#Hq" ∷ □ kvQ F id cn ([] ++ putB xs) : IProp GF)
        $$ [resp Hr0]
      · iexists _, [W8 0]
        iframe resp Hr0
        imodintro
        rw [List.nil_append]
        iapply server_noans
      icases Hresp with ⟨%rs, %xs, resp, Hrs, #Hq⟩
      try wp_auto
      wp_apply wp_closeAfter _ cn true a _ iprop(True) $$ [] as %disarmW #HdisW
      · iframe Hc
        isplitl []
        · itrivial
        imodintro
        iintro -
        iunfold cAcc at Hca
        iexact Hca
      try wp_auto
      ihave HW := writeP_init cn true (kvQ F id) [] $$ HW
      ihave #Hwacc := write_acc cn true (kvQ F id) [] (putB xs) $$ Hq
      wp_apply wp_writeFrame _ cn true a rs xs (DFrac.own 1) ed
          (fun w res => writeP cn true (kvQ F id) [] w res) $$ [Hrs HW]
        as %okw ⟨%w, %res, -, -, -⟩
      · iframe Hc Hed Hrs HW
        iexact Hwacc
      try wp_auto
      wp_bind (App (Val #disarmW) (Val #()))
      iapply HdisW
      iintro %inT -
      try wp_auto
      wp_apply wp_Close tc cn true a la ra (fun _ => iprop(True)) $$ [] as %err' -
      · iframe Hcat
        iunfold cAcc at Hca
        iexact Hca
      try wp_auto
      iapply HΦ
      itrivial
    · -- the answer `v`: `putB (1 :: v)`
      subst Hv
      ihave %Hvl0 := ownSlice_len $$ Hv
      have Hvl : (v.length : Int) < 2 ^ 63 := by obtain ⟨h1, -⟩ := Hvl0; rw [h1]; word
      try wp_auto
      wp_apply wp_slice_literal (V := w8) [W8 1]
      isplitr
      · ipureintro; rfl
      iintro %r1 ⟨Hr1, Hr1c⟩
      rw [show go.arrayLiteralSize [KeyedElement none (ElementExpression go.byte #(W8 1))] = 1 from rfl]
      try wp_auto
      wp_apply wp_slice_append _ [W8 1] _ v (DFrac.own 1) $$ [$Hr1 $Hr1c $Hv] as %r2 ⟨Hr2, -, -⟩
      try wp_auto
      ihave Hresp : (∃ (rs : GoSlice) (xs : List w8), "resp" ∷ resp_ptr ↦ rs ∗ "Hrs" ∷ rs ↦* xs ∗
          "#Hq" ∷ □ kvQ F id cn ([] ++ putB xs) : IProp GF)
        $$ [resp Hr2]
      · iexists _, [W8 1] ++ v
        iframe resp Hr2
        imodintro
        rw [List.nil_append, List.singleton_append]
        ihave H := server_reply F id cn kind tmo pl v Hrl (by omega)
        iunfold reqBytes at H
        iapply H $$ Hlb Ha
      icases Hresp with ⟨%rs, %xs, resp, Hrs, #Hq⟩
      try wp_auto
      wp_apply wp_closeAfter _ cn true a _ iprop(True) $$ [] as %disarmW #HdisW
      · iframe Hc
        isplitl []
        · itrivial
        imodintro
        iintro -
        iunfold cAcc at Hca
        iexact Hca
      try wp_auto
      ihave HW := writeP_init cn true (kvQ F id) [] $$ HW
      ihave #Hwacc := write_acc cn true (kvQ F id) [] (putB xs) $$ Hq
      wp_apply wp_writeFrame _ cn true a rs xs (DFrac.own 1) ed
          (fun w res => writeP cn true (kvQ F id) [] w res) $$ [Hrs HW]
        as %okw ⟨%w, %res, -, -, -⟩
      · iframe Hc Hed Hrs HW
        iexact Hwacc
      try wp_auto
      wp_bind (App (Val #disarmW) (Val #()))
      iapply HdisW
      iintro %inT -
      try wp_auto
      wp_apply wp_Close tc cn true a la ra (fun _ => iprop(True)) $$ [] as %err' -
      · iframe Hcat
        iunfold cAcc at Hca
        iexact Hca
      try wp_auto
      iapply HΦ
      itrivial
end proof

end kvraft
end EtcdGrove
end Perennial
