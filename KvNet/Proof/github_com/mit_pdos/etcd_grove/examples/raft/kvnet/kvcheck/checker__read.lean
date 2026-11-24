/-
The proof of `KvNet/Spec/.../kvcheck/checker__read.lean` (kvdurable's `Cluster.Read` over the wire). The
read's linearization point is the first change of the store's history, from the start of the call on,
after which the key has the returned value; which value that is is known only at the return, so the
call creates a prophecy (`primitive.NewProph`) and resolves it with its answer (gokv's
`trusted_proph.ResolveBytes`). At the start (`kd_read_start`) the read registers a slot with its
caller's update, the history then `H0` (the log `l` of a committed lower bound) and the prophesied
answer. Each attempt takes a fresh sequence number (`fresh`), whose law mints the read at every replica
id after `l` (`kv_mint_reads`), `EncodeRead`'s bytes, a random member (`randomMember`) and a `request`
whose `ReqRead` payload carries the member's minted read; an answer's fact names the attempt's own
number and key (the payload's encoding is injective) and a committed history `L` extending the log the
context was committed after, which is `l` (`readCtxAfter_agree`), so `L` extends `H0`. The resolution
says the answer is the prophesied one, and the result is taken from the slot (`kd_read_take`, under two
laters: three later credits, one for the start and two carried through the attempts).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker__read
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker__fresh
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker__randomMember
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker__request
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.EncodeRead
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.StoreDefs
public import Spec.github_com.mit_pdos.gokv.trusted_proph.ResolveBytes
public import Perennial.Proof.github_com.goose_lang.primitive.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open raft_kvreconf (ReadRec ansOf bootVoters)
open Iris Iris.BI Iris.ProofMode Net raft_kvnet go_etcd_io.raft.v3

/-- A read's payload names its sequence number and key. -/
theorem readPayload_inj {seq seq' : w64} {key key' : List w8}
    (h : u64Le seq ++ putB key = u64Le seq' ++ putB key') : seq = seq' ∧ key = key' := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp [u64Le_length])
  simp only [putB] at h2
  obtain ⟨-, h3⟩ := List.append_inj h2 (by simp [u64Le_length])
  exact ⟨u64Le_inj h1, h3⟩

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Assumptions]
variable [go.IntoValInj GoString]
variable [kvnet_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

theorem checker.read.wp_proof (wp_fresh : checker.fresh.spec (GF := GF) (hG := hG))
    (wp_EncodeRead : raft_kvnet.EncodeRead.spec (GF := GF) (hG := hG))
    (wp_randomMember : checker.randomMember.spec (GF := GF) (hG := hG))
    (wp_request : checker.request.spec (GF := GF) (hG := hG))
    (wp_ResolveBytes : github_com.mit_pdos.gokv.trusted_proph.ResolveBytes.spec (GF := GF)
      (hG := hG)) :
    checker.read.spec (GF := GF) (hG := hG) := by
  intro γ cf c ls key Ψ Hk
  wp_start as ⟨#Hc, #Hinv, Hau⟩
  ihave #Hc0 := Hc
  iunfold isCheckerP at Hc0
  icases Hc0 with ⟨#Hck, %Hls, -, -⟩
  have Hlen : ((u64Le (W64 0) ++ putB key).length : Int) + 17 < 2 ^ 63 := by
    simp [putB, u64Le_length]; omega
  wp_auto_lc 3
  wp_apply github_com.goose_lang.primitive.wp_NewProph as %pvs %p Hp
  -- the read's slot, with its caller's update and the prophesied answer
  imod kd_read_start γ key (ansOf pvs) Ψ ⊤ CoPset.subseteq_top kdMask_sub_rkv
    $$ Hinv Hlc1 Hau with ⟨%γΦ, %H0, Hel, #Hsp, #HH0⟩
  ihave #HH0' := HH0
  iunfold kvLb at HH0'
  icases HH0' with ⟨%l, #Hl, %HH0l⟩
  try wp_auto
  ihave HI : iprop(£ 1 ∗ £ 1 ∗ proph p pvs ∗ γΦ ↪[γ.r.rds] (⟨key, H0, ansOf pvs⟩ : ReadRec))
    $$ [Hlc2 Hlc3 Hp Hel]
  · iframe Hlc2 Hlc3 Hp Hel
  wp_for HI
  try wp_auto
  wp_apply wp_fresh c (kvCnt γ ls.length) ls true
    (c.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker, go!"nextRead"])
    (fun s => iprop([∗list] id ∈ bootVoters ls.length, kvReadMinted γ id s key l)) rfl
    $$ [$Hpkg $Hck] as %seq #Hmint
  · iintro %a %Ha Hcnt
    iapply kv_mint_reads γ ls.length a key l Ha Hk $$ Hinv Hl Hcnt
  wp_apply wp_EncodeRead seq key as %req ⟨Hreq, -⟩
  imod ownSlice_persist req _ _ $$ Hreq with #Hreq
  try wp_auto
  wp_apply wp_randomMember c (kvCnt γ ls.length) ls Hls.1 $$ [$Hpkg $Hck] as %id %Hid
  ihave #Hm := kvReadMinted_at γ ls.length id seq key l Hid.1 Hid.2 $$ Hmint
  iunfold kvReadMinted at Hm
  icases Hm with ⟨#Hok, #Hra⟩
  have Hlen' : ((u64Le seq ++ putB key).length : Int) + 17 < 2 ^ 63 := by
    simp [putB, u64Le_length] at Hlen ⊢; omega
  wp_apply wp_request (kvFacts γ cf) c (kvCnt γ ls.length) ls id (W8 2) req (u64Le seq ++ putB key)
    DFrac.discard Hid.1 Hid.2 Hlen' $$ [$Hpkg $Hc $Hreq] as %b %ok ⟨-, Hpost⟩
  · rw [reqOk_read]
    iexists seq, key
    simp only [kvFacts]
    iframe Hok
  icases Hpost with (%Hok1 | ⟨%b', %Hok1, Hb, Ha⟩)
  · subst Hok1
    try wp_auto
    wp_for_post
    iframe
  · -- the answer `b'`: the prophecy resolved with it, the result from the read's slot
    subst Hok1
    wp_auto_lc 1
    rw [ansOk_read]
    imod lc_fupd_elim_later $$ Hlc1 Ha with #Ha
    icases Ha with ⟨%seq', %key', %Heq, #Ha⟩
    obtain ⟨h1, h2⟩ := readPayload_inj Heq
    subst h1 h2
    simp only [kvFacts]
    iunfold ansReadK at Ha
    icases Ha with ⟨%l0, %L, #Hra0, #HL, %HLv⟩
    ihave %Hl0 := readCtxAfter_agree γ.r.cluster kdRaftN _ l0 l $$ [Hra0 Hra]
    · iframe Hra0 Hra
    subst Hl0
    icases HI with ⟨Hlc2, Hlc3, Hp, Hel⟩
    wp_apply +noauto wp_ResolveBytes p pvs b b' _ $$ [$Hp $Hb] as %pvs' ⟨%Hpvs, -, Hb⟩
    have Hans : (⟨key, H0, ansOf pvs⟩ : ReadRec).ans = some b' := by
      show ansOf pvs = some b'
      rw [Hpvs]; exact kd_ansOf_cons (GF := GF) b' pvs'
    have Hst : H0 <+: L := by rw [HH0l]; exact HLv.1
    imod kd_read_take γ γΦ ⟨key, H0, ansOf pvs⟩ Ψ L b' ⊤ CoPset.subseteq_top Hans Hst HLv.2
      $$ Hinv Hel Hsp HL with HQ
    imod lc_fupd_elim_later $$ Hlc2 HQ with HQ
    imod lc_fupd_elim_later $$ Hlc3 HQ with HQ
    try wp_auto
    wp_apply wp_bytes_to_string $$ Hb with Hb
    try wp_auto
    wp_for_post
    iapply HΦ
    iexact HQ

end proof

end raft_kvcheck
end EtcdGrove
end Perennial
