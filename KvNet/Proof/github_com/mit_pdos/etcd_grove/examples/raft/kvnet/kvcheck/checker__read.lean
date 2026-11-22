/-
The proof of `KvNet/Spec/.../kvcheck/checker__read.lean`: a loop whose every attempt takes a fresh
sequence number (`fresh`), `EncodeRead`'s bytes, a random member (`randomMember`), the caller's minting
law at that member, and a `request` whose `ReqRead` payload carries the read context's fact; an
answer's fact names the attempt's own number and key (the payload's encoding is injective).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker__read
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker__fresh
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker__randomMember
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker__request
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.EncodeRead

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open Iris Iris.BI Iris.ProofMode Net raft_kvnet

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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF] [NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Assumptions]
variable [field_sem : net.FieldAssumptions]

theorem checker.read.wp_proof (wp_fresh : checker.fresh.spec (GF := GF) (hG := hG))
    (wp_EncodeRead : raft_kvnet.EncodeRead.spec (GF := GF) (hG := hG))
    (wp_randomMember : checker.randomMember.spec (GF := GF) (hG := hG))
    (wp_request : checker.request.spec (GF := GF) (hG := hG)) :
    checker.read.spec (GF := GF) (hG := hG) := by
  intro F c γ ls key Hk
  wp_start as ⟨#Hc, #Hmint⟩
  ihave #Hc0 := Hc
  iunfold isCheckerP at Hc0
  icases Hc0 with ⟨#Hck, %Hls, -, -⟩
  have Hlen : ((u64Le (W64 0) ++ putB key).length : Int) + 17 < 2 ^ 63 := by
    simp [putB, u64Le_length]; omega
  try wp_auto
  ihave HI : iprop(True) $$ []
  · itrivial
  wp_for HI
  try wp_auto
  wp_apply wp_fresh c γ ls true
    (c.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker, go!"nextRead"]) rfl
    $$ [$Hpkg $Hck] as %seq Hn
  wp_apply wp_EncodeRead seq key as %req ⟨Hreq, -⟩
  imod ownSlice_persist req _ _ $$ Hreq with #Hreq
  try wp_auto
  wp_apply wp_randomMember c γ ls Hls.1 $$ [$Hpkg $Hck] as %id %Hid
  imod Hmint $$ %id %seq %Hid Hn with #Hok
  have Hlen' : ((u64Le seq ++ putB key).length : Int) + 17 < 2 ^ 63 := by
    simp [putB, u64Le_length] at Hlen ⊢; omega
  wp_apply wp_request F c γ ls id (W8 2) req (u64Le seq ++ putB key) DFrac.discard Hid.1 Hid.2 Hlen'
    $$ [$Hpkg $Hc $Hreq] as %b %ok ⟨-, Hpost⟩
  · rw [reqOk_read]
    iexists seq, key
    iframe Hok
    ipureintro; rfl
  icases Hpost with (%Hok1 | ⟨%b', %Hok1, Hb, Ha⟩)
  · subst Hok1
    try wp_auto
    wp_for_post
    iframe
  · subst Hok1
    wp_auto_lc 1
    rw [ansOk_read]
    imod lc_fupd_elim_later $$ Hlc1 Ha with #Ha
    icases Ha with ⟨%seq', %key', %Heq, #Ha⟩
    obtain ⟨h1, h2⟩ := readPayload_inj Heq
    subst h1 h2
    wp_apply wp_bytes_to_string $$ Hb with Hb
    try wp_auto
    wp_for_post
    iapply HΦ
    iexists id, seq
    iexact Ha

end proof

end raft_kvcheck
end EtcdGrove
end Perennial
