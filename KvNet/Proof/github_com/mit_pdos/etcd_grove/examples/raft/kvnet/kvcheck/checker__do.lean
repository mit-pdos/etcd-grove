/-
The proof of `KvNet/Spec/.../kvcheck/checker__do.lean`: a fresh id (`fresh`), the caller's minting
law (the operation's fact, persistent), `EncodeOp`'s bytes (frozen), then a loop of `request`s at
random members (`randomMember`) whose `ReqPropose` payload carries the fact, until one answers: the
answer's fact (`ansOk`, a step later) with a later credit of the loop's steps.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker__do
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker__fresh
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker__randomMember
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker__request
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.EncodeOp

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open Iris Iris.BI Iris.ProofMode Net raft_kvnet raft_kvreconf

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF] [NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Assumptions]
variable [field_sem : net.FieldAssumptions]

theorem checker.do.wp_proof (wp_fresh : checker.fresh.spec (GF := GF) (hG := hG))
    (wp_EncodeOp : raft_kvnet.EncodeOp.spec (GF := GF) (hG := hG))
    (wp_randomMember : checker.randomMember.spec (GF := GF) (hG := hG))
    (wp_request : checker.request.spec (GF := GF) (hG := hG)) :
    checker.do.spec (GF := GF) (hG := hG) := by
  intro F c γ ls kind key val Hk Hv
  wp_start as ⟨#Hc, Hmint⟩
  ihave #Hc0 := Hc
  iunfold isCheckerP at Hc0
  icases Hc0 with ⟨#Hck, %Hls, -, -⟩
  wp_auto
  wp_apply wp_fresh c γ ls false
    (c.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker, go!"nextOp"]) rfl $$ [$Hpkg $Hck] as %n Hn
  wp_apply wp_EncodeOp n kind key val Hk Hv as %op ⟨Hops, -⟩
  imod Hmint $$ %n Hn with #Hok
  imod ownSlice_persist op _ _ $$ Hops with #Hops
  have Hlen : ((encodeOp n kind key val).length : Int) + 17 < 2 ^ 63 := by
    rw [encodeOp_length]; omega
  try wp_auto
  ihave HI : iprop(True) $$ []
  · itrivial
  wp_for HI
  try wp_auto
  wp_apply wp_randomMember c γ ls Hls.1 $$ [$Hpkg $Hck] as %id %Hid
  wp_apply wp_request F c γ ls id (W8 1) op (encodeOp n kind key val) DFrac.discard Hid.1 Hid.2 Hlen
    $$ [$Hpkg $Hc $Hops] as %b %ok ⟨-, Hpost⟩
  · rw [reqOk_propose]; iexact Hok
  icases Hpost with (%Hok1 | ⟨%b', %Hok1, Hb, Ha⟩)
  · subst Hok1
    wp_auto
    wp_for_post
    iframe
  · subst Hok1
    wp_auto_lc 1
    rw [ansOk_propose]
    imod lc_fupd_elim_later $$ Hlc1 Ha with #Ha
    wp_apply wp_bytes_to_string $$ Hb with Hb
    try wp_auto
    wp_for_post
    iapply HΦ
    iexists n
    iexact Ha

end proof

end raft_kvcheck
end EtcdGrove
end Perennial
