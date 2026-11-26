/-
The proof of `KvRaft/Spec/.../kvcheck/checker__do.lean` (kvdurable's `Cluster.do` over the wire): a
fresh id (`fresh`), whose law mints the operation's datum at the store's op counter under the
checker's lock (`kd_mint`, with a later credit taken before), its slot holding the caller's update;
`EncodeOp`'s bytes (frozen), then a loop of `request`s at random members (`randomMember`) whose
`ReqPropose` payload carries the minted datum, until one answers: the answer's fact (`waitP`, a step
later) collects the result from the slot (`kd_collect`, under two laters: three credits of the
answer's steps).
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker__do
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker__fresh
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker__randomMember
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker__request
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.EncodeOp
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.StoreDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open raft_kvreconf (encodeOp encodeOp_length kvNext)
open Iris Iris.BI Iris.ProofMode Net kvraft

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Assumptions]
variable [go.IntoValInj GoString]
variable [kvraft_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

theorem checker.do.wp_proof (wp_fresh : checker.fresh.spec (GF := GF) (hG := hG))
    (wp_EncodeOp : kvraft.EncodeOp.spec (GF := GF) (hG := hG))
    (wp_randomMember : checker.randomMember.spec (GF := GF) (hG := hG))
    (wp_request : checker.request.spec (GF := GF) (hG := hG)) :
    checker.do.spec (GF := GF) (hG := hG) := by
  intro γ cf c ls kind key val Ψ Hk Hv
  wp_start as ⟨#Hc, #Hinv, Hau⟩
  ihave #Hc0 := Hc
  iunfold isCheckerP at Hc0
  icases Hc0 with ⟨#Hck, %Hls, -, -⟩
  wp_auto_lc 3
  have Hk64 : (key.length : Int) < 2 ^ 64 := by omega
  -- the minting law: under the lock, the op counter's next id mints the datum and its slot
  wp_apply wp_fresh c (kvCnt γ ls.length) ls false
    (c.[github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker, go!"nextOp"])
    (fun n => iprop(∃ γp : GName × GName, encodeOp n kind key val ↪[γ.r.ops]□ γp ∗
      savedPredOwn γp.1 DFrac.discard Ψ ∗ token γp.2)) rfl
    $$ [$Hpkg $Hck Hlc1 Hau] as %n ⟨%γp, #Hop, #Hsp, Htok⟩
  · iintro %a %Ha Hopn
    unfold kvCnt
    simp only [Bool.false_eq_true, ↓reduceIte]
    ihave Hau : opAu γ (kvNext kind key val) key Ψ $$ [Hau]
    · unfold opAu; iexact Hau
    imod kd_mint γ a kind key val Ψ ⊤ CoPset.subseteq_top Ha Hk64 $$ Hinv Hopn Hlc1 Hau
      with ⟨Hopn, %γp, #Hop, #Hsp, Htok⟩
    imodintro
    iframe Hopn
    iexists γp
    iframe Hop Hsp Htok
  wp_apply wp_EncodeOp n kind key val Hk Hv as %op ⟨Hops, -⟩
  imod ownSlice_persist op _ _ $$ Hops with #Hops
  have Hlen : ((encodeOp n kind key val).length : Int) + 17 < 2 ^ 63 := by
    rw [encodeOp_length]; omega
  try wp_auto
  ihave HI : iprop(token γp.2 ∗ £ 1 ∗ £ 1) $$ [Htok Hlc2 Hlc3]
  · iframe Htok Hlc2 Hlc3
  wp_for HI
  try wp_auto
  wp_apply wp_randomMember c (kvCnt γ ls.length) ls Hls.1 $$ [$Hpkg $Hck] as %id %Hid
  wp_apply wp_request (kvFacts γ cf) c (kvCnt γ ls.length) ls id (W8 1) op (encodeOp n kind key val)
    DFrac.discard Hid.1 Hid.2 Hlen $$ [$Hpkg $Hc $Hops] as %b %ok ⟨-, Hpost⟩
  · rw [reqOk_propose]
    simp only [kvFacts]
    iexists γp
    iexact Hop
  icases Hpost with (%Hok1 | ⟨%b', %Hok1, Hb, Ha⟩)
  · subst Hok1
    wp_auto
    wp_for_post
    iframe
  · subst Hok1
    wp_auto_lc 1
    rw [ansOk_propose]
    imod lc_fupd_elim_later $$ Hlc1 Ha with #Ha
    simp only [kvFacts]
    icases HI with ⟨Htok, Hlc2, Hlc3⟩
    imod kd_collect γ _ γp Ψ b' ⊤ CoPset.subseteq_top $$ Hinv Hop Hsp Htok Ha with HQ
    imod lc_fupd_elim_later $$ Hlc2 HQ with HQ
    imod lc_fupd_elim_later $$ Hlc3 HQ with HQ
    wp_apply wp_bytes_to_string $$ Hb with Hb
    try wp_auto
    wp_for_post
    iapply HΦ
    iexact HQ

end proof

end raft_kvcheck
end EtcdGrove
end Perennial
