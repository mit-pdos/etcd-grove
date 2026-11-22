/-
The proof of `KvNet/Spec/.../kvcheck/checker__request.lean`: the replica's address read from
`c.addrs`, `kvnet.Request` called with the protocol's resources (`kv_dial`: the dial update from the
address's protocol; the writes and reads `kvW`/`kvR`), and its answer's fact by `client_reply_L`.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker__request
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Request

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open Iris Iris.BI Iris.ProofMode Net raft_kvnet

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Assumptions]
variable [field_sem : net.FieldAssumptions]

theorem checker.request.wp_proof (wp_Request : Request.spec (GF := GF) (hG := hG)) :
    checker.request.spec (GF := GF) (hG := hG) := by
  intro F c γ ls id kind payload pl dqp H1 H2 Hpl
  wp_start as ⟨#Hc, Hp, #Hr⟩
  iunfold isCheckerP at Hc
  icases Hc with ⟨#Hck, %Hls, #Hap, #Hg⟩
  icases addrsProto_at F ls id H1 H2 $$ Hap with ⟨%a, %Ha, #Hpa⟩
  obtain ⟨Hla, Hok⟩ := Ha
  iunfold isChecker at Hck
  icases Hck with ⟨%sl, #Hsa, #Hsl, -⟩
  iunfold connGlobals at Hg
  icases Hg with ⟨%eof, %ed, %et, #Heof, #Hed, #Het⟩
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  have Hb : 0 ≤ sint.Z (id - W64 1) ∧ sint.Z (id - W64 1) < sint.Z sl.len := by
    have := Hlen.2; constructor <;> word
  rw [ite_eq_left Hb]
  have Hidx : ls[sint.nat (id - W64 1)]? = some a := by
    rw [show sint.nat (id - W64 1) = uint.nat id - 1 by word]; exact Hla
  wp_apply wp_load_slice_index sl _ _ _ a Hb.1 $$ [Hsl] as -
  · iframe Hsl; ipureintro; exact Hidx
  have Hreq : (reqBytes kind (W64 300000000) pl).length < 2 ^ 63 := by
    simp [reqBytes, u64Le_length]; omega
  ihave #HT : ∀ cn, kvP F id cn (helloClientB :: putB (reqBytes kind (W64 300000000) pl)) $$ []
  · iintro %cn
    iapply kvP_req F id cn kind _ pl Hreq $$ Hr
  wp_apply wp_Request a kind (W64 300000000) payload pl dqp (kvW F id) (kvR F id) iprop(True)
      eof ed et Hpl $$ [Hp] as %b %ok ⟨Hp, Hpost⟩
  · iframe Hp Heof Hed Het
    isplitr
    · ipureintro; exact Hok
    iapply kv_dial F id a _ $$ Hpa HT
  try wp_auto
  iapply HΦ
  iframe Hp
  icases Hpost with (⟨%Hok1, %b', %cn, %s, Hb', HW, HR⟩ | ⟨%Hok1, -⟩)
  · iright
    iexists b'
    ihave %Hbl := ownSlice_len _ _ _ $$ Hb'
    iframe Hb'
    isplitr
    · ipureintro; exact Hok1
    unfold kvW kvR
    iapply client_reply_L F id cn kind _ pl b' Hreq (by have := Hbl.1; have := Hbl.2; word) $$ HW HR
  · ileft; ipureintro; exact Hok1

end proof

end raft_kvcheck
end EtcdGrove
end Perennial
