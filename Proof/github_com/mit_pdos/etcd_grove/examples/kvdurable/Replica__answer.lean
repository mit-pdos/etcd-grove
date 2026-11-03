/-
kvreconf's proof (the same Go text), ported. Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Replica__answer.lean`. Lean-first (no
Rocq counterpart); kv's `answer` (`Proof/github_com/mit_pdos/etcd_grove/examples/kv/KV__answer.lean`)
under the lock held across the loop.

A read state of a later index is kept. Another, whose context decodes to this replica's read at
`seq` with a waiter in `reads`: the context is the one minted at `(id, seq)` (`kd_read_minted`), and
the waiter gets the read state's read index with the value after `ap` (`readAns`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica__answer
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.decodeReadCtx
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.ApplyLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open kvreconf (kvFold logHist AppliedOk decodeReadCtxB)
open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

set_option maxHeartbeats 1000000 in
theorem Replica.answer.wp_proof (wp_decodeReadCtx : decodeReadCtx.spec (GF := GF) (hG := hG)) :
    Replica.answer.spec (GF := GF) (hG := hG) := by
  intro γ vs dir id r n st sts sq ms γs ph ap idx csp m mA A psl ps dq Hidx
  wp_start as ⟨#Hrep, Hown, Hpsl, #Hps⟩
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  ihave #Hcl' := Hcl
  iunfold kdCluster at Hcl'
  icases Hcl' with ⟨-, -, -, -, #Hinv, -⟩
  iunfold repOwn at Hown
  iNamed Hown
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HR⟩
  iNamed HR
  try wp_auto
  ihave %Hpslen := ownSlice_len $$ Hpsl
  ihave IH : iprop(∃ (k : w64) (rsv : ReadState) (restv : GoSlice) (ps' : List ReadState)
      (Rd' : GMap w64 Loc),
      "i" ∷ i_ptr ↦ k ∗ "rs" ∷ rs_ptr ↦ rsv ∗ "rest" ∷ rest_ptr ↦ restv ∗
      "Hrest" ∷ restv ↦* ps' ∗ "Hcap" ∷ ownSliceCap ReadState restv (DFrac.own 1) ∗
      "Hps'" ∷ ([∗list] v ∈ ps', rsOk γ.r.cluster v) ∗
      "HK" ∷ mK ↦$ K ∗ "Hidx" ∷ r.[KReplica, go!"index"] ↦{DFrac.own (1 : Qp).half} idx ∗
      "HRd" ∷ mR ↦$ Rd' ∗ "Hreads" ∷ ([∗map] s ↦ ch ∈ Rd', readWaiterOk γ id s ch) ∗
      "Hpsl" ∷ psl ↦*{dq} ps ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (ps.length : Int)⌝) $$ [i rs rest HK Hidx HRd Hreads Hpsl]
  · iexists W64 0, _, _, [], Rd
    iframe i rs rest HK Hidx HRd Hreads Hpsl
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    isplitl []
    · iapply (BigSepL.bigSepL_nil).2; iempintro
    ipureintro; exact ⟨by word, by word⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat k < ps.length := by word
    obtain ⟨sv, Hsv⟩ : ∃ sv, ps[sint.nat k]? = some sv := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z psl.len := ⟨Hk.1, by word⟩
    simp only [Hbnd', and_self]
    wp_apply wp_load_slice_index psl (sint.Z k) _ dq sv Hk.1 $$ [Hpsl] as Hpsl
    · iframe Hpsl; ipureintro; exact Hsv
    ihave #Hsv := BigSepL.bigSepL_lookup (Φ := fun _ v => rsOk (GF := GF) γ.r.cluster v) Hsv $$ Hps
    try wp_auto
    wp_if_destruct
    · -- a later index: kept
      wp_apply wp_slice_literal
      try (isplitr; (ipureintro; rfl))
      iintro %sl1 ⟨Hsl1, -⟩
      try wp_auto
      wp_apply wp_slice_append $$ [$Hrest $Hcap $Hsl1] as %rest' ⟨Hrest, Hcap, -⟩
      wp_for_post
      iframe
      iexists k + W64 1, sv, rest', ps' ++ [sv], Rd'
      iframe
      isplitl
      · iapply (BigSepL.bigSepL_singleton (Φ := fun _ v => rsOk (GF := GF) γ.r.cluster v)).2
        iexact Hsv
      ipureintro; exact ⟨by word, by word⟩
    · -- an applied index: answered, if it is this replica's waiting read
      have Hle : uint.Z sv.Index' ≤ (ap.length : Int) := by word
      iunfold rsOk at Hsv
      icases Hsv with ⟨%cx, #Hcx, #Hok⟩
      wp_apply wp_decodeReadCtx sv.RequestCtx' cx DFrac.discard $$ [$Hcx]
      iintro -
      cases Hdec : decodeReadCtxB cx with
      | none =>
        simp only [decodeReadCtxRet, Hdec]
        try wp_auto
        wp_for_post
        iframe
        iexists k + W64 1, sv, restv, ps', Rd'
        iframe
        ipureintro; exact ⟨by word, by word⟩
      | some x =>
        obtain ⟨rep, sq, key⟩ := x
        simp only [decodeReadCtxRet, Hdec]
        try wp_auto
        wp_if_destruct
        · -- this replica's read
          have Hrep : rep = id := by
            by_cases h : rep = id
            · exact h
            · exfalso; simp_all
          subst Hrep
          try wp_auto
          wp_apply wp_map_lookup2 go.uint64 (go.GoType.ChannelType go.ChanDir.sendrecv go.string)
            mR Rd' sq (DFrac.own 1) $$ [$HRd] as HRd
          cases HRs : Rd' !! sq with
          | none =>
            simp only [Option.getD_none, Option.isSome_none, decide_false, Bool.false_eq_true]
            try wp_auto
            wp_for_post
            iframe
            iexists k + W64 1, sv, restv, ps', Rd'
            iframe
            ipureintro; exact ⟨by word, by word⟩
          | some ch =>
            simp only [Option.getD_some, Option.isSome_some, _root_.decide_true]
            try wp_auto
            wp_apply wp_mapDelete mR Rd' sq go.uint64
              (go.GoType.ChannelType go.ChanDir.sendrecv go.string) $$ [$HRd] as HRd
            icases (BigSepM.bigSepM_delete (Φ := fun s ch => readWaiterOk (GF := GF) γ rep s ch)
              HRs).1 $$ Hreads with ⟨Hw, Hreads⟩
            iunfold readWaiterOk at Hw
            icases Hw with ⟨%c0, %γh, #Hmint, #Hho, Hprod⟩
            -- the waiter's context is the read state's: both are minted at `(id, sq)`
            imod kd_read_minted γ cx c0 sv.Index' rep sq key ⊤ (fun _ _ => CoPset.mem_full) Hdec
              $$ Hinv Hok Hmint with %Hc0
            subst Hc0
            try wp_auto
            wp_apply wp_map_lookup1 go.string go.string mK K key (DFrac.own 1) $$ [$HK] as HK
            wp_apply wp_handoff_send (t := go.string) γh ch (readAns γ c0) iprop(True)
              iprop(False) ((K !! key).getD (zero_val GoString)) $$ [$Hho $Hprod]
            · isplitl
              · unfold readAns
                iexists sv.Index', ap, key
                iframe Hok Hap
                ipureintro
                exact ⟨Hle, ⟨rep, sq, Hdec⟩, Hval key⟩
              · itrivial
            iintro -
            try wp_auto
            wp_for_post
            iframe
            iexists k + W64 1, sv, restv, ps', GMap.delete sq Rd'
            iframe
            ipureintro; exact ⟨by word, by word⟩
        · -- another replica's (or no read)
          wp_for_post
          iframe
          iexists k + W64 1, sv, restv, ps', Rd'
          iframe
          ipureintro; exact ⟨by word, by word⟩
  · try wp_auto
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hrep HmW HW Hwaiters HmR HRd Hreads]
    · inext
      unfold lockInv
      iexists mW, W, mR, Rd'
      iframe
    try wp_auto
    iapply HΦ
    iframe Hrest Hcap Hps'
    unfold repOwn
    iexists mK, K, c
    iframe
    iframe Hap HcsO Hcfg
    ipureintro; exact ⟨Hlen, Hval, HA, Hcsm, Hsz⟩

end proof

end kvdurable
end EtcdGrove
end Perennial
