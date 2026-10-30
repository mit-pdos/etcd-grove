/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Replica__request.lean`.
Lean-first (no Rocq counterpart; kvreconf-snapshot-thread, 2026-10-30: `maybeSnapshot`'s proof,
its storage calls moved to the snapshot goroutine's `snapshot`).

Under the lock the applier reads its own halves (`r.index = len ap`, `r.cs = csp`) and encodes its
maps (`encodeState`: `ap`'s state, `kvr_snapOk_of`). With a configuration and an index past
`snapIndex`, the request carries the frozen entry at `len ap` (`frozenTo_at`: `ap`'s last term),
the snapshot certified in the registry (`kvr_snap_make`), the delivered log (`storDL`), the
configuration and the data; with `compact`, the known compaction point, the frozen log and the
node's applied index. A send that cannot complete (a request pending) drops it.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__request
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.BagSend
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Stats__add
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.encodeState
public import Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetVotersOutgoing
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.KvrStorageApi
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.RunFrozen
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.SnapMake
public import Proof.go_etcd_io.raft.v3.Base
public import Proof.go_etcd_io.raft.v3.FrameH

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

theorem Replica.request.wp_proof
    (wp_encodeState : encodeState.spec (GF := GF) (hG := hG)) :
    Replica.request.spec (GF := GF) (hG := hG) := by
  intro γr vs id r n st sts ρ ap csp m mA A D cp snapIndex snap compact Hpre Hcp
  wp_start as ⟨#Hrr, Hown, #Hcpc, #Hfz, #Hdl, #Hal⟩
  ihave #Hrr' := Hrr
  iunfold isReplicaR at Hrr'
  iNamed Hrr'
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  iunfold repOwn at Hown
  iNamed Hown
  have Hlen' : uint.Z (W64 (ap.length : Int)) = (ap.length : Int) := by word
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HR⟩
  try wp_auto
  -- the data: `nil`, or the encoded state with what the snapshot needs
  wp_join iprop(∃ dv : GoSlice, data_ptr ↦ dv ∗ mK ↦$ K ∗ mA ↦${DFrac.own (1 : Qp).half} A ∗
      index_ptr ↦ W64 ap.length ∗ cs_ptr ↦ csp ∗ snapIndex_ptr ↦ snapIndex ∗ r_ptr ↦ r ∗
      r.[RReplica, go!"kv"] ↦ mK ∗ r.[RReplica, go!"applied"] ↦{DFrac.own (1 : Qp).half} mA ∗
      (⌜dv = slice.nil⌝ ∨ ∃ (e : EntryM) (cc : ConfStateM) (bs : List w8),
        memLog ρ.γs (uint.nat (W64 ap.length)) DFrac.discard [e] ∗
        (kvrJ γr.cluster id).SV (memSnapMade (W64 ap.length) e.Term' cc bs) ∗
        (kvrJ γr.cluster id).DL (uint.nat (W64 ap.length)) ∗
        ownCSM csp DFrac.discard cc ∗ dv ↦* bs) ∗
      ⌜dv ≠ slice.nil → uint.nat snapIndex < ap.length⌝)
    with [data HK HA index cs snapIndex r HmK HmA] as ⟨%dv, data, HK, HA, index, cs, snapIndex, r, HmK, HmA, Hdv, %Hdvi⟩
  · iexists zero_val GoSlice; iframe
    isplitl []
    · ileft; ipureintro; rfl
    ipureintro; intro h; exact absurd rfl h
  · wp_if_destruct
    all_goals try wp_auto
    all_goals try wp_if_destruct
    all_goals try wp_auto
    all_goals try (wp_join_done; iexists zero_val GoSlice; iframe
                   isplitl []
                   · ileft; ipureintro; rfl
                   ipureintro; intro h; exact absurd rfl h)
    wp_apply +noauto wp_encodeState mK mA K A (DFrac.own 1) (DFrac.own (1 : Qp).half) $$ [$Hpkg $HK $HA]
      as %sl ⟨HK, HA, %kvs, %ops, Hsl, %Hkv⟩
    -- the snapshot: its entry, its certificate, its delivered log
    have Hlt : uint.nat snapIndex < ap.length := by word
    have HapD : ap.length ≤ D.length := Hpre.length_le
    have Hne : ap ≠ [] := by intro h; subst h; simp at Hlt
    have Hlast : D[ap.length - 1]? = ap.getLast? := by
      rw [List.getLast?_eq_getElem?]
      obtain ⟨t, rfl⟩ := Hpre
      rw [List.getElem?_append_left (by have := List.length_pos_iff.mpr Hne; omega)]
    icases frozenTo_at ρ.γs cp D ap.length (by omega) HapD $$ Hfz with ⟨%e, #He, %Hee⟩
    obtain ⟨x, Hx⟩ : ∃ x, ap.getLast? = some x := Option.isSome_iff_exists.mp (by
      simp [List.getLast?_eq_some_getLast Hne])
    have Hex := Hee x (by rw [Hlast, Hx])
    have Hterm : Option.map LogEntry.term ap.getLast? = some e.Term' := by
      rw [Hx, Hex]; rfl
    have Hdat := kvr_snapOk_of ap K A kvs ops Hkv.1 Hkv.2 Hval HA
    iunfold csOpt at HcsO
    icases HcsO with (%Hnull | #HcsM)
    · exact absurd Hnull.1 (by assumption)
    imod kvr_snap_make γr vs ap (W64 ap.length) e.Term' (encState kvs ops) m c memSnapEmpty (by word)
        (by word) (by word) Hterm Hcsm Hsz Hdat $$ Hcl Hap Hcfg with #Hsv
    try wp_auto
    wp_join_done
    iexists sl
    iframe
    isplitl [Hsl]
    · iright
      iexists e, c, encState kvs ops
      rw [show uint.nat (W64 (ap.length : Int)) = ap.length by word]
      iframe He Hsl HcsM
      isplitl []
      · unfold kvrJ; rw [← memSnapCreated_some memSnapEmpty]; iexact Hsv
      unfold kvrJ storDL; iexists n, kvrRaftN, D; iframe HisNode Hdl; ipureintro; exact HapD
    ipureintro; intro _; exact Hlt
  -- the lock released, the applier's halves back (and a credit for the send)
  wp_apply (lc := 1) sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked HR]
  · inext; iexact HR
  try wp_auto
  ihave Hown : repOwn γr r ap (W64 ap.length) csp m mA A $$ [HmK HK HmA HA Hcs Hidx]
  · unfold repOwn; iexists mK, K, c; iframe; iframe Hap HcsO Hcfg
    ipureintro; exact ⟨Hlen, Hval, HA, Hcsm, Hsz⟩
  -- `req.compact`
  wp_join iprop(∃ cv : w64, req_ptr ↦
      github_com.mit_pdos.etcd_grove.examples.kvreconf.snapReq.mk (W64 ap.length) csp dv cv ∗ index_ptr ↦ W64 ap.length ∗
      ⌜cv = W64 0 ∨ (compact = true ∧ cv = W64 ap.length)⌝) with [req index]
    as ⟨%cv, req, index, %Hcv⟩
  · iexists W64 0; iframe; ipureintro; left; rfl
  · iexists W64 ap.length; iframe; ipureintro; right; exact ⟨trivial, rfl⟩
  -- what the request carries
  ihave HP : snapReqOk γr id ρ.γs
      (github_com.mit_pdos.etcd_grove.examples.kvreconf.snapReq.mk (W64 ap.length) csp dv cv) $$ [Hdv]
  · unfold snapReqOk
    simp only
    iframe Hdv
    rcases Hcv with Hcv | ⟨Hc, Hcv⟩
    · ileft; ipureintro; exact Hcv
    icases Hal with (%Hf | #Hal)
    · rw [Hc] at Hf; cases Hf
    iright
    iexists cp, D
    iframe Hcpc Hfz
    rw [Hcv, show uint.nat (W64 (ap.length : Int)) = ap.length by word]
    iframe Hal
    ipureintro; exact Hpre.length_le
  -- nothing to ask for: `snapIndex`; otherwise the send, dropped if a request is pending
  wp_if_destruct
  all_goals try wp_if_destruct
  all_goals first
    | (iapply HΦ; iframe Hown; ipureintro; left; rfl)
    | (wp_apply_core chan.wp_select_nonblocking
       isplit
       · iapply BigAndL.bigAndL_cons.2
         isplit
         · simp only [chan.nonblockingClausePre]
           iexists RSnapReq, inferInstance, inferInstance, inferInstance, inferInstance, ρ.snc, ρ.sn, _
           isplitr
           · ipureintro; exact ⟨rfl, rfl⟩
           isplitr
           · iapply is_bag_is_chan $$ HsnB
           unfold nonblockingSendAu
           isplit
           · iapply bag_nb_send_au $$ Hlc1 HsnB HP
             inext
             try wp_auto
             try wp_if_destruct
             all_goals
               iapply HΦ
               iframe Hown
               ipureintro
               first | (left; rfl) | (right; exact ⟨rfl, Hdvi (by assumption)⟩)
           · itrivial
         iapply BigAndL.bigAndL_nil.2
         itrivial
       · try wp_auto
         iapply HΦ
         iframe Hown
         ipureintro; left; rfl)

end proof

end kvreconf
end EtcdGrove
end Perennial
