/-
kvreconf's proof (the same Go text), ported. Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Replica__request.lean`.
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

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica__request
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.DefsLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.BagSend
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Stats__add
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.encodeState
public import Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetVotersOutgoing
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.RunFrozen
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.SnapMake
public import Proof.go_etcd_io.raft.v3.Base
public import Proof.go_etcd_io.raft.v3.FrameH

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open kvreconf (kvSnapOk)
open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

theorem Replica.request.wp_proof
    (wp_encodeState : encodeState.spec (GF := GF) (hG := hG)) :
    Replica.request.spec (GF := GF) (hG := hG) := by
  intro γ vs dir id r n st sts sq ρ ap csp m mA A D cp snapIndex bound snap Hpre Hcp
  wp_start as ⟨#Hrr, Hown, #Hcpc, #Hfz0, #Hdl, #Hcl', #Hal⟩
  ihave #Hfz : kvreconf.frozenTo ρ.γs cp D $$ []
  · unfold kvreconf.frozenTo; iexact Hfz0
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
      r.[KReplica, go!"kv"] ↦ mK ∗ r.[KReplica, go!"applied"] ↦{DFrac.own (1 : Qp).half} mA ∗
      (⌜dv = slice.nil⌝ ∨ ∃ (e : EntryM) (cc : ConfStateM) (bs : List w8),
        memLog ρ.γs (uint.nat (W64 ap.length)) DFrac.discard [e] ∗
        (kdJ γ.r.cluster ρ.key).SV (memSnapMade (W64 ap.length) e.Term' cc bs) ∗
        (kdJ γ.r.cluster ρ.key).DL (uint.nat (W64 ap.length)) ∗
        kdSnapCert γ (memSnapMade (W64 ap.length) e.Term' cc bs) ∗
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
    icases kvreconf.frozenTo_at ρ.γs cp D ap.length (by omega) HapD $$ Hfz with ⟨%e, #He, %Hee⟩
    obtain ⟨x, Hx⟩ : ∃ x, ap.getLast? = some x := Option.isSome_iff_exists.mp (by
      simp [List.getLast?_eq_some_getLast Hne])
    have Hex := Hee x (by rw [Hlast, Hx])
    have Hterm : Option.map LogEntry.term ap.getLast? = some e.Term' := by
      rw [Hx, Hex]; rfl
    have Hdat := kvreconf.kvr_snapOk_of ap K A kvs ops (KVsOf_eq _ _ Hkv.1) (KVsOf_eq _ _ Hkv.2) Hval HA
    rw [← encState_eq] at Hdat
    iunfold csOpt at HcsO
    icases HcsO with (%Hnull | #HcsM)
    · exact absurd Hnull.1 (by assumption)
    imod kd_snap_make γ vs ap (W64 ap.length) e.Term' (encState kvs ops) m c memSnapEmpty (by word)
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
      · unfold kdJ; rw [← memSnapCreated_some memSnapEmpty]; iexact Hsv
      isplitl []
      · unfold kdJ; iapply nodeCommitLb_mono γ.r.cluster ρ.key D.length _ HapD $$ Hcl'
      unfold kdSnapCert
      iright
      isplitl []
      · rw [← memSnapCreated_some memSnapEmpty]; iexact Hsv
      iexists ap, m
      iframe Hap Hcfg
      ipureintro
      simp only [memSnapMade]
      exact ⟨by word, Hdat, Hcsm, Hsz⟩
    ipureintro; intro _; exact Hlt
  -- the lock released, the applier's halves back (and a credit for the send)
  wp_apply (lc := 1) sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked HR]
  · inext; iexact HR
  try wp_auto
  ihave Hown : repOwn γ r ap (W64 ap.length) csp m mA A $$ [HmK HK HmA HA Hcs Hidx]
  · unfold repOwn; iexists mK, K, c; iframe; iframe Hap HcsO Hcfg
    ipureintro; exact ⟨Hlen, Hval, HA, Hcsm, Hsz⟩
  -- `req.compact`
  wp_join iprop(∃ cv : w64, req_ptr ↦
      github_com.mit_pdos.etcd_grove.examples.kvdurable.snapReq.mk (W64 ap.length) csp dv cv ∗ index_ptr ↦ W64 ap.length ∗
      ⌜uint.nat cv ≤ uint.nat bound ∧ uint.nat cv ≤ ap.length ∧ (bound = W64 0 → cv = W64 0)⌝)
    with [req index]
    as ⟨%cv, req, index, %Hcv⟩
  · iexists W64 ap.length; iframe; ipureintro
    exact ⟨by word, by word, fun h => by subst h; word⟩
  · iexists bound; iframe; ipureintro
    exact ⟨Nat.le_refl _, by word, fun h => h⟩
  -- what the request carries
  ihave HP : snapReqOk γ ρ.key ρ.γs
      (github_com.mit_pdos.etcd_grove.examples.kvdurable.snapReq.mk (W64 ap.length) csp dv cv) $$ [Hdv]
  · unfold snapReqOk
    simp only
    iframe Hdv
    icases Hal with (%Hf | #Hal)
    · ileft; ipureintro; exact Hcv.2.2 Hf
    by_cases Hc0 : cv = W64 0
    · ileft; ipureintro; exact Hc0
    iright
    iexists cp, D
    iframe Hcpc Hfz0
    isplitr
    · ipureintro; have := Hpre.length_le; omega
    iapply nodeAppliedLb_mono γ.r.cluster ρ.key _ _ Hcv.1 $$ Hal
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
           iexists KSnapReq, inferInstance, inferInstance, inferInstance, inferInstance, ρ.snc, ρ.sn, _
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

end kvdurable
end EtcdGrove
end Perennial
