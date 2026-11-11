/- Lean-first (no Rocq counterpart). The proof of `stream.recvOne` (Probe, proved).

Under `s.mu`, the poll's bound `n` is `regs_sentLb`'s (at least every registration's `k`); the
non-blocking receive (`wsChan_recv.law`'s second form) either gives a response, checked by
`receive` under the lock, or the channel closed, or (the default) `n ≤ |rs|`, so every watcher may
be stamped (`stamp_ok`, `watcherOk_stamp`): the loop over `s.order` keeps the lock's watchers'
`[∗map]` unchanged as its invariant. Then a blocking receive without the lock; its response is
checked under the lock again, whose received list agrees with the receiver's half.

The callees in call order: `Chan` (through `shapes.law`), the channel's receives
(`wsChan_recv.law`, the poll's bound from a registration's `wsSentLb` or `wsSentLb_zero.law`),
`receive`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__recvOne
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__receive
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.StreamLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem stream.recvOne.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hrecv : mvcc.api.wsChan_recv.law (GF := GF) (hG := hG))
    (hzero : mvcc.api.wsSentLb_zero.law (GF := GF) (hG := hG))
    (wp_stream_receive : stream.receive.spec (GF := GF) (hG := hG)) :
    stream.recvOne.spec (GF := GF) (hG := hG) := by
  intro T q rs
  haveI : ∀ ws γ ι, Persistent (isMvccWatchStream (GF := GF) ws γ ι) := hpers.2.1
  haveI : ∀ ι n, Persistent (wsSentLb (GF := GF) ι n) := hpers.2.2.1
  haveI := streamCtx_persistent hpers T
  wp_start as ⟨#Hctx0, Hrcv⟩
  ihave Hctx := Hctx0
  iunfold streamCtx at Hctx
  icases Hctx with ⟨Hep, #Fx, #Fm, #Fkv, #Fws, #Fwm, #Hws, #Hinv, #Hmu, Hstop⟩
  iunfold rcvOwn at Hrcv
  icases Hrcv with ⟨Hrd, Hhr, Hwr, Hhalf⟩
  iunfold epCtx at Hep
  icases Hep with ⟨Hrn, Hinc, Hregs⟩
  iunfold rnCtx at Hrn
  icases Hrn with ⟨#Hpkg, #Hmpkg, Hrn⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
  iunfold smuInv at HL
  icases HL with ⟨%rs0, %W, %Hl, %P, HB⟩
  iunfold smuBody at HB
  icases HB with ⟨Hwm, ⟨%osl, %ids, Hord, Hids, Hcap, %Hids⟩, Hevl, Hreg, Hrcv0, #Hlb, %Hknown, Hwats⟩
  ihave %Hrs := ghostVar_agree T.σs.rcv _ _ _ _ $$ Hrcv0 Hhalf
  subst Hrs
  icases regs_sentLb hpers hzero Hl rs0 T.σs.ws W $$ Hwats with ⟨Hwats, %n, #Hn, %Hkn⟩
  ihave %Hsh := hsh.2.2.2 T.ws T.ep.ι.kv T.σs.ws $$ Hws
  obtain ⟨wsty, wsv, hws, -, hCh, -, -, -, -, -⟩ := Hsh
  icases hrecv T.ws T.ep.ι.kv T.σs.ws $$ Hws with ⟨#Hch, #Hrecvb, #Hpoll⟩
  rw [hws]
  (try wp_auto)
  icases (epRd_split T.ep q).1 $$ Hrd with ⟨Hrdr, Hlive, Hkvf⟩
  wp_apply +noauto (hCh T.ep.ι.kv T.σs.ws) $$ [] as %ch' %Hch'
  · iframe #
  subst Hch'
  wp_auto
  wp_bind (App (Val (GoInstruction SelectStmt)) _)
  iapply (chan.wp_select_nonblocking_alt [iprop(⌜n ≤ rs0.length⌝)] _ _ _ _) $$ [] [-] []
  all_goals first | iNamedAccu | skip
  · iapply BigSepL2.bigSepL2_singleton.2
    iintro __CTX
    iNamed __CTX
    simp only [chan.nonblockingAltClausePre]
    iexists go_etcd_io.etcd.server.v3.storage.mvcc.WatchResponse, inferInstance, inferInstance,
      inferInstance, inferInstance, wsChanOf T.σs.ws, wsChanNames T.σs.ws
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact Hch
    iapply Hpoll $$ %rs0 %n Hwr Hn
    isplit
    · iintro %v %ok Hres
      cases ok
      · simp only [Bool.false_eq_true, ↓reduceIte]
        irename Hres => Hwr
        wp_auto
        wp_apply sync.Mutex.wp_Unlock (sF go!"mu" T.s) (smuInv T)
          $$ [$Hmu $Hlocked Hwm Hord Hids Hcap Hevl Hreg Hrcv0 Hwats]
        · iunfold smuInv
          iexists rs0, W, Hl, P
          iunfold smuBody
          iframe
          iframe #
          inext; ipureintro; exact ⟨Hids, Hknown⟩
        (try wp_auto)
        iapply HΦ
        iexists rs0
        iunfold rcvOwn
        iframe
        iapply (epRd_split T.ep q).2
        iframe
      · simp only [↓reduceIte]
        icases Hres with ⟨%r, Hwr, Hv⟩
        wp_auto
        wp_apply (wp_stream_receive T q rs0 r v W Hl P)
          $$ [Hwm Hord Hids Hcap Hevl Hreg Hrcv0 Hwats Hhalf Hwr Hv Hrdr Hlive Hhr] as
          ⟨%Hl2, %P2, HB, Hhalf, Hwr, Hrdr, Hlive, Hhr⟩
        · iframe Hhalf Hwr Hv Hrdr Hlive Hhr
          isplitr
          · iexact Hctx0
          iunfold smuBody
          iframe
          iframe #
          isplitr <;> ipureintro <;> first | exact Hids | exact Hknown
        (try wp_auto)
        wp_apply sync.Mutex.wp_Unlock (sF go!"mu" T.s) (smuInv T) $$ [$Hmu $Hlocked HB]
        · iunfold smuInv
          iexists rs0 ++ [r], W, Hl2, P2
          iexact HB
        (try wp_auto)
        iapply HΦ
        iexists rs0 ++ [r]
        iunfold rcvOwn
        iframe
        iapply (epRd_split T.ep q).2
        iframe
    · iintro Hwr %Hle
      iframe
      ipureintro; exact Hle
  · iintro __CTX Hnr
    iNamed __CTX
    icases (BigSepL.bigSepL_singleton (PROP := IProp GF)).1 $$ Hnr with %Hle
    have Hst := stamp_ok W rs0 n Hkn Hle
    wp_auto
    ihave %Hlen := ownSlice_len $$ Hids
    ihave HI : (∃ (j : w64) (v0 : w64),
        "i" ∷ i_ptr ↦ j ∗ "id" ∷ id_ptr ↦ v0 ∗ "Hids" ∷ osl ↦* ids ∗
        "Hwm" ∷ T.wm ↦$ GMap.fmap Reg.wp W ∗
        "Hwats" ∷ ([∗map] id ↦ x ∈ W, watcherOwn' Hl rs0 T.σs.ws id x) ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z osl.len⌝ : IProp GF) $$ [i id Hids Hwm Hwats]
    · iexists W64 0, _
      iframe
      ipureintro; constructor <;> word
    wp_for HI
    by_cases Hlt : sint.Z j < sint.Z osl.len
    · rw [decide_eq_true Hlt]; simp only [↓reduceIte]
      have hjl : sint.nat j < ids.length := by rw [Hlen.1]; word
      list_elem ids (sint.nat j) as wid
      have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z osl.len := ⟨Hj.1, Hlt⟩
      (try wp_auto)
      (try simp only [hb, _root_.and_self, ↓reduceIte])
      wp_apply wp_load_slice_index osl (sint.Z j) ids (DFrac.own 1) wid Hj.1 $$ [Hids] as Hids
      · iframe; ipureintro; exact Hwid_lookup
      (try wp_auto)
      obtain ⟨x, hx⟩ : ∃ x, W !! wid = some x := by
        have := (Hids.2 wid).1 (List.mem_of_getElem? Hwid_lookup)
        exact Option.isSome_iff_exists.1 this
      wp_apply (wp_map_lookup1 go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty
        watcher.ty.PointerType T.wm (GMap.fmap Reg.wp W) wid (DFrac.own 1)) $$ [$Hwm] as Hwm
      rw [hx]
      simp only [Option.map_some, Option.getD_some]
      icases (BigSepM.bigSepM_lookup_acc
        (Φ := fun (id : w64) (x : Reg) => watcherOwn' (GF := GF) Hl rs0 T.σs.ws id x) (m := W) hx)
        $$ Hwats with ⟨Hw, Hwats⟩
      iunfold watcherOwn' at Hw
      icases Hw with ⟨%wv, Hp, #Hk, #He, #Hlbk, %Hok⟩
      (try wp_auto)
      ispecialize Hwats $$ [Hp]
      · iunfold watcherOwn'
        iexists { wv with stamped' := true }
        iframe Hp
        iframe #
        ipureintro; exact watcherOk_stamp Hl rs0 wid x wv Hok (Hst wid x hx)
      wp_for_post
      iframe
      iexists j + W64 1, wid
      iframe
      ipureintro; constructor <;> word
    · rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock (sF go!"mu" T.s) (smuInv T)
        $$ [$Hmu $Hlocked Hwm Hord Hids Hcap Hevl Hreg Hrcv0 Hwats]
      · iunfold smuInv
        iexists rs0, W, Hl, P
        iunfold smuBody
        iframe
        iframe #
        inext; ipureintro; exact ⟨Hids, Hknown⟩
      (try wp_auto)
      wp_apply +noauto (hCh T.ep.ι.kv T.σs.ws) $$ [] as %ch2 %Hch2
      · iframe #
      subst Hch2
      (try wp_auto)
      wp_bind (App (Val (chan.receive _)) _)
      iapply chan.wp_receive (wsChanOf T.σs.ws) (wsChanNames T.σs.ws) $$ Hch
      iintro -
      iapply Hrecvb $$ Hwr
      iintro %v %ok Hres
      cases ok
      · simp only [Bool.false_eq_true, ↓reduceIte]
        irename Hres => Hwr
        wp_auto
        iapply HΦ
        iexists rs0
        iunfold rcvOwn
        iframe
        iapply (epRd_split T.ep q).2
        iframe
      · simp only [↓reduceIte]
        icases Hres with ⟨%r, Hwr, Hv⟩
        wp_auto
        wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
        iunfold smuInv at HL
        icases HL with ⟨%rs1, %W1, %Hl1, %P1, HB⟩
        iunfold smuBody at HB
        icases HB with ⟨Hwm, Hord, Hevl, Hreg, Hrcv1, #Hlb1, %Hk1, Hwats⟩
        ihave %Hrs1 := ghostVar_agree T.σs.rcv _ _ _ _ $$ Hrcv1 Hhalf
        subst Hrs1
        wp_apply (wp_stream_receive T q rs1 r v W1 Hl1 P1)
          $$ [Hwm Hord Hevl Hreg Hrcv1 Hwats Hhalf Hwr Hv Hrdr Hlive Hhr] as
          ⟨%Hl2, %P2, HB, Hhalf, Hwr, Hrdr, Hlive, Hhr⟩
        · iframe Hhalf Hwr Hv Hrdr Hlive Hhr
          isplitr
          · iexact Hctx0
          iunfold smuBody
          iframe
          iframe #
          ipureintro; exact Hk1
        (try wp_auto)
        wp_apply sync.Mutex.wp_Unlock (sF go!"mu" T.s) (smuInv T) $$ [$Hmu $Hlocked HB]
        · iunfold smuInv
          iexists rs1 ++ [r], W1, Hl2, P2
          iexact HB
        (try wp_auto)
        iapply HΦ
        iexists rs1 ++ [r]
        iunfold rcvOwn
        iframe
        iapply (epRd_split T.ep q).2
        iframe

end proof

end mvccfull
end EtcdGrove
end Perennial
