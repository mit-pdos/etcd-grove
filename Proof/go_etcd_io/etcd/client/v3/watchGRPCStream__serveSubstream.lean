/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watchGRPCStream__serveSubstream.lean` (the watch slice's
unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__serveSubstream
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__startBufWait
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__recordBufWait
public import Spec.go_etcd_io.etcd.client.v3.watcherStream__resetBufWait
public import Spec.go_etcd_io.etcd.client.v3.WatchResponse__Err

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

namespace client
section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

instance isBlockLogger_persistent' {α : Type} (bl : Loc) (A : α → IProp GF) :
    Persistent (isBlockLogger (GF := GF) bl A) := by
  unfold isBlockLogger; infer_instance

instance bufLogOk_persistent' (ws bl : Loc) : Persistent (bufLogOk (GF := GF) ws bl) := by
  unfold bufLogOk; infer_instance

/-- The `i`th entry of a list ending at `a`, of length `i + 1`. -/
theorem getElem?_of_getLast? {A : Type} {C : List A} {i : Nat} {a : A} (hC : C.length = i + 1)
    (hl : C.getLast? = some a) : C[i]? = some a := by
  rw [List.getLast?_eq_getElem?] at hl
  rw [hC] at hl
  simpa using hl

/-- **Publishing a response** at the producer's position `i` (the cursor's positions `C`, one more
than the responses published, ending at `hiB`): the cursor extended by `hiA`, the contract's
element. -/
theorem publish_elem (V : WEnv GF) (P : WsPrm GF) (C : List w64) (i : Nat)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) (hiB hiA : w64)
    (hC : C.length = i + 1) (hl : C.getLast? = some hiB)
    (hf : v.CompactRevision' = r.compactRev ∧ v.Canceled' = r.canceled ∧ v.Created' = r.created) :
    monoListAuthOwn (GF := GF) P.γ.cur 1 C ∗ eventsAt v.Events' r.events ∗
      watchHdrOwn v.Header' r ∗ rangeWatchRespOk (EM := V.EM) V.pfx P.o P.rev hiB hiA r ∗
      statusErrOk v.closeErr' ⊢
    |==> (monoListAuthOwn P.γ.cur 1 (C ++ [hiA]) ∗
      rangeWatchElem (EM := V.EM) P.γ V.pfx P.o P.rev (i : Int) v) := by
  iintro ⟨Hauth, #Hev, Hhdr, #Hok, #Hse⟩
  imod monoListAuthOwn_update_app (GF := GF) [hiA] $$ Hauth with ⟨Hauth, #Hlb⟩
  have h1 : (C ++ [hiA])[i]? = some hiB := by
    rw [List.getElem?_append_left (by omega)]; exact getElem?_of_getLast? hC hl
  have h2 : (C ++ [hiA])[i + 1]? = some hiA := by
    rw [List.getElem?_append_right (by omega)]; simp [hC]
  ihave #Hi1 := monoListIdxOwn_get (GF := GF) i hiB h1 $$ Hlb
  ihave #Hi2 := monoListIdxOwn_get (GF := GF) (i + 1) hiA h2 $$ Hlb
  imodintro
  iframe Hauth
  unfold rangeWatchElem
  iexists r, hiB, hiA
  simp only [Int.toNat_natCast]
  iframe Hev Hhdr Hi1 Hi2 Hok Hse
  ipureintro; exact hf

/-- **A received response, live** (`recvElem`'s first disjunct): its value, read-only, with its
content and the contract's positions around it. -/
def recvLive (V : WEnv GF) (P : WsPrm GF) (k : Int) (wr : Loc) : IProp GF :=
  iprop(∃ (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) (hiB hiA : w64),
    wr ↦□ v ∗
    ⌜v.Header' ≠ null ∧ v.closeErr' = GoInterface.nil ∧ v.CompactRevision' = r.compactRev ∧
      v.Canceled' = r.canceled ∧ v.Created' = r.created ∧ r.compactRev = W64 0 ∧
      r.canceled = false⌝ ∗
    eventsAt v.Events' r.events ∗ watchHdrOwn v.Header' r ∗
    monoListIdxOwn P.γhi k.toNat hiB ∗ monoListIdxOwn P.γhi (k.toNat + 1) hiA ∗
    rangeWatchRespOk (EM := V.EM) V.pfx P.o P.rev hiB hiA r ∗
    (if k = 0 then
      iprop(⌜r.created = true ∧ r.events = []⌝ ∗
        ∃ rv : w64, wsReqF P.ws go!"rev" ↦{DFrac.own (1 : Qp).half} rv)
    else iprop(⌜r.created = false⌝)))

/-- **A response received while the substream runs is live**: `recvElem`'s other disjunct says
the substream has exited (its exit flag `γx` set, read-only), which its goroutine (holding the
flag, unset) has not. -/
theorem recvElem_live (V : WEnv GF) (P : WsPrm GF) (k : Int) (wr : Loc) :
    dghostVar P.γx (DFrac.own 1) false ∗ recvElem (GF := GF) V P k wr ⊢
      dghostVar P.γx (DFrac.own 1) false ∗ recvLive V P k wr := by
  unfold recvElem
  iintro ⟨Hx, (Hl | #Hd)⟩
  · iframe Hx; unfold recvLive; iexact Hl
  · ihave %H := dghostVar_agree _ _ _ _ _ $$ Hx Hd
    cases H

/-- A live response's location points to it, read-only. -/
theorem recvLive_ptsto (V : WEnv GF) (P : WsPrm GF) (k : Int) (wr : Loc) :
    recvLive (GF := GF) V P k wr ⊢ recvLive V P k wr ∗
      ∃ v : go_etcd_io.etcd.client.v3.WatchResponse, wr ↦□ v := by
  unfold recvLive
  iintro ⟨%v, %r, %hiB, %hiA, #Hv, Hrest⟩
  isplitl [Hrest]
  · iexists v, r, hiB, hiA
    iframe Hv Hrest
  · iexists v; iexact Hv

/-- The two halves of a points-to, joined. -/
theorem ptsto_halves (l : Loc) (v : w64) :
    typedPointsto (GF := GF) l v (DFrac.own (1 : Qp).half) ∗
      typedPointsto (GF := GF) l v (DFrac.own (1 : Qp).half) ⊢
    typedPointsto (GF := GF) l v (DFrac.own 1) := by
  have h := ((fractional_of_dfractional (fun dq => typedPointsto (GF := GF) l v dq)).fractional
    (1 : Qp).half (1 : Qp).half)
  rw [Qp.half_add_half] at h
  exact h.2

/-- The header of a response without events is read-only. -/
theorem watchHdrOwn_nil (h : Loc) (r : RespModel) (he : r.events = []) :
    watchHdrOwn (GF := GF) h r ⊣⊢ hdrAt h r.hdrRev := by
  unfold watchHdrOwn; rw [if_pos he]; exact .rfl

/-- The header of a response with events is owned. -/
theorem watchHdrOwn_cons (h : Loc) (r : RespModel) (he : r.events ≠ []) :
    watchHdrOwn (GF := GF) h r ⊣⊢ iprop(⌜h ≠ null⌝ ∗
      structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦ r.hdrRev) := by
  unfold watchHdrOwn; rw [if_neg he]; exact .rfl

/-- A ghost update before a send's atomic update. -/
theorem bupd_sendAu {V : Type} [Pos.Countable V] [ZeroVal V] (γ : ChanNames) (v : V)
    (Φ : IProp GF) : (|==> sendAu γ v Φ) ⊢ sendAu γ v Φ := by
  unfold sendAu
  iintro H
  imod H
  iexact H

/-- **The buffer's entries**: the responses received at positions `k`, `k + 1`, ... of `recvc`,
not yet published, each with its content. -/
def bufElems (V : WEnv GF) (P : WsPrm GF) (k : Nat) (l : List Loc) : IProp GF :=
  iprop([∗list] i ↦ wr ∈ l, recvLive V P ((k + i : Nat) : Int) wr)

theorem bufElems_nil (V : WEnv GF) (P : WsPrm GF) (k : Nat) :
    ⊢ bufElems (GF := GF) V P k [] := by
  unfold bufElems
  iapply BigSepL.bigSepL_nil.2
  itrivial

theorem bufElems_cons (V : WEnv GF) (P : WsPrm GF) (k : Nat) (wr : Loc) (l : List Loc) :
    bufElems (GF := GF) V P k (wr :: l) ⊣⊢
      recvLive V P (k : Int) wr ∗ bufElems V P (k + 1) l := by
  unfold bufElems
  refine (BigSepL.bigSepL_cons (PROP := IProp GF)
    (Φ := fun i wr => recvLive V P ((k + i : Nat) : Int) wr) (x := wr) (xs := l)).trans ?_
  apply sep_congr
  · simp
  · refine BiEntails.of_eq (BigSepL.bigSepL_eq_of_forall_eq ?_)
    intro i _
    have : k + (i + 1) = k + 1 + i := by omega
    rw [this]

theorem bufElems_snoc (V : WEnv GF) (P : WsPrm GF) (k : Nat) (wr : Loc) (l : List Loc) :
    bufElems (GF := GF) V P k l ∗ recvLive V P ((k + l.length : Nat) : Int) wr ⊢
      bufElems V P k (l ++ [wr]) := by
  unfold bufElems
  iintro ⟨Hl, Hw⟩
  iapply BigSepL.bigSepL_snoc.2
  iframe Hl
  iexact Hw

end lemmas
end client

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

set_option hygiene false in
/-- **The substream's return** (any `return` of the loop, the loop's resources named as in its
invariant): the deferred functions record the buffer's wait, mark the substream closing, close
`donec`, send what it holds on `closingc` (`closingP`) and signal the wait group. -/
local macro "ss_return" : tactic => `(tactic| (
  wp_for_post
  ihave Hrv : iprop(∃ (q : Qp) (rv : w64), wsReqF P.ws go!"rev" ↦{DFrac.own q} rv) $$ [Hrev]
  · icases Hrev with (⟨-, Hrev⟩ | ⟨-, %rv, Hrev⟩)
    · iexists _, _; iexact Hrev
    · iexists 1, rv; iexact Hrev
  icases Hrv with ⟨%q, %rv, Hrv⟩
  wp_apply wp_recordBufWait $$ [Hbl Hbwt Hrv Hbuf] as ⟨Hbl, Hla, %t'', Hbwt⟩
  · iframe Flg Hbl Hblok Hbwt
    unfold wsLogA
    iframe Hrv Hbuf
  imod dghostVar_update true _ _ $$ Hx with Hx
  imod dghostVar_persist _ _ _ $$ Hx with #Hx
  wp_apply wp_broadcast_chan_close $$ [Hdn] as #Hdnd
  · iframe Hdn; imodintro; iexact Hx
  wp_apply wp_bag_send $$ [Hclosing Hretc Hrr Hprod Hauth Hwstok]
  · iframe Hclb
    unfold closingP closingBody
    iframe Hwstok
    iexists P, rcf
    iframe HP Hretc Hclosing
    isplitr
    · ipureintro; rfl
    isplitl [Hprod Hauth]
    · unfold outcProd; iexists sent, C; iframe Hprod Hauth; ipureintro; exact HC.1
    icases Hrr with (⟨%Hr, Hres⟩ | %Hr)
    · iright; iframe Hres; ipureintro; exact Hr.2
    · ileft; ipureintro; exact Hr.2
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold wgDone at Hwg
  wp_apply wp_wgsWg_Done $$ [Hwg] as Htt
  · iexact Hwg
  iapply HΦ
  iexact Htt))

set_option hygiene false in
/-- The end of the first response's handling (`created`), back to the loop's join point. -/
local macro "c2_fin" : tactic => `(tactic| (
  isplitr
  · first | itrivial | (ipureintro; rfl)
  iexists _, _, _
  iframe
  ipureintro
  first | exact ⟨HC.1, HC.2.2⟩ | simp [HC.1]))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem watchGRPCStream.serveSubstream.wp_proof
    (wp_startBufWait : watchGRPCStream.startBufWait.spec (GF := GF) (hG := hG))
    (wp_recordBufWait : watchGRPCStream.recordBufWait.spec (GF := GF) (hG := hG))
    (wp_resetBufWait : watcherStream.resetBufWait.spec (GF := GF) (hG := hG))
    (wp_Err : WatchResponse.Err.spec (GF := GF) (hG := hG)) :
    watchGRPCStream.serveSubstream.spec (GF := GF) (hG := hG) := by
  intro V G callSl P b0 bl t0 rc γrc
  wp_start as ⟨#HG, #HP, Hclosing, Hbuf, Hb0, Hbl, #Hblok, Hbwt, Hrev, Hretc, Hres, Hprod, Hauth,
    Hcons, #Hhi0, #Hrc, Hdn, Hx, Hwg, Hwstok⟩
  ihave #HP' := HP
  iunfold wsIs at HP'
  icases HP' with ⟨#Hro, #Hfoutc, #Hfrecvc, #Hfdonec, #Houtc, #Hrecvc, #Hdonec, #Hctx, #Hretcb,
    %HPws, -⟩
  ihave #HG' := HG
  iunfold isWGS at HG'
  icases HG' with ⟨%Hwgs, -, #Hsf, %Hlg, #Fowner, #Fremote, #FcallOpts, #Fctx, #FctxKey, #Fcancel,
    #Freqc, #Frespc, #Fdonec, #Ferrc, #Fclosingc, #Flg, #HGctx, #HGcancel, #Hreqb, #Herrb, #Hclb,
    #HGdone⟩
  ihave #Hro' := Hro
  iunfold wrRO at Hro'
  icases Hro' with ⟨#Rctx, #Rkey, #Rend, #Rcn, #Rpn, #Rfrag, #Rwbl, #Rflt, #Rflts, #RprevKV⟩
  ihave #HGc := HGctx
  iNamedPrefix HGc "W"
  ihave #HPc := Hctx
  iNamedPrefix HPc "C"
  wp_apply wp_with_defer
  iintro %defer Hdefer
  wp_auto
  ipersist «$v0»
  ipersist «$r0»
  ipersist emptyWr
  ipersist w
  ipersist ws
  ipersist resumec
  ihave IH : iprop(∃ (rcv : List Loc) (sent : List go_etcd_io.etcd.client.v3.WatchResponse)
      (C : List w64) (bufl : List Loc) (b : GoSlice) (rcf : Loc) (nr : w64)
      (t : _root_.Perennial.time.Time) (cl : w64),
      "Hcons" ∷ spscConsumer P.γr rcv ∗
      "Hprod" ∷ spscProducer P.γ.spsc sent ∗ "Hauth" ∷ monoListAuthOwn P.γ.cur 1 C ∗
      "%HC" ∷ ⌜C.length = sent.length + 1 ∧ bufl.length ≤ rcv.length ∧ C.getLast? = some cl⌝ ∗
      "#Hcur" ∷ monoListIdxOwn P.γhi (rcv.length - bufl.length) cl ∗
      "Hbuf" ∷ wsF P.ws go!"buf" ↦ b ∗ "Hb" ∷ sliceOwn b bufl ∗
      "Hbe" ∷ bufElems V P (rcv.length - bufl.length) bufl ∗
      "Hrev" ∷ (⌜rcv = []⌝ ∗ wsReqF P.ws go!"rev" ↦{DFrac.own (1 : Qp).half} P.rev ∨
        ⌜rcv ≠ []⌝ ∗ ∃ rv : w64, wsReqF P.ws go!"rev" ↦ rv) ∗
      "Hretc" ∷ wsReqF P.ws go!"retc" ↦ rcf ∗
      "Hrr" ∷ ((⌜rcv = [] ∧ rcf = P.retc⌝ ∗ retcRes P) ∨ ⌜rcv ≠ [] ∧ rcf = null⌝) ∗
      "Hbwt" ∷ wsF P.ws go!"bufWaitStartTime" ↦ t ∗
      "nextRev" ∷ nextRev_ptr ↦ nr) $$ [Hcons Hprod Hauth Hbuf Hb0 Hrev Hretc Hres Hbwt nextRev]
  · iexists [], [], [P.rev - W64 1], [], b0, P.retc, P.rev, t0, (P.rev - W64 1)
    simp only [named]
    iframe Hcons Hprod Hauth Hbuf Hb0 Hretc Hbwt nextRev
    simp only [List.length_nil, Nat.sub_self]
    iframe Hhi0
    isplitr
    · ipureintro; simp
    isplitr
    · iapply bufElems_nil
    isplitl [Hrev]
    · ileft; iframe Hrev; try (ipureintro; rfl)
    ileft; iframe Hres; try (ipureintro; simp)
  wp_for IH
  iunfold sliceOwn at Hb
  icases Hb with ⟨Hb, Hbcap⟩
  ihave %Hblen := ownSlice_len _ _ _ $$ Hb
  wp_bind (If (Val #(decide (sint.Z (W64 0) < sint.Z b.len))) _ _)
  iapply (wp_wand_r (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
      ∃ (cw oc : Loc) (t' : _root_.Perennial.time.Time), curWr_ptr ↦ cw ∗ outc_ptr ↦ oc ∗
      b ↦* bufl ∗ wsF P.ws go!"buf" ↦ b ∗ wsF P.ws go!"bufWaitStartTime" ↦ t' ∗
      wsF P.ws go!"bufLogger" ↦ bl ∗
      ⌜(bufl = [] ∧ oc = chan.nil ∧ cw = «$r0_ptr») ∨
        (∃ wr0 rest, bufl = wr0 :: rest ∧ oc = P.outc ∧ cw = wr0)⌝)))
  isplitl [curWr outc Hb Hbuf Hbwt Hbl]
  · wp_if_destruct
    · obtain ⟨wr0, rest, hbl⟩ : ∃ wr0 rest, bufl = wr0 :: rest := by
        cases bufl with
        | nil => simp at Hblen; word
        | cons a l => exact ⟨a, l, rfl⟩
      subst hbl
      rw [ite_eq_left_iff.2 (fun h => absurd ⟨by word, Hif⟩ h)]
      wp_apply wp_load_slice_index b (sint.Z (W64 0)) (wr0 :: rest) (DFrac.own 1) wr0 (by word)
        $$ [Hb] as Hb
      · iframe Hb; ipureintro; simp
      wp_apply wp_startBufWait $$ [Hbl Hbwt] as ⟨Hbl, %t', Hbwt⟩
      · iframe Flg Hbl Hblok Hbwt
      isplitr
      · first | itrivial | (ipureintro; rfl)
      iexists wr0, P.outc, t'
      iframe
      ipureintro; right; exact ⟨wr0, rest, rfl, rfl, rfl⟩
    · have hnil : bufl = [] := by
        cases bufl with
        | nil => rfl
        | cons a l => exfalso; simp at Hblen; apply Hif; word
      subst hnil
      (try wp_auto)
      isplitr
      · first | itrivial | (ipureintro; rfl)
      iexists «$r0_ptr», chan.nil, t
      iframe
      ipureintro; left; exact ⟨rfl, rfl, rfl⟩
  iintro %v ⟨%Hv, %cw, %oc, %t', curWr, outc, Hb, Hbuf, Hbwt, Hbl, %Hco⟩
  subst Hv
  ihave HcwP : iprop(∃ vcw : go_etcd_io.etcd.client.v3.WatchResponse, cw ↦□ vcw ∗
      bufElems V P (rcv.length - bufl.length) bufl) $$ [Hbe]
  · rcases Hco with ⟨rfl, rfl, rfl⟩ | ⟨wr0, rest, rfl, rfl, rfl⟩
    · iexists _; iframe Hbe; iexact «$r0»
    · icases (bufElems_cons V P _ cw rest).1 $$ Hbe with ⟨Hhd, Hrest⟩
      icases recvLive_ptsto V P _ cw $$ Hhd with ⟨Hhd, %vcw, #Hvcw⟩
      iexists vcw
      iframe Hvcw
      iapply (bufElems_cons V P _ cw rest).2
      iframe Hhd Hrest
  icases HcwP with ⟨%vcw, #Hvcw, Hbe⟩
  wp_auto
  wp_apply +noauto WHDone as %dch2 %dγ2 #Hdone2
  wp_auto
  wp_apply +noauto CHDone as %dch3 %dγ3 #Hdone3
  wp_auto_lc 5
  wp_apply_core chan.wp_select_blocking_nil
  iapply BigAndL.bigAndL_cons.2
  isplit
  · rcases Hco with ⟨rfl, rfl, rfl⟩ | ⟨wr0, rest, rfl, rfl, rfl⟩
    · iright
      iapply chan.nilClausePre_send
      rfl
    ileft
    simp only [chan.blockingClausePre]
    iexists go_etcd_io.etcd.client.v3.WatchResponse, inferInstance, inferInstance, inferInstance,
      inferInstance, P.outc, P.γ.spsc.chanName, vcw
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · ihave #Ho' := Houtc
      unfold isSpsc
      icases Ho' with ⟨#Hic, -⟩
      iexact Hic
    icases (bufElems_cons V P _ cw rest).1 $$ Hbe with ⟨Hhd, Hrest⟩
    iunfold recvLive at Hhd
    icases Hhd with ⟨%v0, %r, %hiB, %hiA, #Hw0, %Hv, #Hev, Hhdr, #HiB, #HiA, #Hok, -⟩
    icombine Hw0 Hvcw gives %Heq
    subst Heq
    simp only [Int.toNat_natCast]
    ihave %HhB := mono_list_idx_agree P.γhi _ _ _ $$ HiB Hcur
    subst HhB
    iapply bupd_sendAu
    imod publish_elem V P C sent.length v0 r hiB hiA HC.1 HC.2.2
      ⟨Hv.2.2.1, Hv.2.2.2.1, Hv.2.2.2.2.1⟩ $$ [Hauth Hhdr] with ⟨Hauth, Helem⟩
    · iframe Hauth Hev Hok Hhdr
      rw [Hv.2.1]; iapply statusErrOk_nil
    imodintro
    iapply spsc_send_au P.γ.spsc P.outc _ _ sent v0 _ $$ Houtc [$Hlc1 $Hlc2 $Hlc3] [$Hprod $Helem]
    inext
    iintro Hprod
    wp_auto
    ihave ⟨%q, %rv, Hrv, Hrevb⟩ : iprop(∃ (q : Qp) (rv : w64), wsReqF P.ws go!"rev" ↦{DFrac.own q} rv ∗
        (wsReqF P.ws go!"rev" ↦{DFrac.own q} rv -∗
          (⌜rcv = []⌝ ∗ wsReqF P.ws go!"rev" ↦{DFrac.own (1 : Qp).half} P.rev ∨
            ⌜rcv ≠ []⌝ ∗ ∃ rv : w64, wsReqF P.ws go!"rev" ↦ rv))) $$ [Hrev]
    · icases Hrev with (⟨%Hc, Hrev⟩ | ⟨%Hc, %rv, Hrev⟩)
      · iexists _, _; iframe Hrev; iintro Hrev; ileft; iframe Hrev; ipureintro; exact Hc
      · iexists 1, rv; iframe Hrev; iintro Hrev; iright; isplitr
        · ipureintro; exact Hc
        iexists rv; iexact Hrev
    wp_apply wp_recordBufWait $$ [Hbl Hbwt Hrv Hbuf] as ⟨Hbl, Hla, %t'', Hbwt⟩
    · iframe Flg Hbl Hblok Hbwt
      unfold wsLogA
      iframe Hrv Hbuf
    iunfold wsLogA at Hla
    icases Hla with ⟨Hrv, Hbuf⟩
    ihave Hrev := Hrevb $$ Hrv
    (try wp_auto)
    have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by
      simp at Hblen; word
    rw [if_pos Hb0]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) (cw :: rest) (DFrac.own 1) cw (by word)
      $$ [Hb] as Hb
    · iframe Hb; ipureintro; simp
    wp_apply wp_Err cw v0 DFrac.discard $$ [] as %err ⟨-, %Herr, -⟩
    · iframe Hvcw
      rw [Hv.2.1]; iapply statusErrOk_nil
    have Herr0 : err = interface.nil :=
      Herr.2 ⟨Hv.2.1, Hv.2.2.1.trans Hv.2.2.2.2.2.1, Hv.2.2.2.1.trans Hv.2.2.2.2.2.2⟩
    subst Herr0
    (try wp_auto)
    rw [if_pos Hb0]
    wp_apply wp_store_slice_index b (sint.Z (W64 0)) (cw :: rest) (null : Loc) $$ [Hb] as Hb
    · iframe Hb; ipureintro; simp
    (try wp_auto)
    ihave %Hcapwf := ownSliceCap_wf _ _ $$ Hbcap
    have Hb1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z b.len ∧ sint.Z b.len ≤ sint.Z b.cap := by
      simp at Hblen; word
    rw [if_pos Hb1]
    icases ownSlice_slice_with_cap (W64 1) b.len b _ ⟨by word, Hb1.2.1, by word⟩ $$ [Hb Hbcap]
      with ⟨-, Hb, Hbcap⟩
    · iframe
    (try wp_auto)
    wp_for_post
    iframe HΦ Hdn Hx Hwg Hwstok resuming Hdefer Hclosing Hbl
    iexists rcv, sent ++ [v0], C ++ [hiA], rest, slice.slice b Loc (W64 1) b.len, rcf, nr, t'', hiA
    have hlen : rest.length + 1 ≤ rcv.length := by simpa using HC.2.1
    have hidx : rcv.length - rest.length = rcv.length - (cw :: rest).length + 1 := by
      simp only [List.length_cons]; omega
    simp only [named]
    rw [hidx]
    iframe Hcons Hprod Hauth Hbuf Hbwt nextRev Hretc HiA Hrest Hrr
    unfold sliceOwn
    iframe Hbcap
    isplitr
    · ipureintro
      refine ⟨by simp [HC.1], by omega, by simp⟩
    isplitl [Hb]
    · have h1 : sint.nat (W64 1) = 1 := by word
      have hsub : subslice (sint.nat (W64 1)) (sint.nat b.len) (null :: rest) = rest := by
        rw [← Hblen.1, h1]; simp [subslice]
      simp only [hsub]
      iexact Hb
    iexact Hrev
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, P.recvc,
      P.γr.chanName
    isplitr
    · ipureintro; rfl
    isplitr
    · ihave #Hrv' := Hrecvc
      unfold isSpsc
      icases Hrv' with ⟨#Hic, -⟩
      iexact Hic
    iapply spsc_rcv_au P.γr P.recvc _ _ rcv _ $$ Hrecvc [$Hlc1 $Hlc2] Hcons
    inext
    iintro %wr %ok Hrecv
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hrecv with ⟨-, %Hwr⟩
      wp_auto
      ss_return
    simp only [↓reduceIte]
    icases Hrecv with ⟨HE, Hcons⟩
    icases recvElem_live V P _ wr $$ [Hx HE] with ⟨Hx, HE⟩
    · iframe
    iunfold recvLive at HE
    icases HE with ⟨%v, %r, %hiB, %hiA, #Hwr, %Hv, #Hev, Hhdr, #HiB, #HiA, #Hok, Hk⟩
    ihave #Hwr' := Hwr
    iStructNamed Hwr'
    wp_auto
    by_cases hk : rcv = []
    · subst hk
      simp only [List.length_nil, Int.natCast_zero, Int.toNat_zero, ↓reduceIte]
      icases Hk with ⟨%Hcr, %rv, Hrv2⟩
      have Hcreated : v.Created' = true := Hv.2.2.2.2.1.trans Hcr.1
      rw [Hcreated]
      icases Hrr with (⟨%Hrr, Hres⟩ | %Hrr)
      rotate_left
      · exact absurd rfl Hrr.1
      obtain ⟨-, rfl⟩ := Hrr
      icases Hrev with (⟨-, Hrev⟩ | ⟨%Hne, -⟩)
      rotate_left
      · exact absurd rfl Hne
      icombine Hrev Hrv2 gives %Hrveq
      subst Hrveq
      ihave Hrev := ptsto_halves _ _ $$ [Hrev Hrv2]
      · iframe
      wp_auto
      have hbl : bufl = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 HC.2.1)
      subst hbl
      simp only [List.length_nil, Nat.sub_self]
      ihave %HhB := mono_list_idx_agree P.γhi 0 _ _ $$ HiB Hcur
      subst HhB
      ihave #Hok' := Hok
      iunfold rangeWatchRespOk at Hok'
      icases Hok' with ⟨%Hokp, -⟩
      have HhA : hiA = hiB := by rw [Hokp.2.2, Hcr.2]; rfl
      subst HhA
      ihave #Hhdr := (watchHdrOwn_nil _ _ Hcr.2).1 $$ Hhdr
      ihave #Hhdr2 := Hhdr
      iunfold hdrAt at Hhdr2
      icases Hhdr2 with (⟨%Hn, -⟩ | ⟨-, #Hhrev⟩)
      · exact absurd Hn Hv.1
      wp_bind (If (Val #(!decide (P.retc = chan.nil))) _ _)
      iapply (wp_wand_r (Φ := fun x => iprop(⌜x = executeVal⌝ ∗
          ∃ (sent' : List go_etcd_io.etcd.client.v3.WatchResponse) (C' : List w64) (nr' : w64),
          spscProducer P.γ.spsc sent' ∗ monoListAuthOwn P.γ.cur 1 C' ∗
          ⌜C'.length = sent'.length + 1 ∧ C'.getLast? = some hiA⌝ ∗
          wsReqF P.ws go!"retc" ↦ (null : Loc) ∗ nextRev_ptr ↦ nr' ∗
          wsReqF P.ws go!"rev" ↦ P.rev ∗ wr_ptr ↦ wr)))
      isplitl [Hprod Hauth Hretc nextRev Hres Hrev wr]
      · wp_if_destruct
        · (try wp_auto)
          isplitr
          · first | itrivial | (ipureintro; rfl)
          iexists sent, C, nr
          rw [Hif]
          iframe
          ipureintro; exact ⟨HC.1, HC.2.2⟩
        · iunfold retcRes at Hres
          wp_apply wp_bag_send $$ [Hres]
          · iframe Hretcb
            unfold retcP
            iexists P.γ
            iframe Houtc
            iexact Hres
          (try wp_auto)
          cases hcn : P.cn
          · (try wp_auto)
            wp_if_destruct <;> (try wp_auto) <;> c2_fin
          · (try wp_auto)
            imod publish_elem V P C sent.length v r hiA hiA HC.1 HC.2.2
              ⟨Hv.2.2.1, Hv.2.2.2.1, Hv.2.2.2.2.1⟩ $$ [Hauth] with ⟨Hauth, Helem⟩
            · iframe Hauth Hev Hok
              isplitl []
              · iapply (watchHdrOwn_nil _ _ Hcr.2).2; iexact Hhdr
              rw [Hv.2.1]; iapply statusErrOk_nil
            wp_apply wp_spsc_send P.γ.spsc P.outc _ _ sent v $$ [Hprod Helem] as Hprod
            · iframe Houtc Hprod Helem
            wp_if_destruct <;> (try wp_auto) <;> c2_fin
      iintro %x ⟨%Hx, %sent', %C', %nr', Hprod, Hauth, %HC', Hretc, nextRev, Hrev, wr⟩
      subst Hx
      wp_auto
      ihave #Hev' := Hev
      iunfold eventsAt at Hev'
      icases Hev' with ⟨%ls, #Hls, %Hlslen, -⟩
      ihave %Hsl := ownSlice_len $$ Hls
      have Hlen0 : sint.Z v.Events'.len = 0 := by
        rw [Hcr.2] at Hlslen; simp at Hlslen; subst Hlslen; simp at Hsl; word
      rw [show decide (sint.Z (W64 0) < sint.Z v.Events'.len) = false by simp [Hlen0]]
      wp_auto
      wp_for_post
      iframe HΦ Hdn Hx Hwg Hwstok resuming Hdefer Hclosing Hbl
      iexists [wr], sent', C', [], b, (null : Loc), nr', t', hiA
      simp only [named, List.nil_append, List.length_singleton, List.length_nil, Nat.sub_zero,
        Nat.zero_add]
      iframe Hcons Hprod Hauth Hbuf Hbwt nextRev Hretc HiA
      unfold sliceOwn
      iframe Hb Hbcap
      isplitr
      · ipureintro; exact ⟨HC'.1, by simp, HC'.2⟩
      isplitr
      · iapply bufElems_nil
      isplitl [Hrev]
      · iright
        isplitr
        · ipureintro; simp
        iexists _; iexact Hrev
      iright; ipureintro; simp
    · have hk' : ((rcv.length : Nat) : Int) ≠ 0 := by
        intro h; apply hk; exact List.eq_nil_of_length_eq_zero (by omega)
      simp only [hk', ↓reduceIte]
      icases Hk with %Hcr
      have Hcreated : v.Created' = false := Hv.2.2.2.2.1.trans Hcr
      icases Hrev with (⟨%Hc, -⟩ | ⟨-, %rv, Hrev⟩)
      · exact absurd Hc hk
      ihave ⟨%dq, Hhf, Hback⟩ : iprop(∃ dq : DFrac,
          structFieldRef etcdserverpb.ResponseHeader go!"Revision" v.Header' ↦{dq} r.hdrRev ∗
          (structFieldRef etcdserverpb.ResponseHeader go!"Revision" v.Header' ↦{dq} r.hdrRev -∗
            watchHdrOwn v.Header' r)) $$ [Hhdr]
      · by_cases he : r.events = []
        · icases (watchHdrOwn_nil _ _ he).1 $$ Hhdr with #Hhdr
          ihave #Hhdr2 := Hhdr
          iunfold hdrAt at Hhdr2
          icases Hhdr2 with (⟨%Hn, -⟩ | ⟨-, #Hhrev⟩)
          · exact absurd Hn Hv.1
          iexists DFrac.discard
          iframe Hhrev
          iintro -
          iapply (watchHdrOwn_nil _ _ he).2
          iexact Hhdr
        · icases (watchHdrOwn_cons _ _ he).1 $$ Hhdr with ⟨%Hn, Hhrev⟩
          iexists DFrac.own 1
          iframe Hhrev
          iintro Hhrev
          iapply (watchHdrOwn_cons _ _ he).2
          iframe Hhrev
          ipureintro; exact Hn
      ihave #Hev' := Hev
      iunfold eventsAt at Hev'
      icases Hev' with ⟨%ls, #Hls, %Hlslen, #Hevat⟩
      ihave %Hsl := ownSlice_len $$ Hls
      rw [Hcreated]
      wp_auto
      wp_bind (If (Val #(decide (sint.Z (W64 0) < sint.Z v.Events'.len))) _ _)
      iapply (wp_wand_r (Φ := fun x => iprop(⌜x = executeVal⌝ ∗ ∃ nr' : w64,
          nextRev_ptr ↦ nr' ∗ wr_ptr ↦ wr)))
      isplitl [nextRev wr]
      · wp_if_destruct
        · have Hlt : sint.nat (v.Events'.len - W64 1) < ls.length := by word
          obtain ⟨l, Hl⟩ : ∃ l, ls[sint.nat (v.Events'.len - W64 1)]? = some l :=
            ⟨_, List.getElem?_eq_getElem Hlt⟩
          obtain ⟨e, He⟩ : ∃ e, r.events[sint.nat (v.Events'.len - W64 1)]? = some e :=
            ⟨_, List.getElem?_eq_getElem (by rw [← Hlslen]; exact Hlt)⟩
          have Hbnd : 0 ≤ sint.Z (v.Events'.len - W64 1) ∧
              sint.Z (v.Events'.len - W64 1) < sint.Z v.Events'.len := by word
          rw [if_pos Hbnd]
          icases ownSlice_elem_acc (sint.Z (v.Events'.len - W64 1)) l v.Events' DFrac.discard ls
            Hbnd.1 Hl $$ Hls with ⟨#Hle, -⟩
          ihave #He' := Hevat $$ %(sint.nat (v.Events'.len - W64 1)) %l %e %Hl %He
          iunfold eventAt at He'
          icases He' with ⟨%keySl, #Htyp, #HevKv, -, -, #HmR⟩
          (try wp_auto)
          isplitr
          · first | itrivial | (ipureintro; rfl)
          iexists _
          iframe
        · (try wp_auto)
          isplitr
          · first | itrivial | (ipureintro; rfl)
          iexists _
          iframe
      iintro %x ⟨%Hx, %nr', nextRev, wr⟩
      subst Hx
      wp_auto
      icases Hrr with (⟨%Hr, -⟩ | %Hr)
      · exact absurd Hr.1 hk
      wp_apply wp_slice_literal (V := Loc) [wr]
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      (try wp_auto)
      wp_apply wp_slice_append $$ [Hb Hbcap Hsl2] as %b' ⟨Hb, Hbcap, -⟩
      · iframe
      (try wp_auto)
      wp_for_post
      iframe HΦ Hdn Hx Hwg Hwstok resuming Hdefer Hclosing Hbl
      iexists rcv ++ [wr], sent, C, bufl ++ [wr], b', rcf, nr', t', cl
      have hidx : rcv.length + 1 - (bufl.length + 1) = rcv.length - bufl.length := by omega
      simp only [named, List.length_append, List.length_singleton]
      (try rw [hidx])
      iframe Hcons Hprod Hauth Hbuf Hbwt nextRev Hretc Hcur
      unfold sliceOwn
      iframe Hb Hbcap
      isplitr
      · ipureintro; exact ⟨HC.1, by omega, HC.2.2⟩
      isplitl [Hbe Hhf Hback]
      · iapply bufElems_snoc
        iframe Hbe
        have hk2 : rcv.length - bufl.length + bufl.length = rcv.length := by omega
        rw [hk2]
        unfold recvLive
        iexists v, r, hiB, hiA
        iframe Hwr Hev HiB HiA Hok
        isplitr
        · ipureintro; exact Hv
        isplitl [Hhf Hback]
        · iapply Hback; iexact Hhf
        simp only [hk', ↓reduceIte]
        ipureintro; exact Hcr
      isplitl [Hrev]
      · iright
        isplitr
        · ipureintro; simp
        iexists _; iexact Hrev
      iright; ipureintro; exact ⟨by simp, Hr.2⟩
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch2, dγ2
    isplit
    · ipureintro; rfl
    isplit
    · iapply context.isContextDone_is_chan $$ Hdone2
    iapply context.isContextDone_receive _ _ _ _ $$ Hdone2
    iintro -
    wp_auto
    ss_return
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch3, dγ3
    isplit
    · ipureintro; rfl
    isplit
    · iapply context.isContextDone_is_chan $$ Hdone3
    iapply context.isContextDone_receive _ _ _ _ $$ Hdone3
    iintro -
    wp_auto
    ss_return
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, rc, γrc
    isplit
    · ipureintro; rfl
    isplit
    · iapply ownBroadcastChan_is_chan $$ Hrc
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hrc
    iintro ⟨#Hf, -⟩
    iexfalso
    iexact Hf
  iapply BigAndL.bigAndL_nil.2
  itrivial
