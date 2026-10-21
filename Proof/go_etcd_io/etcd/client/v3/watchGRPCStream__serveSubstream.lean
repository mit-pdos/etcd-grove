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
public import Proof.go_etcd_io.etcd.client.v3.WatchResume

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
    (hf : v.CompactRevision' = r.compactRev ∧ v.Canceled' = r.canceled ∧ v.Created' = r.created)
    :
    monoListAuthOwn (GF := GF) P.γ.cur 1 C ∗ eventsAt v.Events' r.events ∗
      watchHdrOwn v.Header' r ∗ rangeWatchRespOk (EM := V.EM) V.pfx P.o P.rev hiB hiA r ∗
      statusErrOk v.closeErr' ∗
      (⌜P.γ.cpl = false⌝ ∨ ∃ c2 c2' : w64, monoListIdxOwn P.γ.cur2 i c2 ∗
        monoListIdxOwn P.γ.cur2 (i + 1) c2' ∗ watchRespOk (EM := V.EM) P.o.key c2 c2' v r) ⊢
    |==> (monoListAuthOwn P.γ.cur 1 (C ++ [hiA]) ∗
      rangeWatchElem (EM := V.EM) P.γ V.pfx P.o P.rev (i : Int) v) := by
  iintro ⟨Hauth, #Hev, Hhdr, #Hok, #Hse, #Hc2⟩
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
  isplitr
  · ipureintro; exact hf
  iexact Hc2

/-- A created response without events keeps the cache's contract's position. -/
theorem watchRespOk_created (V : WEnv GF) (pfx : GoString) (c c' : w64) (v : go_etcd_io.etcd.client.v3.WatchResponse)
    (r : RespModel) (hc : r.created = true) (he : r.events = []) :
    watchRespOk (EM := V.EM) pfx c c' v r ⊢ ⌜c' = c⌝ := by
  unfold watchRespOk
  iintro (⟨%H, -⟩ | %H | ⟨%H, -, -⟩ | ⟨%H, -⟩)
  · ipureintro; exact H.2
  · ipureintro; exact H.2.2.2
  · exfalso; simp [RespModel.isProgressNotify, hc] at H
  · exact absurd he H.2.1

/-- **Publishing a received response, the second cursor** (K2e-7): the `kk`th received response's
contract at the second dispatch cursor's positions becomes the published one's at `γ.cur2`'s. -/
theorem publish_cmpl (V : WEnv GF) (P : WsPrm GF) (i k : Nat) (kk : Int) (hk : kk.toNat = k)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) :
    cur2Pos (GF := GF) P i k ∗ recvCmpl V P kk v r ⊢
    |==> (cur2Pos P (i + 1) (k + 1) ∗
      (⌜P.γ.cpl = false⌝ ∨ ∃ c2 c2' : w64, monoListIdxOwn P.γ.cur2 i c2 ∗
        monoListIdxOwn P.γ.cur2 (i + 1) c2' ∗ watchRespOk (EM := V.EM) P.o.key c2 c2' v r)) := by
  unfold cur2Pos recvCmpl
  rw [hk]
  iintro ⟨(%H | ⟨%C2, %cl2, Ha, %HC, #Hk⟩), #Hc⟩
  · imodintro
    isplitl []
    · ileft; ipureintro; exact H
    · ileft; ipureintro; exact H
  icases Hc with (%H | ⟨%h2B, %h2A, #HB, #HA, #Hok⟩)
  · imodintro
    isplitl []
    · ileft; ipureintro; exact H
    · ileft; ipureintro; exact H
  ihave %Hb := mono_list_idx_agree P.γh2 _ _ _ $$ HB Hk
  subst Hb
  imod monoListAuthOwn_update_app (GF := GF) [h2A] $$ Ha with ⟨Ha, #Hlb⟩
  have h1 : (C2 ++ [h2A])[i]? = some h2B := by
    rw [List.getElem?_append_left (by omega)]; exact getElem?_of_getLast? HC.1 HC.2
  have h2 : (C2 ++ [h2A])[i + 1]? = some h2A := by
    rw [List.getElem?_append_right (by omega)]; simp [HC.1]
  ihave #Hi1 := monoListIdxOwn_get (GF := GF) i h2B h1 $$ Hlb
  ihave #Hi2 := monoListIdxOwn_get (GF := GF) (i + 1) h2A h2 $$ Hlb
  imodintro
  isplitl [Ha]
  · iright
    iexists C2 ++ [h2A], h2A
    iframe Ha HA
    ipureintro; simp [HC.1]
  iright
  iexists h2B, h2A
  iframe Hi1 Hi2 Hok

/-- **A created response, not published** (K2e-7): the second cursor's position moves past it
(it keeps the cache's contract's position). -/
theorem skip_cmpl (V : WEnv GF) (P : WsPrm GF) (i k : Nat) (kk : Int) (hk : kk.toNat = k)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) (hc : r.created = true)
    (he : r.events = []) :
    cur2Pos (GF := GF) P i k ∗ recvCmpl V P kk v r ⊢ cur2Pos P i (k + 1) := by
  unfold cur2Pos recvCmpl
  rw [hk]
  iintro ⟨(%H | ⟨%C2, %cl2, Ha, %HC, #Hk⟩), #Hc⟩
  · ileft; ipureintro; exact H
  icases Hc with (%H | ⟨%h2B, %h2A, #HB, #HA, #Hok⟩)
  · ileft; ipureintro; exact H
  ihave %Hb := mono_list_idx_agree P.γh2 _ _ _ $$ HB Hk
  subst Hb
  ihave %Ha := watchRespOk_created V P.o.key h2B h2A v r hc he $$ Hok
  subst Ha
  iright
  iexists C2, h2A
  iframe Ha HA
  ipureintro; exact HC

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

/-- The two halves of the membership token and a whole one are too many. -/
theorem ghostMapElem_half_whole (γ : GName) (k : Loc) :
    ghostMapElem (GF := GF) (K := Loc) (V := Unit) γ k (DFrac.own (1 : Qp).half) () ∗
      ghostMapElem γ k (DFrac.own 1) () ⊢ False := by
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %Hv
  exfalso
  obtain ⟨Hv, _⟩ := Hv
  revert Hv
  simp only [CMRA.Valid, DFrac.op_own]
  intro h
  have : (1 / 2 : Rat) + 1 ≤ 1 := h
  grind

theorem chainE_trans (P : WsPrm GF) (a b c : Nat) :
    chainE (GF := GF) P a b ∗ chainE P b c ⊢ chainE P a c := by
  unfold chainE
  iintro ⟨⟨%H1, ⟨%x, #Hx1, #Hx2⟩, Hy⟩, ⟨%H2, ⟨%x', #Hx1', #Hx2'⟩, Hy'⟩⟩
  ihave %Hxx := mono_list_idx_agree P.γhi b _ _ $$ Hx2 Hx1'
  subst Hxx
  isplitr
  · ipureintro; omega
  isplitr
  · iexists x; iframe Hx1 Hx2'
  icases Hy with (%H | ⟨%y, #Hy1, #Hy2⟩)
  · ileft; ipureintro; exact H
  icases Hy' with (%H | ⟨%y', #Hy1', #Hy2'⟩)
  · ileft; ipureintro; exact H
  ihave %Hyy := mono_list_idx_agree P.γh2 b _ _ $$ Hy2 Hy1'
  subst Hyy
  iright; iexists y; iframe Hy1 Hy2'

theorem hi_move (P : WsPrm GF) (a b : Nat) (cl : w64) :
    monoListIdxOwn (GF := GF) P.γhi a cl ∗ chainE P a b ⊢ monoListIdxOwn P.γhi b cl := by
  unfold chainE
  iintro ⟨#Hc, -, ⟨%x, #Hx1, #Hx2⟩, -⟩
  ihave %Hxx := mono_list_idx_agree P.γhi a _ _ $$ Hc Hx1
  subst Hxx
  iexact Hx2

theorem cur2Pos_move (P : WsPrm GF) (n a b : Nat) :
    cur2Pos (GF := GF) P n a ∗ chainE P a b ⊢ cur2Pos P n b := by
  unfold cur2Pos chainE
  iintro ⟨(%H | ⟨%C2, %cl2, Ha, %HC, #Hk⟩), ⟨-, -, Hy⟩⟩
  · ileft; ipureintro; exact H
  icases Hy with (%H | ⟨%y, #Hy1, #Hy2⟩)
  · ileft; ipureintro; exact H
  ihave %Hyy := mono_list_idx_agree P.γh2 a _ _ $$ Hk Hy1
  subst Hyy
  iright
  iexists C2, cl2
  iframe Ha Hy2
  ipureintro; exact HC

theorem bufE_le (V : WEnv GF) (P : WsPrm GF) (q : List (Nat × Loc)) :
    ∀ (a n : Nat), bufE (GF := GF) V P a q n ⊢ ⌜a ≤ n⌝ := by
  induction q with
  | nil =>
    intro a n
    simp only [bufE]
    unfold chainE
    iintro ⟨%H, -⟩
    ipureintro; exact H
  | cons x rest ih =>
    intro a n
    simp only [bufE]
    iintro ⟨Hc, -, Hr⟩
    unfold chainE
    icases Hc with ⟨%H1, -⟩
    ihave %H2 := ih (x.1 + 1) n $$ Hr
    ipureintro; omega

theorem bufE_zero (V : WEnv GF) (P : WsPrm GF) (q : List (Nat × Loc)) (a : Nat) :
    bufE (GF := GF) V P a q 0 ⊢ ⌜a = 0 ∧ q = []⌝ := by
  cases q with
  | nil =>
    simp only [bufE]
    unfold chainE
    iintro ⟨%H, -⟩
    ipureintro; exact ⟨by omega, by simp⟩
  | cons x rest =>
    simp only [bufE]
    iintro ⟨-, -, Hr⟩
    ihave %H := bufE_le V P rest (x.1 + 1) 0 $$ Hr
    exfalso; omega

theorem bufE_snoc (V : WEnv GF) (P : WsPrm GF) (q : List (Nat × Loc)) (n : Nat) (wr : Loc) :
    ∀ a : Nat, bufE (GF := GF) V P a q n ∗ recvLive V P (n : Int) wr ∗ chainE P (n + 1) (n + 1) ⊢
      bufE V P a (q ++ [(n, wr)]) (n + 1) := by
  induction q with
  | nil =>
    intro a
    simp only [bufE, List.nil_append]
    iintro ⟨Hc, Hl, Hn⟩
    iframe
  | cons x rest ih =>
    intro a
    simp only [bufE, List.cons_append]
    iintro ⟨⟨Hc, Hx, Hr⟩, Hl, Hn⟩
    iframe Hc Hx
    iapply ih (x.1 + 1)
    iframe

theorem bufE_skip (V : WEnv GF) (P : WsPrm GF) (q : List (Nat × Loc)) (n : Nat) :
    ∀ a : Nat, bufE (GF := GF) V P a q n ∗ chainE P n (n + 1) ⊢ bufE V P a q (n + 1) := by
  induction q with
  | nil =>
    intro a
    simp only [bufE]
    iintro H
    iapply chainE_trans P a n (n + 1) $$ H
  | cons x rest ih =>
    intro a
    simp only [bufE]
    iintro ⟨⟨Hc, Hx, Hr⟩, Hn⟩
    iframe Hc Hx
    iapply ih (x.1 + 1)
    iframe

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
/-- **The substream stops for good** (any `return` of the loop but `resumec`'s, the loop's resources
named as in its invariant): the deferred functions record the buffer's wait, mark the substream
closing (for good), set `γx`, close `donec` (`lifeQ`, stopped), leave what `run` needs in the
lifetime's invariant (`stopBody`), post the whole membership token on `closingc` and signal the
wait group. -/
local macro "ss_return" : tactic => `(tactic| (
  wp_for_post
  ihave Hrv : iprop(∃ (q : Qp), wsReqF P.ws go!"rev" ↦{DFrac.own q} nr) $$ [Hrev]
  · icases Hrev with (⟨%Hkr, Hrev⟩ | ⟨-, Hrev⟩)
    · iexists _; rw [Hkr.2]; iexact Hrev
    · iexists 1; iexact Hrev
  icases Hrv with ⟨%q, Hrv⟩
  wp_apply +noauto wp_recordBufWait $$ [Hbl Hbwt Hrv Hbuf] as ⟨Hbl, Hla, %t'', Hbwt⟩
  · iframe Flg Hbl Hblok Hbwt
    unfold wsLogA
    iframe Hrv Hbuf
  iunfold wsLogA at Hla
  icases Hla with ⟨Hrv, Hbuf⟩
  imod dghostVar_update true _ _ $$ Hx with Hx
  imod dghostVar_persist _ _ _ $$ Hx with #Hx
  wp_auto_lc 1
  ipersist Hclosing
  -- the deposit (D25), before `donec`'s close (which publishes it)
  iapply fupd_wp
  iinv Hlinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑lifeN) $$ Hlc1 Hi with Hi
  iunfold lifeSt at Hi
  icases Hi with (⟨Hγt2, Hmh⟩ | ⟨#Ht, -⟩)
  rotate_left
  · ihave %H := dghostVar_agree _ _ _ _ _ $$ Hγt Ht
    cases H
  imod dghostVar_update_halves true _ _ _ $$ Hγt Hγt2 with ⟨Hγt, -⟩
  imod dghostVar_persist _ _ _ $$ Hγt with #Hγt
  ihave Hwstok := (ghostMapElem_halves G.γws P.ws ()).2 $$ [Hwstok Hmh]
  · iframe
  imod Hclose $$ [Houtcf Hprod Hauth Hc2 Hretc Hrr Hrv Hdnf] with -
  · inext
    iunfold lifeSt
    iright
    iframe Hγt
    ileft
    isplitr
    · unfold wsStopped; iframe #
    ileft
    unfold stopBody outcProd
    iexists rcf, q, nr, L.dc
    ihave #Hrs' : iprop(∃ hl c2 : w64, resumeOk V P nr hl c2) $$ []
    · icases Hrsm with ⟨%hl, %c2, -, -, #Hrs⟩
      iexists hl, c2
      iexact Hrs
    iframe Hretc Hrv Hdnf Hrs'
    isplitl [Houtcf Hprod Hauth Hc2]
    · ileft
      iframe Houtcf
      iexists sent, C; iframe Hprod Hauth
      isplitr
      · ipureintro; exact HC.1
      iapply cur2Pos_auth; iexact Hc2
    icases Hrr with (⟨%Hr, Hres, -⟩ | %Hr)
    · iright; iframe Hres; ipureintro; exact Hr.2.1
    · ileft; ipureintro; exact Hr.2
  imodintro
  wp_apply +noauto wp_broadcast_chan_close $$ [Hdn] as #Hdnd
  · iframe Hdn; imodintro; unfold lifeQ wsStopped; iframe #
  (try wp_auto)
  wp_apply wp_bag_send $$ [Hwstok]
  · iframe Hclb
    unfold closingP
    iexact Hwstok
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
  refine ⟨?_, ?_, ?_⟩
  · first | exact HC.1 | simp [HC.1]
  · first | exact HC.2 | simp
  · first | exact Or.inl rfl | exact Or.inl Hnr0P | exact Or.inr ⟨Hif, rfl⟩ | (right; exact ⟨by simpa using Hif, rfl⟩)))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem watchGRPCStream.serveSubstream.wp_proof
    (wp_startBufWait : watchGRPCStream.startBufWait.spec (GF := GF) (hG := hG))
    (wp_recordBufWait : watchGRPCStream.recordBufWait.spec (GF := GF) (hG := hG))
    (wp_resetBufWait : watcherStream.resetBufWait.spec (GF := GF) (hG := hG))
    (wp_Err : WatchResponse.Err.spec (GF := GF) (hG := hG)) :
    watchGRPCStream.serveSubstream.spec (GF := GF) (hG := hG) := by
  intro V G callSl P L k0 rv0 rcv0 bl rc γrc
  wp_start as ⟨#HG, #HP, Hst0, %Hk0, #Hls0, Hclosing, Hbl, #Hblok, Houtcf, Hdnf, Hdn, #Hlinv,
    Hγt, #Hrc, Hx, Hwg, Hwstok⟩
  ihave #HP' := HP
  iunfold wsIs at HP'
  icases HP' with ⟨#Hro, #Hfrecvc, #Houtc, #Hrecvc, #Hctx, #Hretcb, %HPws, #Hsok⟩
  ihave #HG' := HG
  iunfold isWGS at HG'
  icases HG' with ⟨%Hwgs, -, #Hsf, %Hlg, #Fowner, #Fremote, #FcallOpts, #Fctx, #FctxKey, #Fcancel,
    #Freqc, #Frespc, #Fdonec, #Ferrc, #Fclosingc, #Flg, #HGctx, #HGcancel, #Hreqb, #Herrb, #Hclb,
    #HGdone, -⟩
  ihave #Hro' := Hro
  iunfold wrRO at Hro'
  icases Hro' with ⟨#Rctx, #Rkey, #Rend, #Rcn, #Rpn, #Rfrag, #Rwbl, #Rflt, #Rflts, #RprevKV⟩
  ihave #HGc := HGctx
  iNamedPrefix HGc "W"
  ihave #HPc := Hctx
  iNamedPrefix HPc "C"
  iunfold wsRun at Hst0
  icases Hst0 with ⟨%sent0, %C0, %bq0, %b0, %rcf0, %t0, %cl0, %p00, Hcons, -, Hprod, Hauth, %HC0,
    #Hcur0, Hc20, Hbuf, Hb0, Hbe0, Hrev0, #Hrsm0, Hretc, Hrr0, Hbwt⟩
  icases Hrev0 with (⟨-, Hrev⟩ | ⟨%Hne, -⟩)
  rotate_left
  · exact absurd Hk0 Hne
  wp_apply wp_with_defer
  iintro %defer Hdefer
  wp_auto
  ipersist «$v0»
  ipersist «$r0»
  ipersist emptyWr
  ipersist w
  ipersist ws
  ipersist resumec
  ihave IH : iprop(∃ (rcv : List Loc) (nr : w64), "Hst" ∷ wsRun V P k0 rv0 rcv nr ∗
      "nextRev" ∷ nextRev_ptr ↦ nr)
      $$ [Hcons Hprod Hauth Hc20 Hbuf Hb0 Hbe0 Hrev Hretc Hrr0 Hbwt nextRev]
  · iexists rcv0, rv0
    simp only [named]
    iframe nextRev
    unfold wsRun
    iexists sent0, C0, bq0, b0, rcf0, t0, cl0, p00
    iframe Hcons Hprod Hauth Hc20 Hbuf Hb0 Hbe0 Hretc Hrr0 Hbwt Hcur0 Hrsm0
    isplitr
    · ipureintro; omega
    isplitr
    · ipureintro; exact HC0
    ileft; iframe Hrev; ipureintro; exact ⟨Hk0, rfl⟩
  wp_for IH
  iunfold wsRun at Hst
  icases Hst with ⟨%sent, %C, %bq, %b, %rcf, %t, %cl, %p0, Hcons, %Hkr, Hprod, Hauth, %HC, #Hcur,
    Hc2, Hbuf, Hb, Hbe, Hrev, #Hrsm, Hretc, Hrr, Hbwt⟩
  iunfold sliceOwn at Hb
  icases Hb with ⟨Hb, Hbcap⟩
  ihave %Hblen := ownSlice_len _ _ _ $$ Hb
  wp_auto
  wp_bind (If (Val #(decide (sint.Z (W64 0) < sint.Z b.len))) _ _)
  iapply (wp_wand_r (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
      ∃ (cw oc : Loc) (t' : _root_.Perennial.time.Time), curWr_ptr ↦ cw ∗ outc_ptr ↦ oc ∗
      b ↦* (bq.map Prod.snd) ∗ wsF P.ws go!"buf" ↦ b ∗ wsF P.ws go!"bufWaitStartTime" ↦ t' ∗
      wsF P.ws go!"bufLogger" ↦ bl ∗ wsF P.ws go!"outc" ↦ P.outc ∗
      ⌜(bq = [] ∧ oc = chan.nil ∧ cw = «$r0_ptr») ∨
        (∃ k wr0 rest, bq = (k, wr0) :: rest ∧ oc = P.outc ∧ cw = wr0)⌝)))
  isplitl [curWr outc Hb Hbuf Hbwt Hbl Houtcf]
  · wp_if_destruct
    · obtain ⟨k, wr0, rest, hbl⟩ : ∃ k wr0 rest, bq = (k, wr0) :: rest := by
        cases bq with
        | nil => simp at Hblen; word
        | cons a l => exact ⟨a.1, a.2, l, rfl⟩
      subst hbl
      simp only [List.map_cons]
      rw [ite_eq_left_iff.2 (fun h => absurd ⟨by word, Hif⟩ h)]
      wp_apply wp_load_slice_index b (sint.Z (W64 0)) (wr0 :: rest.map Prod.snd) (DFrac.own 1) wr0
        (by word) $$ [Hb] as Hb
      · iframe Hb; ipureintro; simp
      wp_apply wp_startBufWait $$ [Hbl Hbwt] as ⟨Hbl, %t', Hbwt⟩
      · iframe Flg Hbl Hblok Hbwt
      isplitr
      · first | itrivial | (ipureintro; rfl)
      iexists wr0, P.outc, t'
      iframe
      ipureintro; right; exact ⟨k, wr0, rest, rfl, rfl, rfl⟩
    · have hnil : bq = [] := by
        cases bq with
        | nil => rfl
        | cons a l => exfalso; simp at Hblen; apply Hif; word
      subst hnil
      (try wp_auto)
      isplitr
      · first | itrivial | (ipureintro; rfl)
      iexists «$r0_ptr», chan.nil, t
      iframe
      ipureintro; left; exact ⟨rfl, rfl, rfl⟩
  iintro %v ⟨%Hv, %cw, %oc, %t', curWr, outc, Hb, Hbuf, Hbwt, Hbl, Houtcf, %Hco⟩
  subst Hv
  ihave HcwP : iprop(∃ vcw : go_etcd_io.etcd.client.v3.WatchResponse, cw ↦□ vcw ∗
      bufE V P p0 bq rcv.length) $$ [Hbe]
  · rcases Hco with ⟨rfl, rfl, rfl⟩ | ⟨k, wr0, rest, rfl, rfl, rfl⟩
    · iexists _; iframe Hbe; iexact «$r0»
    · irevert Hbe
      simp only [bufE]
      iintro ⟨#Hch, Hhd, Hrest⟩
      icases recvLive_ptsto V P _ cw $$ Hhd with ⟨Hhd, %vcw, #Hvcw⟩
      iexists vcw
      iframe Hvcw Hch Hhd Hrest
  icases HcwP with ⟨%vcw, #Hvcw, Hbe⟩
  wp_auto
  wp_apply +noauto WHDone as %dch2 %dγ2 #Hdone2
  wp_auto
  wp_apply +noauto CHDone as %dch3 %dγ3 #Hdone3
  wp_auto_lc 5
  wp_apply_core chan.wp_select_blocking_nil
  iapply BigAndL.bigAndL_cons.2
  isplit
  · rcases Hco with ⟨rfl, rfl, rfl⟩ | ⟨k, wr0, rest, rfl, rfl, rfl⟩
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
    irevert Hbe
    simp only [bufE]
    iintro ⟨#Hch, Hhd, Hrest⟩
    iunfold recvLive at Hhd
    icases Hhd with ⟨%v0, %r, %hiB, %hiA, #Hw0, %Hv, #Hev, Hhdr, #HiB, #HiA, #Hok, #Hcm, -⟩
    icombine Hw0 Hvcw gives %Heq
    subst Heq
    simp only [Int.toNat_natCast]
    ihave #Hcurk := hi_move P p0 k cl $$ [Hcur Hch]
    · iframe #
    ihave %HhB := mono_list_idx_agree P.γhi _ _ _ $$ HiB Hcurk
    subst HhB
    ihave Hc2 := cur2Pos_move P sent.length p0 k $$ [Hc2 Hch]
    · iframe Hc2 Hch
    iapply bupd_sendAu
    imod publish_cmpl V P sent.length k (k : Int) (Int.toNat_natCast _) v0 r
      $$ [Hc2 Hcm] with ⟨Hc2, #Hc2e⟩
    · iframe Hc2 Hcm
    imod publish_elem V P C sent.length v0 r hiB hiA HC.1 HC.2
      ⟨Hv.2.2.1, Hv.2.2.2.1, Hv.2.2.2.2.1⟩ $$ [Hauth Hhdr] with ⟨Hauth, Helem⟩
    · iframe Hauth Hev Hok Hhdr Hc2e
      rw [Hv.2.1]; iapply statusErrOk_nil
    imodintro
    iapply spsc_send_au P.γ.spsc P.outc _ _ sent v0 _ $$ Houtc [$Hlc1 $Hlc2 $Hlc3] [$Hprod $Helem]
    inext
    iintro Hprod
    simp only [List.map_cons]
    wp_auto
    ihave ⟨%q, %rv, Hrv, Hrevb⟩ : iprop(∃ (q : Qp) (rv : w64), wsReqF P.ws go!"rev" ↦{DFrac.own q} rv ∗
        (wsReqF P.ws go!"rev" ↦{DFrac.own q} rv -∗
          (⌜rcv.length = k0 ∧ nr = rv0⌝ ∗ wsReqF P.ws go!"rev" ↦{DFrac.own (1 : Qp).half} rv0 ∨
            ⌜rcv.length ≠ k0⌝ ∗ wsReqF P.ws go!"rev" ↦ nr))) $$ [Hrev]
    · icases Hrev with (⟨%Hc, Hrev⟩ | ⟨%Hc, Hrev⟩)
      · iexists _, _; iframe Hrev; iintro Hrev; ileft; iframe Hrev; ipureintro; exact Hc
      · iexists 1, nr; iframe Hrev; iintro Hrev; iright; isplitr
        · ipureintro; exact Hc
        iexact Hrev
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
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) (cw :: rest.map Prod.snd) (DFrac.own 1) cw
      (by word) $$ [Hb] as Hb
    · iframe Hb; ipureintro; simp
    wp_apply wp_Err cw v0 DFrac.discard $$ [] as %err ⟨-, %Herr, -⟩
    · iframe Hvcw
      rw [Hv.2.1]; iapply statusErrOk_nil
    have Herr0 : err = interface.nil :=
      Herr.2 ⟨Hv.2.1, Hv.2.2.1.trans Hv.2.2.2.2.2.1, Hv.2.2.2.1.trans Hv.2.2.2.2.2.2⟩
    subst Herr0
    (try wp_auto)
    rw [if_pos Hb0]
    wp_apply wp_store_slice_index b (sint.Z (W64 0)) (cw :: rest.map Prod.snd) (null : Loc)
      $$ [Hb] as Hb
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
    iframe HΦ Hdn Hx Hwg Hwstok resuming Hdefer Hclosing Hbl Houtcf Hdnf Hγt
    iexists rcv, nr
    simp only [named]
    iframe nextRev
    unfold wsRun
    iexists sent ++ [v0], C ++ [hiA], rest, slice.slice b Loc (W64 1) b.len, rcf, t'', hiA, k + 1
    simp only [List.length_append, List.length_singleton]
    iframe Hcons Hprod Hauth Hbuf Hbwt Hretc HiA Hrest Hrr Hc2 Hrev Hrsm
    unfold sliceOwn
    iframe Hbcap
    isplitr
    · ipureintro; exact Hkr
    isplitr
    · ipureintro; exact ⟨by simp [HC.1], by simp⟩
    have h1 : sint.nat (W64 1) = 1 := by word
    have hsub : subslice (sint.nat (W64 1)) (sint.nat b.len) (null :: rest.map Prod.snd) =
        rest.map Prod.snd := by
      rw [h1]
      have : sint.nat b.len = (rest.map Prod.snd).length + 1 := by
        simp only [List.map_cons, List.length_cons] at Hblen; rw [← Hblen.1]
      rw [this]; simp [subslice]
      exact List.take_of_length_le (by simp)
    simp only [hsub]
    iexact Hb
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
      unfold isSspsc
      icases Hrv' with ⟨#Hic, -⟩
      iexact Hic
    iapply sspsc_rcv_au P.γr P.recvc _ _ rcv _ $$ Hrecvc [$Hlc1 $Hlc2] Hcons
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
    icases HE with ⟨%v, %r, %hiB, %hiA, #Hwr, %Hv, #Hev, Hhdr, #HiB, #HiA, #Hok, #Hcm, Hk⟩
    ihave #Hwr' := Hwr
    iStructNamed Hwr'
    wp_auto
    icases Hrsm with ⟨%hl0, %c20, #Hhl0, #Hc20', #Hrs⟩
    simp only [Int.toNat_natCast]
    by_cases hk : rcv.length = k0
    · -- (D25) the lifetime's first response: a created one
      cases hcrr : r.created
      · irevert Hk
        simp only [hcrr, Bool.false_eq_true, ↓reduceIte]
        iintro ⟨#Hns, -⟩
        iexfalso
        iapply lifeStart_notStart P k0
        isplit
        · iexact Hls0
        · rw [← hk]; iexact Hns
      irevert Hk
      simp only [hcrr, ↓reduceIte]
      iintro ⟨%Hcr0, %rv, Hrv2⟩
      have Hcr : r.created = true ∧ r.events = [] := ⟨hcrr, Hcr0⟩
      have Hcreated : v.Created' = true := Hv.2.2.2.2.1.trans Hcr.1
      rw [Hcreated]
      icases Hrev with (⟨%Hnr0, Hrev⟩ | ⟨%Hne, -⟩)
      rotate_left
      · exact absurd hk Hne
      icombine Hrev Hrv2 gives %Hrveq
      subst Hrveq
      ihave Hrev := ptsto_halves _ _ $$ [Hrev Hrv2]
      · iframe
      by_cases hr0 : rcv = []
      · -- the first response ever: `retc`, the created notification, "now"'s resume revision
        subst hr0
        simp only [List.length_nil] at hk Hkr
        subst hk
        simp only [List.length_nil, Nat.zero_add]
        icases Hrr with (⟨%Hrr, Hres, #Hhi0⟩ | %Hrr)
        rotate_left
        · exact absurd rfl Hrr.1
        obtain ⟨-, rfl, Hnr0P⟩ := Hrr
        obtain ⟨-, Hnrv⟩ := Hnr0
        subst Hnr0P
        subst Hnrv
        ihave %Hbz := bufE_zero V P bq p0 $$ Hbe
        obtain ⟨rfl, rfl⟩ := Hbz
        wp_auto
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
            ⌜C'.length = sent'.length + 1 ∧ C'.getLast? = some hiA ∧
              (nr' = P.rev ∨ (P.rev = W64 0 ∧ nr' = r.hdrRev))⌝ ∗ cur2Pos P sent'.length 1 ∗
            wsReqF P.ws go!"retc" ↦ (null : Loc) ∗ nextRev_ptr ↦ nr' ∗
            wsReqF P.ws go!"rev" ↦ P.rev ∗ wr_ptr ↦ wr ∗ wsF P.ws go!"outc" ↦ P.outc)))
        isplitl [Hprod Hauth Hretc nextRev Hres Hrev wr Hc2 Houtcf]
        · wp_if_destruct
          · (try wp_auto)
            ihave Hc2 := skip_cmpl V P sent.length 0 0 rfl v r Hcr.1 Hcr.2 $$ [Hc2 Hcm]
            · iframe Hc2 Hcm
            isplitr
            · first | itrivial | (ipureintro; rfl)
            iexists sent, C, P.rev
            rw [Hif]
            iframe
            ipureintro; exact ⟨HC.1, HC.2, Or.inl rfl⟩
          · iunfold retcRes at Hres
            wp_apply wp_bag_send $$ [Hres]
            · iframe Hretcb
              unfold retcP
              iexists P.γ
              iframe Houtc
              icases Hres with ⟨Hr1, Hr2, Hr3⟩
              iframe Hr1 Hr2 Hr3
              ipureintro; exact HPws.2.2
            (try wp_auto)
            cases hcn : P.cn
            · (try wp_auto)
              ihave Hc2 := skip_cmpl V P sent.length 0 0 rfl v r Hcr.1 Hcr.2 $$ [Hc2 Hcm]
              · iframe Hc2 Hcm
              wp_if_destruct <;> (try wp_auto) <;> c2_fin
            · (try wp_auto)
              imod publish_cmpl V P sent.length 0 0 rfl v r $$ [Hc2 Hcm] with ⟨Hc2, #Hc2e⟩
              · iframe Hc2 Hcm
              imod publish_elem V P C sent.length v r hiA hiA HC.1 HC.2
                ⟨Hv.2.2.1, Hv.2.2.2.1, Hv.2.2.2.2.1⟩ $$ [Hauth] with ⟨Hauth, Helem⟩
              · iframe Hauth Hev Hok Hc2e
                isplitl []
                · iapply (watchHdrOwn_nil _ _ Hcr.2).2; iexact Hhdr
                rw [Hv.2.1]; iapply statusErrOk_nil
              wp_apply wp_spsc_send P.γ.spsc P.outc _ _ sent v $$ [Hprod Helem] as Hprod
              · iframe Houtc Hprod Helem
              ihave Hc2 : cur2Pos P (sent ++ [v]).length 1 $$ [Hc2]
              · simp only [List.length_append, List.length_singleton]; iexact Hc2
              wp_if_destruct <;> (try wp_auto) <;> c2_fin
        iintro %x ⟨%Hx, %sent', %C', %nr', Hprod, Hauth, %HC', Hc2, Hretc, nextRev, Hrev, wr, Houtcf⟩
        subst Hx
        wp_auto
        ihave %Hhl0e := mono_list_idx_agree P.γhi 0 _ _ $$ HiB Hhl0
        subst Hhl0e
        ihave ⟨%h2A, #Hh2A, #Hw2⟩ := recvCmpl_at V P 0 v r c20 $$ [Hcm Hc20']
        · iframe Hcm; simp only [Int.toNat_zero]; iexact Hc20'
        ihave %Hh2e : ⌜P.γ.cpl = true → h2A = c20⌝ $$ []
        · icases Hw2 with (%Hcf | #Hw2)
          · ipureintro; intro h; rw [Hcf] at h; cases h
          ihave %H := watchRespOk_created V P.o.key c20 h2A v r Hcr.1 Hcr.2 $$ Hw2
          ipureintro; intro _; exact H
        ihave %Hhi0e := mono_list_idx_agree P.γhi 0 _ _ $$ HiB Hhi0
        have hl0 : nr' = P.rev ∨ sint.Z hiA < 0 := by
          rcases HC'.2.2 with h | ⟨h0, -⟩
          · exact Or.inl h
          · right; rw [Hhi0e, h0]; decide
        ihave #Hrs' := resumeOk_created V P r.hdrRev nr' hiA c20 HPws.2.2 HC'.2.2 hl0 $$ [Hrs]
        · iexact Hrs
        ihave #Hh2A' : iprop(⌜P.γ.cpl = false⌝ ∨ monoListIdxOwn P.γh2 1 c20) $$ []
        · icases Hh2A with (%Hcf | #Hh2A)
          · ileft; ipureintro; exact Hcf
          · cases hcp : P.γ.cpl
            · ileft; ipureintro; rfl
            · iright; rw [← Hh2e hcp]; simp only [Int.toNat_zero, Nat.zero_add] at *; iexact Hh2A
        ihave #Hev' := Hev
        iunfold eventsAt at Hev'
        icases Hev' with ⟨%ls, #Hls, %Hlslen, -⟩
        ihave %Hsl := ownSlice_len $$ Hls
        have Hlen0 : sint.Z v.Events'.len = 0 := by
          rw [Hcr.2] at Hlslen; simp at Hlslen; subst Hlslen; simp at Hsl; word
        rw [show decide (sint.Z (W64 0) < sint.Z v.Events'.len) = false by simp [Hlen0]]
        wp_auto
        wp_for_post
        iframe HΦ Hdn Hx Hwg Hwstok resuming Hdefer Hclosing Hbl Houtcf Hdnf Hγt
        iexists [wr], nr'
        simp only [named]
        iframe nextRev
        unfold wsRun
        iexists sent', C', [], b, (null : Loc), t', hiA, 1
        simp only [List.length_singleton, List.map_nil, List.nil_append]
        iframe Hcons Hprod Hauth Hbuf Hbwt Hretc Hc2
        unfold sliceOwn
        iframe Hb Hbcap
        isplitr
        · ipureintro; omega
        isplitr
        · ipureintro; exact ⟨HC'.1, HC'.2.1⟩
        isplitr
        · iexact HiA
        isplitr
        · simp only [bufE]
          iapply chainE_refl P 1 hiA
          iframe HiA
          icases Hh2A' with (%H | #H)
          · ileft; ipureintro; exact H
          · iright; iexists _; iexact H
        isplitl [Hrev]
        · iright
          isplitr
          · ipureintro; simp
          iexact Hrev
        isplitr
        · iexists hiA, c20
          iframe HiA Hh2A' Hrs'
        iright; ipureintro; simp
      · -- (D25) a resumed create: skipped, both cursors kept
        icases Hrr with (⟨%Hrr, -, -⟩ | %Hrr)
        · exact absurd Hrr.1 hr0
        obtain ⟨-, rfl⟩ := Hrr
        ihave %HhA0 : ⌜hiA = hiB⌝ $$ []
        · ihave #Hok' := Hok
          iunfold rangeWatchRespOk at Hok'
          icases Hok' with ⟨%Hokp, -⟩
          ipureintro; rw [Hokp.2.2, Hcr.2]; rfl
        subst HhA0
        ihave %Hhl0e := mono_list_idx_agree P.γhi _ _ _ $$ Hhl0 HiB
        subst Hhl0e
        ihave ⟨%h2A, #Hh2A, #Hw2⟩ := recvCmpl_at V P (rcv.length : Int) v r c20 $$ [Hcm Hc20']
        · iframe Hcm; simp only [Int.toNat_natCast]; iexact Hc20'
        simp only [Int.toNat_natCast] at *
        ihave %Hh2e : ⌜P.γ.cpl = true → h2A = c20⌝ $$ []
        · icases Hw2 with (%Hcf | #Hw2)
          · ipureintro; intro h; rw [Hcf] at h; cases h
          ihave %H := watchRespOk_created V P.o.key c20 h2A v r Hcr.1 Hcr.2 $$ Hw2
          ipureintro; intro _; exact H
        ihave #Hh2A' : iprop(⌜P.γ.cpl = false⌝ ∨ monoListIdxOwn P.γh2 (rcv.length + 1) c20) $$ []
        · icases Hh2A with (%Hcf | #Hh2A)
          · ileft; ipureintro; exact Hcf
          · cases hcp : P.γ.cpl
            · ileft; ipureintro; rfl
            · iright; rw [← Hh2e hcp]; iexact Hh2A
        ihave #Hchn : chainE P rcv.length (rcv.length + 1) $$ []
        · unfold chainE
          isplitr
          · ipureintro; omega
          isplitr
          · iexists hl0; iframe Hhl0 HiA
          icases Hh2A' with (%Hcf | #Hh2)
          · ileft; ipureintro; exact Hcf
          icases Hc20' with (%Hcf | #Hc0)
          · ileft; ipureintro; exact Hcf
          iright; iexists c20; iframe Hc0 Hh2
        ihave #Hev' := Hev
        iunfold eventsAt at Hev'
        icases Hev' with ⟨%ls, #Hls, %Hlslen, -⟩
        ihave %Hsl := ownSlice_len $$ Hls
        have Hlen0 : sint.Z v.Events'.len = 0 := by
          rw [Hcr.2] at Hlslen; simp at Hlslen; subst Hlslen; simp at Hsl; word
        wp_auto
        rw [show decide (sint.Z (W64 0) < sint.Z v.Events'.len) = false by simp [Hlen0]]
        wp_auto
        wp_for_post
        iframe HΦ Hdn Hx Hwg Hwstok resuming Hdefer Hclosing Hbl Houtcf Hdnf Hγt
        iexists rcv ++ [wr], nr
        simp only [named]
        iframe nextRev
        unfold wsRun
        iexists sent, C, bq, b, (null : Loc), t', cl, p0
        simp only [List.length_append, List.length_singleton]
        iframe Hcons Hprod Hauth Hbuf Hbwt Hretc Hc2 Hcur
        unfold sliceOwn
        iframe Hb Hbcap
        isplitr
        · ipureintro; omega
        isplitr
        · ipureintro; exact HC
        isplitl [Hbe]
        · iapply bufE_skip V P bq rcv.length p0
          iframe Hbe Hchn
        isplitl [Hrev]
        · iright
          isplitr
          · ipureintro; omega
          iexact Hrev
        isplitr
        · iexists hl0, c20
          iframe HiA Hh2A' Hrs
        iright; ipureintro; simp
    · have hne0 : rcv ≠ [] := by intro h; subst h; simp at hk Hkr; omega
      cases hcrr : r.created
      rotate_left
      · -- (D25) a created response after the lifetime's first: `run`'s half of `rev` with the whole
        irevert Hk
        simp only [hcrr, ↓reduceIte]
        iintro ⟨-, %rv, Hrv2⟩
        icases Hrev with (⟨%Hc, -⟩ | ⟨-, Hrev⟩)
        · exact absurd Hc.1 hk
        iexfalso
        iapply w64_ptsto_excl $$ [$Hrev $Hrv2]
      irevert Hk
      simp only [hcrr, Bool.false_eq_true, ↓reduceIte]
      iintro ⟨#Hns, #Hrf⟩
      have Hcr : r.created = false := hcrr
      have Hcreated : v.Created' = false := Hv.2.2.2.2.1.trans Hcr
      icases Hrev with (⟨%Hc, -⟩ | ⟨-, Hrev⟩)
      · exact absurd Hc.1 hk
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
      -- F3: the resume revision moves only forward (`issues/etcd-watch-resume-below-start-revision.md`)
      wp_bind (If _ _ _)
      iapply (wp_wand_r (Φ := fun x => iprop(⌜x = executeVal⌝ ∗ (∃ nr' : w64, nextRev_ptr ↦ nr' ∗
          ⌜(sint.Z nr < sint.Z (r.hdrRev + W64 1) ∧ nr' = r.hdrRev + W64 1) ∨
            (¬ sint.Z nr < sint.Z (r.hdrRev + W64 1) ∧ nr' = nr)⌝) ∗
          wr_ptr ↦ wr ∗
          structFieldRef etcdserverpb.ResponseHeader go!"Revision" v.Header' ↦{dq} r.hdrRev)))
      isplitl [nextRev wr Hhf]
      · wp_if_destruct
        · (try wp_auto)
          isplitr
          · first | itrivial | (ipureintro; rfl)
          iframe
          first | (iexists _; iframe) | skip
          ipureintro; left; exact ⟨by simpa using Hif, rfl⟩
        · (try wp_auto)
          isplitr
          · first | itrivial | (ipureintro; rfl)
          iframe
          first | (iexists _; iframe) | skip
          ipureintro; right; exact ⟨by simpa using Hif, rfl⟩
      iintro %x ⟨%Hx, ⟨%nr0, nextRev, %Hnr0⟩, wr, Hhf⟩
      subst Hx
      wp_auto
      wp_bind (If (Val #(decide (sint.Z (W64 0) < sint.Z v.Events'.len))) _ _)
      iapply (wp_wand_r (Φ := fun x => iprop(⌜x = executeVal⌝ ∗ ∃ nr' : w64,
          nextRev_ptr ↦ nr' ∗ wr_ptr ↦ wr ∗
          ⌜(r.events = [] ∧ nr' = nr0) ∨ (∃ e, r.events.getLast? = some e ∧ nr' = e.rev + W64 1)⌝)))
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
          ipureintro; right; refine ⟨e, ?_, rfl⟩
          rw [List.getLast?_eq_getElem?, ← He]
          congr 1
          rw [← Hlslen]; have h := Hsl.1; word
        · (try wp_auto)
          isplitr
          · first | itrivial | (ipureintro; rfl)
          iexists _
          iframe
          ipureintro; left; refine ⟨?_, rfl⟩
          rw [← List.length_eq_zero_iff, ← Hlslen]
          have : ¬ (0 < sint.Z v.Events'.len) := by simpa using Hif
          have h2 := Hsl.1; word
      iintro %x ⟨%Hx, %nr', nextRev, wr, %Hnr'⟩
      subst Hx
      wp_auto
      icases Hrr with (⟨%Hr, -, -⟩ | %Hr)
      · exact absurd Hr.1 hne0
      -- (D25) the resume revision after the response
      ihave %Hhl0e := mono_list_idx_agree P.γhi _ _ _ $$ HiB Hhl0
      subst Hhl0e
      ihave ⟨%h2A, #Hh2A, #Hw2⟩ := recvCmpl_at V P _ v r c20 $$ [Hcm Hc20']
      · iframe Hcm; simp only [Int.toNat_natCast]; iexact Hc20'
      ihave #Hrs' := resumeOk_step V P nr hiB c20 hiA h2A nr0 nr' r v HPws.2.1 HPws.2.2
          ⟨Hcr, Hv.2.2.2.2.2.2, Hv.2.2.2.2.2.1⟩ ⟨Hv.2.1, Hv.2.2.1, Hv.2.2.2.1⟩ Hnr0 Hnr' $$
          [Hrs Hok Hw2 Hrf]
      · iframe #
      simp only [Int.toNat_natCast] at *
      ihave #Hrsm' : iprop(∃ hl c2 : w64, monoListIdxOwn P.γhi (rcv.length + 1) hl ∗
          (⌜P.γ.cpl = false⌝ ∨ monoListIdxOwn P.γh2 (rcv.length + 1) c2) ∗
          resumeOk V P nr' hl c2) $$ []
      · iexists hiA, h2A
        iframe Hrs' HiA Hh2A
      wp_apply wp_slice_literal (V := Loc) [wr]
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      (try wp_auto)
      wp_apply wp_slice_append $$ [Hb Hbcap Hsl2] as %b' ⟨Hb, Hbcap, -⟩
      · iframe
      (try wp_auto)
      wp_for_post
      iframe HΦ Hdn Hx Hwg Hwstok resuming Hdefer Hclosing Hbl Houtcf Hdnf Hγt
      iexists rcv ++ [wr], nr'
      simp only [named]
      iframe nextRev
      unfold wsRun
      iexists sent, C, bq ++ [(rcv.length, wr)], b', rcf, t', cl, p0
      simp only [List.length_append, List.length_singleton, List.map_append, List.map_cons,
        List.map_nil]
      iframe Hcons Hprod Hauth Hbuf Hbwt Hretc Hcur Hc2 Hrsm'
      unfold sliceOwn
      iframe Hb Hbcap
      isplitr
      · ipureintro; omega
      isplitr
      · ipureintro; exact HC
      isplitl [Hbe Hhf Hback]
      · iapply bufE_snoc V P bq rcv.length wr p0
        iframe Hbe
        isplitl [Hhf Hback]
        · unfold recvLive
          iexists v, r, hiB, hiA
          simp only [Int.toNat_natCast]
          iframe Hwr Hev HiB HiA Hok Hcm
          isplitr
          · ipureintro; exact Hv
          isplitl [Hhf Hback]
          · iapply Hback; iexact Hhf
          simp only [hcrr, Bool.false_eq_true, ↓reduceIte]
          iframe Hns Hrf
        iapply chainE_refl P (rcv.length + 1) hiA
        iframe HiA
        icases Hh2A with (%H | #H)
        · ileft; ipureintro; exact H
        · iright; iexists _; iexact H
      isplitl [Hrev]
      · iright
        isplitr
        · ipureintro; omega
        iexact Hrev
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
    iintro ⟨#Hlb, -⟩
    -- (D25) resumed: the goroutine leaves its state in the lifetime's invariant
    (try wp_auto)
    wp_apply +noauto wp_resetBufWait $$ [Hbwt] as Hbwt
    · iframe
    wp_auto_lc 1
    wp_for_post
    (try wp_auto)
    iapply fupd_wp
    iinv Hlinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑lifeN) $$ Hlc1 Hi with Hi
    iunfold lifeSt at Hi
    icases Hi with (⟨Hγt2, Hmh⟩ | ⟨#Ht, -⟩)
    rotate_left
    · ihave %H := dghostVar_agree _ _ _ _ _ $$ Hγt Ht
      cases H
    imod dghostVar_update_halves true _ _ _ $$ Hγt Hγt2 with ⟨Hγt, -⟩
    imod dghostVar_persist _ _ _ $$ Hγt with #Hγt
    ihave Hwstok := (ghostMapElem_halves G.γws P.ws ()).2 $$ [Hwstok Hmh]
    · iframe
    imod Hclose $$ [Hcons Hprod Hauth Hc2 Hbuf Hb Hbcap Hbe Hrev Hretc Hrr Hbwt Hclosing Hbl Houtcf
      Hdnf Hx Hwstok] with -
    · inext
      iunfold lifeSt
      iright
      iframe Hγt
      iright
      isplitr
      · iexact Hlb
      ileft
      unfold resumeBody
      iexists k0, rv0, rcv, nr, bl, L.dc
      iframe Hclosing Hbl Hblok Houtcf Hdnf Hx Hwstok Hls0
      unfold wsRun
      iexists sent, C, bq, b, rcf, _, cl, p0
      iframe Hcons Hprod Hauth Hc2 Hbuf Hbe Hrev Hretc Hrr Hbwt Hcur Hrsm
      unfold sliceOwn
      iframe Hb Hbcap
      ipureintro; exact ⟨Hkr, HC⟩
    imodintro
    wp_apply +noauto wp_broadcast_chan_close $$ [Hdn] as #Hdnd
    · iframe Hdn; imodintro; unfold lifeQ; iframe #
    (try wp_auto)
    ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
    · iPkgInit
    iunfold wgDone at Hwg
    wp_apply wp_wgsWg_Done $$ [Hwg] as Htt
    · iexact Hwg
    iapply HΦ
    iexact Htt
  iapply BigAndL.bigAndL_nil.2
  itrivial
