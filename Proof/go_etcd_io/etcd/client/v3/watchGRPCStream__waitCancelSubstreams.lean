/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watchGRPCStream__waitCancelSubstreams.lean`. Lean-first
(no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__waitCancelSubstreams
public import Perennial.Spec.sync.WaitGroup__Add
public import Perennial.Spec.sync.WaitGroup__Wait
public import Perennial.Proof.sync.WaitGroupJoin
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.Results
public import Proof.go_etcd_io.etcd.client.v3.WatchApiLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

set_option maxHeartbeats 4000000 in
theorem watchGRPCStream.waitCancelSubstreams.wp_proof :
    watchGRPCStream.waitCancelSubstreams.spec (GF := GF) (hG := hG) := by
  intro V G callSl s l dq Pf stopc γst γS γh n
  wp_start as ⟨#HG, Hres, Hs, %HPf, #Hstop, Hsh, Htt, Hin⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave %Hlen := ownSlice_len $$ Hs
  iunfold wgsWgShared at Hsh
  icases Hsh with ⟨#HwgsS, #HinvSh, Hsha, Hu, %Hb⟩
  ihave Hsh : iprop(wgsWgShared (wgsF G.wgs go!"wg") γS γh n) $$ [Hsha Hu]
  · unfold wgsWgShared; iframe Hsha Hu; iframe #; ipureintro; exact Hb
  wp_auto
  imod wcj_init wg_ptr (wgsF G.wgs go!"wg") γS Hb $$ [$wg $HwgsS] with Hadd
  wp_apply chan.wp_make1 (V := Unit) as %dc %γd ⟨#Hdc, %-, Hdo⟩
  rename_i iv_ptr
  irename : (iv_ptr ↦ zero_val w64 : IProp GF) => iv
  -- the key to what the goroutines give back, and `donec`'s predicate
  imod dghostVar_alloc (GF := GF) () with ⟨%γk, Hkey⟩
  let Rall : IProp GF := iprop([∗list] ws ∈ l, wcOut V G (Pf ws) ∗
    wgsShareTok (wgsF G.wgs go!"wg") γS γh)
  let Qd : IProp GF := iprop(inv wcdN iprop(Rall ∨ ownTok γk))
  imod alloc_broadcast_chan (E := ⊤) Qd γd dc $$ Hdc Hdo with Hdb
  icases ownBroadcastChan_dup_unknown _ _ _ _ $$ Hdb with ⟨Hdb, #Hdu⟩
  ipersist w
  ipersist stopc
  ihave HI : iprop(∃ (k v : w64), "i" ∷ i_ptr ↦ k ∗ "iv" ∷ iv_ptr ↦ v ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (l.length : Int)⌝ ∗
      "Hadd" ∷ sync.tokJoin.ownAdder wcjN (wcjL γS) wg_ptr (sint.nat k)
        iprop([∗list] ws ∈ l.take (sint.nat k),
          wcOut V G (Pf ws) ∗ wgsShareTok (wgsF G.wgs go!"wg") γS γh) ∗
      "Hsh" ∷ wgsWgShared (wgsF G.wgs go!"wg") γS γh (n + sint.nat k) ∗ "Htt" ∷ threadTok ∗
      "Hin" ∷ ([∗list] ws ∈ l.drop (sint.nat k), wcIn V G (Pf ws))) $$ [i iv Hadd Hsh Htt Hin]
  · iexists W64 0, _
    simp only [named]
    have h0 : sint.nat (W64 0) = 0 := by word
    rw [h0]
    simp only [List.take_zero, List.drop_zero, Nat.add_zero]
    iframe i iv Hsh Htt Hin
    isplitr
    · ipureintro; constructor <;> word
    iapply sync.tokJoin.ownAdder_wand $$ [] Hadd
    iintro -
    iapply BigSepL.bigSepL_nil.2
    itrivial
  wp_for HI
  wp_if_destruct
  · have Hif' : sint.Z k < sint.Z s.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    have Hlt : sint.nat k < l.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, l[sint.nat k]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z s.len := ⟨Hk.1, by word⟩
    rw [ite_eq_left Hbnd]
    wp_apply wp_load_slice_index s (sint.Z k) l (DFrac.own 1) x Hk.1 $$ [Hs] as Hs
    · iframe; ipureintro; rw [← Hx]
    wp_apply sync.tokJoin.WaitGroup.wp_Add
      iprop(wcOut V G (Pf x) ∗ wgsShareTok (wgsF G.wgs go!"wg") γS γh) wcjN (wcjL γS) wg_ptr
      (sint.nat k) _ $$ [Hadd Htt] as ⟨Hadd, Hdone⟩
    · iframe
    imod wgsWg_mint _ _ _ _ $$ Hsh with ⟨Hsh, Hstok⟩
    rw [ite_eq_left Hbnd]
    wp_apply wp_load_slice_index s (sint.Z k) l (DFrac.own 1) x Hk.1 $$ [Hs] as Hs
    · iframe; ipureintro; rw [← Hx]
    have hxl : l[sint.nat k] = x := (List.getElem?_eq_some_iff.1 Hx).2
    have hdrop : l.drop (sint.nat k) = x :: l.drop (sint.nat k + 1) := by
      rw [List.drop_eq_getElem_cons Hlt, hxl]
    have htake : l.take (sint.nat k + 1) = l.take (sint.nat k) ++ [x] := by
      rw [List.take_add_one, Hx]; rfl
    irevert Hin
    rw [hdrop]
    iintro Hin
    icases BigSepL.bigSepL_cons.1 $$ Hin with ⟨Hxin, Hin⟩
    have HPx : (Pf x).ws = x := HPf x (List.mem_of_getElem? Hx)
    (try wp_auto)
    wp_apply wp_fork_tok_self $$ [Hdone Hstok Hxin] as Htt
    · -- the goroutine of `x`
      generalize Pf x = P at HPx ⊢
      subst HPx
      iunfold wcIn at Hxin
      icases Hxin with ⟨#HP, Hst⟩
      ihave #HP' := HP
      iunfold wsIs at HP'
      icases HP' with ⟨#Hro, -, #Houtc, -, #Hctx, -, %HPok, -⟩
      ihave #Hro' := Hro
      iunfold wrRO at Hro'
      icases Hro' with ⟨#Rctx, -⟩
      ihave #HPc := Hctx
      iNamedPrefix HPc "C"
      wp_auto
      wp_apply wp_with_defer
      iintro %defer Hdefer
      wp_auto
      ipersist ws
      ihave #HG' := HG
      iunfold isWGS at HG'
      icases HG' with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Fclosingc, -, -, -, -, -, #Hclb, -, -⟩
      ihave #Hspsc' := Houtc
      iunfold isSpsc at Hspsc'
      icases Hspsc' with ⟨#Hic, -⟩
      ihave %Hnn := isChan_not_null P.outc P.γ.spsc.chanName go_etcd_io.etcd.client.v3.WatchResponse $$ Hic
      icases Hst with (Hrb | ⟨#Hstp, Hsb⟩)
      · iunfold resumeBody at Hrb
        icases Hrb with ⟨%k0, %rv0, %rcv, %nr, %bl, %dc, Hrun, #Hls, Hcl, Hbl, #Hblok, Houtf, Hdnf,
          Hgx, Hel⟩
        wp_auto
        wp_apply +noauto CHDone as %dch %dγ #Hdn
        wp_auto
        wp_apply_core chan.wp_select_blocking
        iapply BigAndL.bigAndL_cons.2
        isplit
        · simp only [chan.blockingClausePre]
          iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch, dγ
          isplit
          · ipureintro; rfl
          isplit
          · iapply context.isContextDone_is_chan $$ Hdn
          iapply context.isContextDone_receive _ _ _ _ $$ Hdn
          iintro ⟨#HPD, #Hcc⟩
          wp_auto
          ipersist Hcl
          iunfold wsRun at Hrun
          icases Hrun with ⟨%sent, %C, %bq, %b, %rcf, %t, %cl, %p0, -, -, Hprod, -, -, -, -, -, -, -,
            Hrev, #Hrsm, Hretc, Hrr, -⟩
          wp_apply wp_spsc_close P.γ.spsc P.outc _ (fun _ => iprop(True)) sent $$ [$Houtc $Hprod]
          (try wp_auto)
          imod dghostVar_update true _ _ $$ Hgx with Hgx
          imod dghostVar_persist _ _ _ $$ Hgx with #Hgx
          wp_apply wp_wgsWg_Add_wcj wg_ptr (wgsF G.wgs go!"wg") γS γh _ $$ [Hdone Hstok]
            as ⟨HdB, Hstok⟩
          · iframe
          (try wp_auto)
          wp_bind (Fork _)
          iapply wp_wcj_fork wg_ptr (wgsF G.wgs go!"wg") γS _ _ _
          iframe HdB HwgsS
          isplitl [Hel]
          · inext
            iintro Hwd
            wp_apply wp_with_defer
            iintro %defer2 Hdefer2
            wp_auto
            wp_apply wp_bag_send $$ [Hel]
            · iframe Hclb
              unfold closingP
              iexact Hel
            (try wp_auto)
            wp_apply wp_wgsWg_Done $$ [Hwd] as Htt
            · iframe #; iframe
            (try wp_auto)
            first | iexact Htt | (iframe Htt; ipureintro; rfl)
          inext
          iintro Hdone
          wp_auto
          wp_apply sync.tokJoin.WaitGroup.wp_Done wcjN (wcjL γS) wg_ptr _
            $$ [Hdone Hstok Houtf Hrev Hretc Hrr Hdnf] as Htt
          · iframe Hdone Hstok
            iframe #
            unfold wcOut
            iright
            isplitr
            · unfold wsStopped; iframe #
            unfold stopBody
            ihave Hrv : iprop(∃ (q : Qp), wsReqF P.ws go!"rev" ↦{DFrac.own q} nr) $$ [Hrev]
            · icases Hrev with (⟨%Hkr, Hrev⟩ | ⟨-, Hrev⟩)
              · iexists _; rw [Hkr.2]; iexact Hrev
              · iexists 1; iexact Hrev
            icases Hrv with ⟨%q, Hrv⟩
            iexists rcf, q, nr, dc
            ihave #Hrs' : iprop(∃ hl c2 : w64, resumeOk V P nr hl c2) $$ []
            · icases Hrsm with ⟨%hl, %c2, -, -, #Hrs⟩
              iexists hl, c2
              iexact Hrs
            iframe Hretc Hrv Hdnf Hrs'
            isplitl [Houtf]
            · iright
              rw [show (chan.nil : GoChan) = null from rfl]
              iframe Houtf Hcc
            icases Hrr with (⟨%Hr, Hres, -⟩ | %Hr)
            · iright; iframe Hres; ipureintro; exact Hr.2.1
            · ileft; ipureintro; exact Hr.2
          (try wp_auto)
          first | iexact Htt | (iframe Htt; ipureintro; rfl)
        iapply BigAndL.bigAndL_cons.2
        isplit
        · simp only [chan.blockingClausePre]
          iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stopc, γst
          isplit
          · ipureintro; rfl
          isplit
          · iapply ownBroadcastChan_is_chan $$ Hstop
          iapply broadcast_chan_receive _ _ _ _ _ $$ Hstop
          iintro -
          wp_auto
          wp_apply sync.tokJoin.WaitGroup.wp_Done wcjN (wcjL γS) wg_ptr _
            $$ [Hdone Hstok Hrun Hcl Hbl Houtf Hdnf Hgx Hel] as Htt
          · iframe Hdone Hstok
            iframe #
            unfold wcOut
            ileft
            unfold resumeBody
            iexists k0, rv0, rcv, nr, bl, dc
            iframe
            iframe #
          (try wp_auto)
          first | iexact Htt | (iframe Htt; ipureintro; rfl)
        iapply BigAndL.bigAndL_nil.2
        itrivial
      · ihave #Hstp' := Hstp
        iunfold wsStopped at Hstp'
        icases Hstp' with ⟨#Hgx, #Hcl⟩
        wp_auto
        ihave #HErrU := CHErr $$ %Broadcast.Unknown
        wp_apply HErrU $$ [] as %err herr
        rename_i err
        cases err with
        | nil =>
          wp_auto
          wp_apply sync.tokJoin.WaitGroup.wp_Done wcjN (wcjL γS) wg_ptr _
            $$ [Hdone Hstok Hsb] as Htt
          · iframe Hdone Hstok
            iframe #
            unfold wcOut
            iright
            iframe Hsb Hstp
          (try wp_auto)
          first | iexact Htt | (iframe Htt; ipureintro; rfl)
        | ok ei =>
          irevert herr
          simp only [reduceCtorEq, ↓reduceIte]
          iintro ⟨#HPD, #Hcc⟩
          iunfold stopBody at Hsb
          icases Hsb with ⟨%rc, %q, %nr, %dc, Hoc, Hrc, Hret, Hrev, Hdnf⟩
          icases Hoc with (⟨Houtf, Hprod⟩ | ⟨Houtf, #Hcc0⟩)
          · wp_auto
            rw [decide_eq_false (show ¬ (P.outc = chan.nil) from Hnn)]
            wp_auto
            iunfold outcProd at Hprod
            icases Hprod with ⟨%sent, %C, Hprod, -, -⟩
            wp_apply wp_spsc_close P.γ.spsc P.outc _ (fun _ => iprop(True)) sent $$ [$Houtc $Hprod]
            (try wp_auto)
            wp_apply sync.tokJoin.WaitGroup.wp_Done wcjN (wcjL γS) wg_ptr _
              $$ [Hdone Hstok Houtf Hrc Hret Hrev Hdnf] as Htt
            · iframe Hdone Hstok
              iframe #
              unfold wcOut
              iright
              iframe Hstp
              unfold stopBody
              iexists rc, q, nr, dc
              iframe Hrc Hret Hrev Hdnf
              iright
              rw [show (chan.nil : GoChan) = null from rfl]
              iframe Houtf Hcc
            (try wp_auto)
            first | iexact Htt | (iframe Htt; ipureintro; rfl)
          · wp_auto
            wp_apply sync.tokJoin.WaitGroup.wp_Done wcjN (wcjL γS) wg_ptr _
              $$ [Hdone Hstok Houtf Hrc Hret Hrev Hdnf] as Htt
            · iframe Hdone Hstok
              iframe #
              unfold wcOut
              iright
              iframe Hstp
              unfold stopBody
              iexists rc, q, nr, dc
              iframe Hrc Hret Hrev Hdnf
              iright
              iframe Houtf Hcc0
            (try wp_auto)
            first | iexact Htt | (iframe Htt; ipureintro; rfl)
    wp_for_post
    iframe
    iexists k + W64 1, k
    simp only [named]
    have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    rw [hk1, htake]
    iframe i iv Hin Htt
    isplitr
    · ipureintro; constructor <;> word
    isplitl [Hadd]
    · iapply sync.tokJoin.ownAdder_wand $$ [] Hadd
      iintro ⟨H1, H2⟩
      iapply BigSepL.bigSepL_snoc.2
      iframe
    rw [show n + (sint.nat k + 1) = n + sint.nat k + 1 by omega]
    iframe
  -- the loop's end: a goroutine closes `donec` after the local join's `Wait`
  have hkl : sint.nat k = l.length := by
    have : ¬ sint.Z k < sint.Z s.len := by
      first | assumption | (intro h; apply Hif; simp [h])
    word
  rw [hkl, List.take_length, List.drop_length] at *
  ipersist donec
  (try wp_auto)
  wp_apply wp_fork $$ [Hadd Hdb]
  · wp_apply wp_with_defer
    iintro %defer Hdefer
    (try wp_auto)
    wp_apply sync.tokJoin.WaitGroup.wp_Wait wcjN (wcjL γS) wg_ptr l.length _ $$ [Hadd] as ⟨HP, -⟩
    · iframe #; iframe
    imod inv_alloc wcdN ⊤ iprop(Rall ∨ ownTok γk) $$ [HP] with #Hinv
    · inext; ileft; iexact HP
    (try wp_auto)
    wp_apply wp_broadcast_chan_close dc γd Qd $$ [$Hdb] as -
    · imodintro; iexact Hinv
    (try wp_auto)
    itrivial
  (try wp_auto)
  iapply HΦ
  iframe
  iexists γd, Qd
  iframe Hdu
  iintro Hlc #HQ
  simp only [Qd]
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ HQ with ⟨Hi, Hclose⟩
  imod lc_fupd_elim_later (E := ⊤ \ ↑wcdN) $$ Hlc Hi with Hi
  icases Hi with (HR | Hk2)
  · imod Hclose $$ [Hkey] with -
    · inext; iright; unfold ownTok; iexact Hkey
    imodintro
    iexact HR
  · iexfalso; iapply ownTok_excl; iframe Hk2; unfold ownTok; iexact Hkey

end proof

end EtcdGrove
end Perennial
