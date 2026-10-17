/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watchGRPCStream__closeSubstream.lean` (the watch slice's
unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__closeSubstream
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__sendCloseSubstream
public import Proof.go_etcd_io.raft.v3.FrameH

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
theorem nilOut_found (l : List Loc) (ws : Loc) (n : Nat) (hpre : ∀ j, j < n → l[j]? ≠ some ws)
    (hn : l[n]? = some ws) : nilOut l ws = l.set n null := by
  unfold nilOut
  rw [List.findIdx?_eq_some_iff_getElem.2 ?_]
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.1 hn
  refine ⟨hlt, by simp, fun j hj => ?_⟩
  have := hpre j hj
  rw [List.getElem?_eq_getElem (by omega)] at this
  simpa using this

theorem nilOut_none (l : List Loc) (ws : Loc) (hall : ∀ j, j < l.length → l[j]? ≠ some ws) :
    nilOut l ws = l := by
  unfold nilOut
  rw [List.findIdx?_eq_none_iff.2 ?_]
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have := hall j hj
  rw [List.getElem?_eq_getElem hj] at this
  simpa using this

set_option hygiene false in
/-- The code after the `select` on `ws.initReq.retc <- ws.outc` (closing `ws.outc` or forking `sendCloseSubstream`, then the `substreams`/`resuming` removal), for the `select`'s three ways out: `retc` nil (`default`), and with `retc` live the send done and `default`. -/
local macro "close_rest" : tactic => `(tactic| (
    (try wp_auto)
    cases e with
    | nil =>
      (try wp_auto)
      wp_if_destruct
      · (try wp_auto)
        wp_if_destruct
        · rename_i ig
          irename : (ig ↦ zero_val w64 : IProp GF) => gi
          ihave %Hsll := ownSlice_len $$ Hs
          ihave IH : iprop(∃ (n v0 : w64), "i" ∷ i_ptr ↦ n ∗ "gi" ∷ ig ↦ v0 ∗
              "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (l.length : Int) ∧
                ∀ j, j < sint.nat n → l[j]? ≠ some P.ws⌝) $$ [i gi]
          · iexists W64 0, _
            simp only [named]
            iframe
            ipureintro
            refine ⟨by word, by word, fun j hj => absurd hj (by simp)⟩
          wp_for IH
          (try wp_auto)
          wp_if_destruct
          · have Hc : sint.Z n < sint.Z s.len := by
              first | assumption | exact of_decide_eq_true (go.intoVal_inj Hif)
            have Hlt : sint.nat n < l.length := by word
            obtain ⟨x, Hx⟩ : ∃ x, l[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
            have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z s.len := ⟨Hn.1, by word⟩
            rw [ite_eq_left Hbnd]
            wp_apply wp_load_slice_index s (sint.Z n) l (DFrac.own 1) x Hn.1 $$ [Hs] as Hs
            · iframe; ipureintro; rw [← Hx]
            (try wp_auto)
            rw [ite_eq_left Hbnd]
            wp_apply wp_load_slice_index s (sint.Z n) l (DFrac.own 1) x Hn.1 $$ [Hs] as Hs
            · iframe; ipureintro; rw [← Hx]
            (try wp_auto)
            wp_if_destruct
            · -- found: set to nil, return
              (try wp_auto)
              rw [ite_eq_left Hbnd]
              wp_apply wp_store_slice_index s (sint.Z n) l null $$ [Hs] as Hs
              · iframe; ipureintro; constructor <;> word
              (try wp_auto)
              wp_for_post
              iapply HΦ
              rw [nilOut_found l P.ws (sint.nat n) Hn.2.2 Hx]
              iframe
            · (try wp_auto)
              wp_for_post
              iframe
              iexists n + W64 1, n
              simp only [named]
              iframe
              ipureintro
              refine ⟨by word, by word, fun j hj => ?_⟩
              rcases Nat.lt_succ_iff_lt_or_eq.1 (show j < sint.nat n + 1 by word) with h | h
              · exact Hn.2.2 j h
              · subst h; rw [Hx]; intro h'; cases h'; contradiction
          · -- the end: no place held `ws`
            have Hc : ¬ sint.Z n < sint.Z s.len := by
              first | assumption | (intro h; apply Hif; simp [h])
            (try wp_auto)
            (try rw [decide_eq_false Hc, if_pos (decide_eq_true rfl)])
            (try wp_auto)
            iapply HΦ
            rw [nilOut_none l P.ws (fun j hj => Hn.2.2 j (by have := Hsll; word))]
            iframe
        · (try wp_auto)
          wp_apply wp_mapDelete $$ [$(frameH `Hmap)] as Hmap
          (try wp_auto)
          iapply HΦ
          iframe
      · iunfold outcProd at Hprod
        icases Hprod with ⟨%sent, %C, Hprod, -, -⟩
        (try wp_auto)
        wp_apply wp_spsc_close P.γ.spsc P.outc _ (fun _ => iprop(True)) sent $$ [$(frameH `Hspsc) $(frameH `Hprod)]
        (try wp_auto)
        wp_if_destruct
        · rename_i ig
          irename : (ig ↦ zero_val w64 : IProp GF) => gi
          ihave %Hsll := ownSlice_len $$ Hs
          ihave IH : iprop(∃ (n v0 : w64), "i" ∷ i_ptr ↦ n ∗ "gi" ∷ ig ↦ v0 ∗
              "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (l.length : Int) ∧
                ∀ j, j < sint.nat n → l[j]? ≠ some P.ws⌝) $$ [i gi]
          · iexists W64 0, _
            simp only [named]
            iframe
            ipureintro
            refine ⟨by word, by word, fun j hj => absurd hj (by simp)⟩
          wp_for IH
          (try wp_auto)
          wp_if_destruct
          · have Hc : sint.Z n < sint.Z s.len := by
              first | assumption | exact of_decide_eq_true (go.intoVal_inj Hif)
            have Hlt : sint.nat n < l.length := by word
            obtain ⟨x, Hx⟩ : ∃ x, l[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
            have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z s.len := ⟨Hn.1, by word⟩
            rw [ite_eq_left Hbnd]
            wp_apply wp_load_slice_index s (sint.Z n) l (DFrac.own 1) x Hn.1 $$ [Hs] as Hs
            · iframe; ipureintro; rw [← Hx]
            (try wp_auto)
            rw [ite_eq_left Hbnd]
            wp_apply wp_load_slice_index s (sint.Z n) l (DFrac.own 1) x Hn.1 $$ [Hs] as Hs
            · iframe; ipureintro; rw [← Hx]
            (try wp_auto)
            wp_if_destruct
            · -- found: set to nil, return
              (try wp_auto)
              rw [ite_eq_left Hbnd]
              wp_apply wp_store_slice_index s (sint.Z n) l null $$ [Hs] as Hs
              · iframe; ipureintro; constructor <;> word
              (try wp_auto)
              wp_for_post
              iapply HΦ
              rw [nilOut_found l P.ws (sint.nat n) Hn.2.2 Hx]
              iframe
            · (try wp_auto)
              wp_for_post
              iframe
              iexists n + W64 1, n
              simp only [named]
              iframe
              ipureintro
              refine ⟨by word, by word, fun j hj => ?_⟩
              rcases Nat.lt_succ_iff_lt_or_eq.1 (show j < sint.nat n + 1 by word) with h | h
              · exact Hn.2.2 j h
              · subst h; rw [Hx]; intro h'; cases h'; contradiction
          · -- the end: no place held `ws`
            have Hc : ¬ sint.Z n < sint.Z s.len := by
              first | assumption | (intro h; apply Hif; simp [h])
            (try wp_auto)
            (try rw [decide_eq_false Hc, if_pos (decide_eq_true rfl)])
            (try wp_auto)
            iapply HΦ
            rw [nilOut_none l P.ws (fun j hj => Hn.2.2 j (by have := Hsll; word))]
            iframe
        · (try wp_auto)
          wp_apply wp_mapDelete $$ [$(frameH `Hmap)] as Hmap
          (try wp_auto)
          iapply HΦ
          iframe
    | ok e0 =>
      (try wp_auto)
      ihave #HErrU := HErr $$ %Broadcast.Unknown
      wp_apply HErrU $$ [] as %err herr
      cases err with
      | nil =>
        (try wp_auto)
        icases typedPointsto_not_null_dup _ _ _ $$ «$v0» with ⟨Hh0, %Hhnn⟩
        wp_apply wp_fork $$ [Hprod Hh0 «$a1»]
        · wp_apply wp_sendCloseSubstream V P wgs «$a1_ptr» _ $$ [$(frameH `Hws) $(frameH `Hprod) $(frameH `«$a1») $(frameH `Hh0)]
          · iframe Hse
            ipureintro
            exact ⟨Hhnn, rfl, rfl, rfl, rfl⟩
          itrivial
        (try wp_auto)
        wp_if_destruct
        · rename_i ig
          irename : (ig ↦ zero_val w64 : IProp GF) => gi
          ihave %Hsll := ownSlice_len $$ Hs
          ihave IH : iprop(∃ (n v0 : w64), "i" ∷ i_ptr ↦ n ∗ "gi" ∷ ig ↦ v0 ∗
              "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (l.length : Int) ∧
                ∀ j, j < sint.nat n → l[j]? ≠ some P.ws⌝) $$ [i gi]
          · iexists W64 0, _
            simp only [named]
            iframe
            ipureintro
            refine ⟨by word, by word, fun j hj => absurd hj (by simp)⟩
          wp_for IH
          (try wp_auto)
          wp_if_destruct
          · have Hc : sint.Z n < sint.Z s.len := by
              first | assumption | exact of_decide_eq_true (go.intoVal_inj Hif)
            have Hlt : sint.nat n < l.length := by word
            obtain ⟨x, Hx⟩ : ∃ x, l[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
            have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z s.len := ⟨Hn.1, by word⟩
            rw [ite_eq_left Hbnd]
            wp_apply wp_load_slice_index s (sint.Z n) l (DFrac.own 1) x Hn.1 $$ [Hs] as Hs
            · iframe; ipureintro; rw [← Hx]
            (try wp_auto)
            rw [ite_eq_left Hbnd]
            wp_apply wp_load_slice_index s (sint.Z n) l (DFrac.own 1) x Hn.1 $$ [Hs] as Hs
            · iframe; ipureintro; rw [← Hx]
            (try wp_auto)
            wp_if_destruct
            · -- found: set to nil, return
              (try wp_auto)
              rw [ite_eq_left Hbnd]
              wp_apply wp_store_slice_index s (sint.Z n) l null $$ [Hs] as Hs
              · iframe; ipureintro; constructor <;> word
              (try wp_auto)
              wp_for_post
              iapply HΦ
              rw [nilOut_found l P.ws (sint.nat n) Hn.2.2 Hx]
              iframe
            · (try wp_auto)
              wp_for_post
              iframe
              iexists n + W64 1, n
              simp only [named]
              iframe
              ipureintro
              refine ⟨by word, by word, fun j hj => ?_⟩
              rcases Nat.lt_succ_iff_lt_or_eq.1 (show j < sint.nat n + 1 by word) with h | h
              · exact Hn.2.2 j h
              · subst h; rw [Hx]; intro h'; cases h'; contradiction
          · -- the end: no place held `ws`
            have Hc : ¬ sint.Z n < sint.Z s.len := by
              first | assumption | (intro h; apply Hif; simp [h])
            (try wp_auto)
            (try rw [decide_eq_false Hc, if_pos (decide_eq_true rfl)])
            (try wp_auto)
            iapply HΦ
            rw [nilOut_none l P.ws (fun j hj => Hn.2.2 j (by have := Hsll; word))]
            iframe
        · (try wp_auto)
          wp_apply wp_mapDelete $$ [$(frameH `Hmap)] as Hmap
          (try wp_auto)
          iapply HΦ
          iframe
      | ok e1 =>
        (try wp_auto)
        wp_if_destruct
        · (try wp_auto)
          wp_if_destruct
          · rename_i ig
            irename : (ig ↦ zero_val w64 : IProp GF) => gi
            ihave %Hsll := ownSlice_len $$ Hs
            ihave IH : iprop(∃ (n v0 : w64), "i" ∷ i_ptr ↦ n ∗ "gi" ∷ ig ↦ v0 ∗
                "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (l.length : Int) ∧
                  ∀ j, j < sint.nat n → l[j]? ≠ some P.ws⌝) $$ [i gi]
            · iexists W64 0, _
              simp only [named]
              iframe
              ipureintro
              refine ⟨by word, by word, fun j hj => absurd hj (by simp)⟩
            wp_for IH
            (try wp_auto)
            wp_if_destruct
            · have Hc : sint.Z n < sint.Z s.len := by
                first | assumption | exact of_decide_eq_true (go.intoVal_inj Hif)
              have Hlt : sint.nat n < l.length := by word
              obtain ⟨x, Hx⟩ : ∃ x, l[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
              have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z s.len := ⟨Hn.1, by word⟩
              rw [ite_eq_left Hbnd]
              wp_apply wp_load_slice_index s (sint.Z n) l (DFrac.own 1) x Hn.1 $$ [Hs] as Hs
              · iframe; ipureintro; rw [← Hx]
              (try wp_auto)
              rw [ite_eq_left Hbnd]
              wp_apply wp_load_slice_index s (sint.Z n) l (DFrac.own 1) x Hn.1 $$ [Hs] as Hs
              · iframe; ipureintro; rw [← Hx]
              (try wp_auto)
              wp_if_destruct
              · -- found: set to nil, return
                (try wp_auto)
                rw [ite_eq_left Hbnd]
                wp_apply wp_store_slice_index s (sint.Z n) l null $$ [Hs] as Hs
                · iframe; ipureintro; constructor <;> word
                (try wp_auto)
                wp_for_post
                iapply HΦ
                rw [nilOut_found l P.ws (sint.nat n) Hn.2.2 Hx]
                iframe
              · (try wp_auto)
                wp_for_post
                iframe
                iexists n + W64 1, n
                simp only [named]
                iframe
                ipureintro
                refine ⟨by word, by word, fun j hj => ?_⟩
                rcases Nat.lt_succ_iff_lt_or_eq.1 (show j < sint.nat n + 1 by word) with h | h
                · exact Hn.2.2 j h
                · subst h; rw [Hx]; intro h'; cases h'; contradiction
            · -- the end: no place held `ws`
              have Hc : ¬ sint.Z n < sint.Z s.len := by
                first | assumption | (intro h; apply Hif; simp [h])
              (try wp_auto)
              (try rw [decide_eq_false Hc, if_pos (decide_eq_true rfl)])
              (try wp_auto)
              iapply HΦ
              rw [nilOut_none l P.ws (fun j hj => Hn.2.2 j (by have := Hsll; word))]
              iframe
          · (try wp_auto)
            wp_apply wp_mapDelete $$ [$(frameH `Hmap)] as Hmap
            (try wp_auto)
            iapply HΦ
            iframe
        · iunfold outcProd at Hprod
          icases Hprod with ⟨%sent, %C, Hprod, -, -⟩
          (try wp_auto)
          wp_apply wp_spsc_close P.γ.spsc P.outc _ (fun _ => iprop(True)) sent $$ [$(frameH `Hspsc) $(frameH `Hprod)]
          (try wp_auto)
          wp_if_destruct
          · rename_i ig
            irename : (ig ↦ zero_val w64 : IProp GF) => gi
            ihave %Hsll := ownSlice_len $$ Hs
            ihave IH : iprop(∃ (n v0 : w64), "i" ∷ i_ptr ↦ n ∗ "gi" ∷ ig ↦ v0 ∗
                "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (l.length : Int) ∧
                  ∀ j, j < sint.nat n → l[j]? ≠ some P.ws⌝) $$ [i gi]
            · iexists W64 0, _
              simp only [named]
              iframe
              ipureintro
              refine ⟨by word, by word, fun j hj => absurd hj (by simp)⟩
            wp_for IH
            (try wp_auto)
            wp_if_destruct
            · have Hc : sint.Z n < sint.Z s.len := by
                first | assumption | exact of_decide_eq_true (go.intoVal_inj Hif)
              have Hlt : sint.nat n < l.length := by word
              obtain ⟨x, Hx⟩ : ∃ x, l[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
              have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z s.len := ⟨Hn.1, by word⟩
              rw [ite_eq_left Hbnd]
              wp_apply wp_load_slice_index s (sint.Z n) l (DFrac.own 1) x Hn.1 $$ [Hs] as Hs
              · iframe; ipureintro; rw [← Hx]
              (try wp_auto)
              rw [ite_eq_left Hbnd]
              wp_apply wp_load_slice_index s (sint.Z n) l (DFrac.own 1) x Hn.1 $$ [Hs] as Hs
              · iframe; ipureintro; rw [← Hx]
              (try wp_auto)
              wp_if_destruct
              · -- found: set to nil, return
                (try wp_auto)
                rw [ite_eq_left Hbnd]
                wp_apply wp_store_slice_index s (sint.Z n) l null $$ [Hs] as Hs
                · iframe; ipureintro; constructor <;> word
                (try wp_auto)
                wp_for_post
                iapply HΦ
                rw [nilOut_found l P.ws (sint.nat n) Hn.2.2 Hx]
                iframe
              · (try wp_auto)
                wp_for_post
                iframe
                iexists n + W64 1, n
                simp only [named]
                iframe
                ipureintro
                refine ⟨by word, by word, fun j hj => ?_⟩
                rcases Nat.lt_succ_iff_lt_or_eq.1 (show j < sint.nat n + 1 by word) with h | h
                · exact Hn.2.2 j h
                · subst h; rw [Hx]; intro h'; cases h'; contradiction
            · -- the end: no place held `ws`
              have Hc : ¬ sint.Z n < sint.Z s.len := by
                first | assumption | (intro h; apply Hif; simp [h])
              (try wp_auto)
              (try rw [decide_eq_false Hc, if_pos (decide_eq_true rfl)])
              (try wp_auto)
              iapply HΦ
              rw [nilOut_none l P.ws (fun j hj => Hn.2.2 j (by have := Hsll; word))]
              iframe
          · (try wp_auto)
            wp_apply wp_mapDelete $$ [$(frameH `Hmap)] as Hmap
            (try wp_auto)
            iapply HΦ
            iframe
  ))

set_option maxHeartbeats 2000000 in
theorem watchGRPCStream.closeSubstream.wp_proof
    (wp_sendCloseSubstream : watchGRPCStream.sendCloseSubstream.spec (GF := GF) (hG := hG)) :
    watchGRPCStream.closeSubstream.spec (GF := GF) (hG := hG) := by
  intro V wgs ws id e dq1 dq2 dq3 m M s l
  wp_start as ⟨Hcl, Hid, Hce, #Hse, Hsub, Hmap, Hres, Hs⟩
  iunfold closingBody at Hcl
  icases Hcl with ⟨%P, %rc, %HPws, #Hws, Hprod, Hrc, Hret, Hclosing⟩
  subst HPws
  ihave #Hws' := Hws
  iunfold wsIs at Hws'
  icases Hws' with ⟨#Hro, #Houtc, -, -, #Hspsc, -, -, #Hctx, #Hbag, %Hok⟩
  iunfold wrRO at Hro
  icases Hro with ⟨#Hctxf, -⟩
  ihave #Hctx1 := Hctx
  iNamed Hctx1
  ihave #Hctx2 := Hctx
  icases Hret with (%Hrc0 | ⟨%Hrc1, Hres0⟩)
  · subst Hrc0
    wp_auto_lc 2
    wp_apply_core chan.wp_select_nonblocking_nil
    isplit
    · iapply BigAndL.bigAndL_cons.2
      isplit
      · iright
        iapply chan.nilClausePre_send (V := Loc) (t := go.GoType.ChannelType go.ChanDir.sendrecv go_etcd_io.etcd.client.v3.WatchResponse.ty) null P.outc _ rfl
      iapply BigAndL.bigAndL_nil.2
      itrivial
    close_rest
  · subst Hrc1
    wp_auto_lc 2
    wp_apply_core chan.wp_select_nonblocking
    isplit
    · iapply BigAndL.bigAndL_cons.2
      isplit
      · simp only [chan.nonblockingClausePre]
        iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, P.retc, P.γret, P.outc
        isplit
        · ipureintro; exact ⟨rfl, rfl⟩
        isplit
        · iapply is_bag_is_chan $$ Hbag
        iapply blocking_send_implies_nonblocking
        iapply bag_send_au $$ [$Hlc1 $Hlc2] Hbag [Hres0]
        · iunfold retcP
          iunfold retcRes at Hres0
          iexists P.γ
          iframe Hspsc Hres0
        inext
        close_rest
      iapply BigAndL.bigAndL_nil.2
      itrivial
    close_rest

end proof

end EtcdGrove
end Perennial
