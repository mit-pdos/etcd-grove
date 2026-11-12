/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watchGRPCStream__broadcastResponse.lean` (the watch slice's
unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__broadcastResponse

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
/-- The loop's state at the key `k`: done (sent or stopped) once the loop passed it. -/
def bcastAt (V : WEnv GF) (Pf : Loc → WsPrm GF) (Sf : Loc → List Loc) (Df : Loc → DnInfo GF) (γend : GName) (n : Nat) (wr : Loc)
    (keys : List w64) (i : Nat) (k : w64) (ws : Loc) : IProp GF :=
  if k ∈ keys.take i then iprop(sendDone (Pf ws) (Sf ws) wr (Df ws) γend n ∨ sendFail V (Pf ws) (Sf ws) wr (Df ws) γend n)
  else iprop(⌜(Pf ws).ws = ws⌝ ∗ sendCap1 V (Pf ws) (Sf ws) wr (Df ws) γend n)

theorem bcastAt_step (V : WEnv GF) (Pf : Loc → WsPrm GF) (Sf : Loc → List Loc) (Df : Loc → DnInfo GF) (γend : GName) (n : Nat) (wr : Loc) (keys : List w64) (M : GMap w64 Loc) (i : Nat)
    (key : w64) (v : Loc) (hk : keys[i]? = some key) (hnd : keys.Nodup) (hM : M !! key = some v) :
    ([∗map] k ↦ ws ∈ M, bcastAt (GF := GF) V Pf Sf Df γend n wr keys i k ws) ⊢
      (⌜(Pf v).ws = v⌝ ∗ sendCap1 V (Pf v) (Sf v) wr (Df v) γend n) ∗
        ((sendDone (Pf v) (Sf v) wr (Df v) γend n ∨ sendFail V (Pf v) (Sf v) wr (Df v) γend n) -∗
        [∗map] k ↦ ws ∈ M, bcastAt V Pf Sf Df γend n wr keys (i + 1) k ws) := by
  have htake : keys.take (i + 1) = keys.take i ++ [key] := by
    rw [List.take_add_one, hk]; rfl
  have hnot : key ∉ keys.take i := by
    have h := hnd
    rw [← List.take_append_drop (i + 1) keys, htake, List.append_assoc] at h
    have h2 := (List.nodup_append.1 h).2.2
    intro hmem
    exact h2 key hmem key (by simp) rfl
  refine (BigSepM.bigSepM_delete (Φ := bcastAt V Pf Sf Df γend n wr keys i) hM).1.trans ?_
  unfold bcastAt
  rw [if_neg hnot]
  refine sep_mono_right (wand_intro ?_)
  refine (sep_mono_left (BigSepM.bigSepM_mono (Ψ := bcastAt V Pf Sf Df γend n wr keys (i + 1)) ?_)).trans ?_
  · intro k x hkx
    have hne : k ≠ key := by
      intro e; rw [e] at hkx
      rw [show Std.delete M key = GMap.delete key M from rfl] at hkx
      simp [gmap_get?_eq] at hkx
    unfold bcastAt
    rw [htake]
    simp only [List.mem_append, List.mem_singleton, hne, _root_.or_false]
    exact .rfl
  refine sep_comm.1.trans ?_
  refine (sep_mono_left ?_).trans (BigSepM.bigSepM_delete (Φ := bcastAt V Pf Sf Df γend n wr keys (i + 1)) hM).2
  unfold bcastAt
  rw [if_pos (by rw [htake]; simp)]

theorem watchGRPCStream.broadcastResponse.wp_proof :
    watchGRPCStream.broadcastResponse.spec (GF := GF) (hG := hG) := by
  intro V wgs wr m M dq1 dq2 Pf Sf Df γend n
  wp_start as ⟨Hsub, Hmap, Hauth, Hcaps⟩
  (try wp_auto)
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ v : Loc, ws_ptr ↦ v ∗
      wr_ptr ↦ wr ∗ ⌜0 ≤ i⌝ ∗ monoNatAuthOwn γend 1 n ∗
      [∗map] k ↦ x ∈ M, bcastAt V Pf Sf Df γend n wr keys i.toNat k x))
    _ _ _ m M dq2 $$ Hmap
  iintro %keys ⟨%Hkmem, %Hklen, %Hknd⟩
  isplitl [ws wr Hcaps Hauth]
  · iexists _
    iframe
    ipureintro; exact Int.le_refl 0
  isplitr
  · imodintro
    iintro %i %key %v ⟨%Hki, %Hmv⟩ ⟨%v0, Hws, Hwr, %Hi, Hauth, HM⟩
    icases bcastAt_step V Pf Sf Df γend n wr keys M i.toNat key v Hki Hknd Hmv $$ HM with ⟨⟨%HPws, Hcap⟩, HM⟩
    iunfold sendCap1 at Hcap
    icases Hcap with ⟨#Hws', Hprod, Hel, Hdc⟩
    generalize hP : Pf v = P at HPws ⊢
    generalize hS : Sf v = sent
    generalize hD : Df v = d
    subst HPws
    ihave #Hws'' := Hws'
    iunfold wsIs at Hws''
    icases Hws'' with ⟨-, #Hrecvc, -, #Hspsc, -⟩
    iunfold dnCap at Hdc
    icases Hdc with ⟨Hdc, #Href⟩
    iunfold donecAt at Hdc
    icases Hdc with ⟨Hdonec, #Hdn⟩
    have Hi1 : (i + 1).toNat = i.toNat + 1 := by omega
    wp_auto_lc 3
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, P.recvc,
        P.γr.chanName, wr
      isplit
      · ipureintro; exact ⟨rfl, rfl⟩
      isplit
      · ihave #H := Hspsc
        unfold isSspsc
        icases H with ⟨$, -⟩
      iapply sspsc_send_au P.γr P.recvc _ _ sent wr _ $$ Hspsc [$Hlc1 $Hlc2 $Hlc3] [Hprod Hel]
      · iframe
      inext
      iintro Hprod
      (try wp_auto)
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _
      iframe
      isplitr
      · ipureintro; omega
      rw [Hi1]
      iapply HM
      ileft
      iunfold sendDone
      iframe Hprod
      iunfold dnCap
      iframe Href
      iunfold donecAt
      iframe
      try iexact Hdn
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, d.dc, d.γ
      isplit
      · ipureintro; rfl
      isplit
      · iapply ownBroadcastChan_is_chan $$ Hdn
      iapply broadcast_chan_receive $$ Hdn
      iintro ⟨#HdnQ, -⟩
      ihave #HdnD := Href $$ HdnQ Hauth
      (try wp_auto)
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _
      iframe
      isplitr
      · ipureintro; omega
      rw [Hi1]
      iapply HM
      iright
      iunfold sendFail
      iframe Hprod Hel HdnD
      iunfold dnCap
      iframe Href
      iunfold donecAt
      iframe
      try iexact Hdn
    iapply BigAndL.bigAndL_nil.2
    itrivial
  iintro ⟨%v, Hws, Hwr, %Hi, Hauth, HM⟩ Hmap
  (try wp_auto)
  iapply HΦ
  iframe
  iapply BigSepM.bigSepM_mono (Ψ := fun _ x => iprop(sendDone (GF := GF) (Pf x) (Sf x) wr (Df x) γend n ∨
    sendFail V (Pf x) (Sf x) wr (Df x) γend n)) ?_ $$ HM
  intro k x hkx
  unfold bcastAt
  have hk : k ∈ keys.take (GMap.size M : Int).toNat := by
    rw [Int.toNat_natCast, ← Hklen, List.take_length]
    exact (Hkmem k).2 (by rw [gmap_get?_eq] at hkx; simp [hkx])
  rw [if_pos hk]

end proof

end EtcdGrove
end Perennial
