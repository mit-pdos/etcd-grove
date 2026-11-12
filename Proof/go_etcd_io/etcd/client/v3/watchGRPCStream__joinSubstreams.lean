/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watchGRPCStream__joinSubstreams.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__joinSubstreams

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

theorem watchGRPCStream.joinSubstreams.wp_proof :
    watchGRPCStream.joinSubstreams.spec (GF := GF) (hG := hG) := by
  intro wgs m M s l dq1 dq2 dq3 dq4 U Df
  wp_start as ⟨Hsub, Hm, Hres, Hs, HU, %HMU⟩
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ v : Loc, ws_ptr ↦ v ∗
      ⌜0 ≤ i⌝ ∗ ([∗map] w ↦ _u ∈ U, donecAt w (Df w)) ∗
      □ (∀ (X : w64) (ws : Loc), ⌜X ∈ keys.take i.toNat ∧ M !! X = some ws⌝ → □ (Df ws).Q)))
    _ _ _ m M dq2 $$ Hm
  iintro %keys ⟨%Hkmem, %Hklen, %Hknd⟩
  isplitl [ws HU]
  · iexists _
    iframe
    isplitr
    · ipureintro; exact Int.le_refl 0
    imodintro
    iintro %X %ws %H
    exfalso; simp at H
  isplitr
  · imodintro
    iintro %i %key %v ⟨%Hki, %Hmv⟩ ⟨%v0, Hws, %Hi, HU, #Hacc⟩
    have hUv : U !! v = some () := HMU.1 key v Hmv
    icases (BigSepM.bigSepM_lookup_acc (Φ := fun w (_ : Unit) => donecAt (GF := GF) w (Df w)) hUv).1
      $$ HU with ⟨Hd, Hback⟩
    iunfold donecAt at Hd
    icases Hd with ⟨Hdc, #Hbc⟩
    wp_auto
    ihave #Hch := ownBroadcastChan_is_chan _ _ _ _ $$ Hbc
    wp_bind (App (Val (chan.receive (go.GoType.StructType []))) _)
    iapply chan.wp_receive (V := Unit) (Df v).dc (Df v).γ $$ Hch
    iintro _
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hbc
    iintro ⟨#HQ, -⟩
    wp_auto
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists _
    iframe Hws
    isplitr
    · ipureintro; omega
    isplitl [Hback Hdc]
    · iapply Hback
      iunfold donecAt
      iframe Hdc Hbc
    imodintro
    iintro %X %ws %HXX
    obtain ⟨HX, HXm⟩ := HXX
    have htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hki]; rfl
    rw [htake] at HX
    rcases List.mem_append.1 HX with h | h
    · iapply Hacc
      ipureintro; exact ⟨h, HXm⟩
    · simp at h; subst h
      rw [Hmv] at HXm; cases HXm
      iexact HQ
  iintro ⟨%v, ws, %Hi, HU, #Hacc⟩ Hm
  ihave #HaccM : iprop(□ ∀ (X : w64) (ws : Loc), ⌜M !! X = some ws⌝ → □ (Df ws).Q) $$ []
  · imodintro
    iintro %X %ws' %HX
    have hk : X ∈ keys.take (GMap.size M : Int).toNat := by
      rw [Int.toNat_natCast, ← Hklen, List.take_length]
      exact (Hkmem X).2 (by simp [HX])
    iapply Hacc
    ipureintro; exact ⟨hk, HX⟩
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hs
  ihave HI : iprop(∃ (n : w64) (v : Loc), "i" ∷ i_ptr ↦ n ∗ "ws" ∷ ws_ptr ↦ v ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (l.length : Int)⌝ ∗
      "HU" ∷ ([∗map] w ↦ _u ∈ U, donecAt w (Df w)) ∗
      "#Hl1" ∷ □ (∀ ws : Loc, ⌜ws ∈ l.take (sint.nat n) ∧ ws ≠ null⌝ → □ (Df ws).Q))
      $$ [i ws HU]
  · iexists W64 0, _
    simp only [named]
    iframe
    isplitr
    · ipureintro; constructor <;> word
    imodintro
    iintro %ws' %H
    exfalso
    have h0 : sint.nat (W64 0) = 0 := by word
    rw [h0] at H; simp at H
  wp_for HI
  wp_if_destruct
  · have Hif' : sint.Z n < sint.Z s.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    have Hlt : sint.nat n < l.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, l[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z s.len := ⟨Hn.1, by word⟩
    rw [ite_eq_left Hbnd]
    wp_apply wp_load_slice_index s (sint.Z n) l dq4 x Hn.1 $$ [Hs] as Hs
    · iframe; ipureintro; rw [← Hx]
    have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    have htake : l.take (sint.nat n + 1) = l.take (sint.nat n) ++ [x] := by
      rw [List.take_add_one, Hx]; rfl
    wp_if_destruct
    · -- a nil substream: skipped
      wp_for_post
      iframe
      iexists n + W64 1, null
      iframe
      isplitr
      · ipureintro; constructor <;> word
      imodintro
      iintro %ws' %H12
      obtain ⟨H1, H2⟩ := H12
      rw [hn1, htake] at H1
      rcases List.mem_append.1 H1 with h | h
      · iapply Hl1
        ipureintro; exact ⟨h, H2⟩
      · simp at h; subst h; exact absurd rfl H2
    · have hUx : U !! x = some () := HMU.2 x (List.mem_of_getElem? Hx) ‹¬x = null›
      icases (BigSepM.bigSepM_lookup_acc (Φ := fun w (_ : Unit) => donecAt (GF := GF) w (Df w)) hUx).1
        $$ HU with ⟨Hd, Hback⟩
      iunfold donecAt at Hd
      icases Hd with ⟨Hdc, #Hbc⟩
      wp_auto
      ihave #Hch := ownBroadcastChan_is_chan _ _ _ _ $$ Hbc
      wp_bind (App (Val (chan.receive (go.GoType.StructType []))) _)
      iapply chan.wp_receive (V := Unit) (Df x).dc (Df x).γ $$ Hch
      iintro _
      iapply broadcast_chan_receive _ _ _ _ _ $$ Hbc
      iintro ⟨#HQ, -⟩
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, x
      iframe
      isplitr
      · ipureintro; constructor <;> word
      isplitl [Hback Hdc]
      · iapply Hback
        iunfold donecAt
        iframe Hdc Hbc
      imodintro
      iintro %ws' %H12
      obtain ⟨H1, H2⟩ := H12
      rw [hn1, htake] at H1
      rcases List.mem_append.1 H1 with h | h
      · iapply Hl1
        ipureintro; exact ⟨h, H2⟩
      · simp at h; subst h; iexact HQ
  · have Hnot : ¬ (sint.Z n < sint.Z s.len) := by
      first | exact Hif | exact (fun h => Hif (by simp [h]))
    have hn : sint.nat n = l.length := by word
    (try simp only [Hnot, decide_false])
    (try cleanup_bool_decide)
    (try rw [if_pos (by simp)])
    (try wp_auto)
    iapply HΦ
    iframe
    iframe #
    imodintro
    iintro %ws' %H
    iapply Hl1
    ipureintro; rw [hn, List.take_length]; exact H

end proof

end EtcdGrove
end Perennial
