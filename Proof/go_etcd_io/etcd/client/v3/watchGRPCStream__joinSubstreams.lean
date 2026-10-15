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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem watchGRPCStream.joinSubstreams.wp_proof :
    watchGRPCStream.joinSubstreams.spec (GF := GF) (hG := hG) := by
  intro wgs m M s l dq1 dq2 dq3 dq4
  wp_start as ⟨Hsub, Hm, #HM, Hres, Hs, #Hl⟩
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (_ : List w64) (_ : Int) => iprop(∃ v : Loc, ws_ptr ↦ v))
    _ _ _ m M dq2 $$ Hm
  iintro %keys %Hkeys
  isplitl [ws]
  · iexists _; iexact ws
  isplitr
  · imodintro
    iintro %i %key %v ⟨%Hki, %Hmv⟩ ⟨%v0, Hws⟩
    wp_auto
    ihave #Hd := BigSepM.bigSepM_lookup (Φ := fun (_ : w64) ws => donecOf (GF := GF) ws) Hmv $$ HM
    iunfold donecOf at Hd
    icases Hd with ⟨%dc, %γ, %Qd, #Hdc, #Hbc⟩
    wp_auto
    ihave #Hch := ownBroadcastChan_is_chan _ _ _ _ $$ Hbc
    wp_bind (App (Val (chan.receive (go.GoType.StructType []))) _)
    iapply chan.wp_receive (V := Unit) dc γ $$ Hch
    iintro _
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hbc
    iintro ⟨-, -⟩
    wp_auto
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists _; iexact Hws
  iintro ⟨%v, ws⟩ Hm
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hs
  ihave HI : iprop(∃ (n : w64) (v : Loc), "i" ∷ i_ptr ↦ n ∗ "ws" ∷ ws_ptr ↦ v ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (l.length : Int)⌝) $$ [i ws]
  · iexists W64 0, _
    simp only [named]
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · have Hlt : sint.nat n < l.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, l[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z s.len := ⟨Hn.1, by word⟩
    rw [ite_eq_left Hbnd]
    wp_apply wp_load_slice_index s (sint.Z n) l dq4 x Hn.1 $$ [Hs] as Hs
    · iframe; ipureintro; rw [← Hx]
    ihave #Hx := BigSepL.bigSepL_lookup (Φ := fun _ ws => iprop(⌜ws = null⌝ ∨ donecOf (GF := GF) ws))
      Hx $$ Hl
    wp_if_destruct
    · -- a nil substream: skipped
      wp_for_post
      iframe
      iexists n + W64 1, null
      iframe
      ipureintro; constructor <;> word
    · icases Hx with (%Hxn | #Hd)
      · exact absurd Hxn ‹¬x = null›
      iunfold donecOf at Hd
      icases Hd with ⟨%dc, %γ, %Qd, #Hdc, #Hbc⟩
      wp_auto
      ihave #Hch := ownBroadcastChan_is_chan _ _ _ _ $$ Hbc
      wp_bind (App (Val (chan.receive (go.GoType.StructType []))) _)
      iapply chan.wp_receive (V := Unit) dc γ $$ Hch
      iintro _
      iapply broadcast_chan_receive _ _ _ _ _ $$ Hbc
      iintro ⟨-, -⟩
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, x
      iframe
      ipureintro; constructor <;> word
  · iapply HΦ
    iframe

end proof

end EtcdGrove
end Perennial
