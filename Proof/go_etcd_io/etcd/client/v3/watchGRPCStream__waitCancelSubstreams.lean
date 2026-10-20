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

theorem watchGRPCStream.waitCancelSubstreams.wp_proof :
    watchGRPCStream.waitCancelSubstreams.spec (GF := GF) (hG := hG) := by
  intro wgs s stopc dq
  wp_start as ⟨Hres, Hs⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave %Hlen := ownSlice_len $$ Hs
  have Hs0 : s.len = W64 0 := by simp at Hlen; word
  wp_auto
  imod sync.init_WaitGroup (sync.join.wgjN.@"wg") wg_ptr $$ wg with ⟨%γwg, #Hwg, Hctr, Hwait⟩
  imod sync.join.init wg_ptr γwg $$ [Hwg Hctr Hwait] with Hadd
  · iframe #; iframe
  wp_apply chan.wp_make1 (V := Unit) as %dc %γd ⟨#Hdc, %-, Hdo⟩
  imod alloc_broadcast_chan (E := ⊤) iprop(True) γd dc $$ Hdc Hdo with Hdb
  ihave HI : iprop(∃ n : w64, "i" ∷ i_ptr ↦ n ∗ "%Hn" ∷ ⌜n = W64 0⌝) $$ [i]
  · iexists _; iframe; ipureintro; rfl
  wp_for HI
  wp_if_destruct
  · exfalso; subst Hn; rw [Hs0] at Hif; exact absurd Hif (by decide)
  icases ownBroadcastChan_open _ _ _ _ $$ Hdb with ⟨%γch, #Hint, Hp⟩
  ihave Hdb := ownBroadcastChan_close dc γd iprop(True) .Pending γch $$ [Hp]
  · iframe #; iexact Hp
  ihave #Hdu := ownBroadcastChan_close dc γd iprop(True) .Unknown γch $$ []
  · iframe #
  ipersist donec
  wp_apply wp_fork $$ [Hadd Hdb]
  · wp_apply wp_with_defer
    iintro %defer Hdefer
    (try wp_auto)
    wp_apply (sync.join.WaitGroup.wp_Wait_of sync.WaitGroup.wp_Wait iprop(True) (W32 0) wg_ptr)
      $$ [$Hadd] as ⟨-, -⟩
    (try wp_auto)
    wp_apply wp_broadcast_chan_close dc γd iprop(True) $$ [$Hdb] as -
    · imodintro; itrivial
    (try wp_auto)
    itrivial
  iapply HΦ
  iframe
  iexists γd
  iexact Hdu

end proof

end EtcdGrove
end Perennial
