/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/urlPicker__pick.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.urlPicker__pick

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.urlPicker.pick.wp_proof :
    rafthttp.urlPicker.pick.spec (GF := GF) (hG := hG) := by
  intro pk P 
  wp_start as #Hpk
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold pickerOk at Hpk
  wp_apply sync.Mutex.wp_Lock _ (pickerInv pk P) $$ [$Hpk] as ⟨Hlocked, Hinv⟩
  iunfold pickerInv at Hinv
  icases Hinv with ⟨%sl, %us, %i, Hurls, #Hus, Hi, %Hok⟩
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hus
  obtain ⟨u, Hu⟩ : ∃ u, us[sint.nat i]? = some u := ⟨_, List.getElem?_eq_getElem (by word)⟩
  rw [if_pos (by word)]
  icases ownSlice_elem_acc (sint.Z i) u sl DFrac.discard us Hok.1 Hu $$ Hus with ⟨#Hue, -⟩
  wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [$Hpk $Hlocked Hurls Hi]
  · inext
    iunfold pickerInv
    iexists sl, us, i
    iframe
    iframe #
    ipureintro; exact Hok
  iapply HΦ
  ipureintro; exact Hok.2.2 u (List.mem_of_getElem? Hu)

end proof

end EtcdGrove
end Perennial
