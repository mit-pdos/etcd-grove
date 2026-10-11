/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leaseCache__Delete.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__Delete
public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__delete
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseCacheLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leaseCache.Delete.wp_proof (hdel : leaseCache.delete.spec (GF := GF) (hG := hG)) :
    leaseCache.Delete.spec (GF := GF) (hG := hG) := by
  intro lc γ pfx X Qr key h hm Q
  wp_start as ⟨#Hlc, #Hpeek, #Hh, Hstep⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold isLeaseCache
  icases Hlc with ⟨#Hguard, #Hcl⟩
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hlk, HP⟩
  icases leaseCacheInv_open_w $$ HP with ⟨%st, Hown, HX, Hinst, Hready, #Hfacts, %Hwf, Hclose⟩
  unfold lcPeek
  icases Hpeek $$ %st %_ HX with ⟨HX, #HQr⟩
  wp_apply hdel $$ [$Hown $Hh] as ⟨%h', Hown⟩
  · ipureintro; exact Hwf
  imod Hstep $$ %st %h' HX with ⟨HX, HQ⟩
  have hli : ∀ e : LeaseEntry, (e.del h' hm).li = e.li := fun e => by
    unfold LeaseEntry.del; split <;> rfl
  have hmo := modify_other key (fun e => e.del h' hm) st
  have hready : (st.modify key (fun e => e.del h' hm)).readyN = st.readyN := by
    unfold LeaseCacheSt.readyN; rw [hmo.1]
  ihave #Hfacts' := modify_facts pfx key (fun e => e.del h' hm) st (fun e => by
    unfold LeaseEntry.del; split <;> exact ⟨rfl, rfl, rfl⟩) $$ Hfacts
  imod Hclose $$ %(st.modify key (fun e => e.del h' hm))
    %(modify_wf key _ st hli Hwf) Hfacts' [Hinst] [Hready] Hown HX with HP
  · rw [hmo.2.2.2.2.2.2]; iexact Hinst
  · rw [hready]; iexact Hready
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk $HP]
  iapply HΦ
  iexists st
  iframe
  iframe #

end proof

end leasing
end EtcdGrove
end Perennial
