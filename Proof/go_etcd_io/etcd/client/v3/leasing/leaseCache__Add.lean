/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leaseCache__Add.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__Add
public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseKey__get
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leaseCache.Add.wp_proof (hget : leaseKey.get.spec (GF := GF) (hG := hG)) :
    leaseCache.Add.spec (GF := GF) (hG := hG) := by
  intro lc γ pfx X Qr key e0 opv o Q
  wp_start as ⟨#Hlc, #Hpeek, #Hready, Hresp, #Hfacts0, %He0, #Hop, Hstep⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold isLeaseCache closedChInit
  icases Hlc with ⟨#Hguard, ⟨%ch, #Hch, #Hwc⟩⟩
  iunfold respOwn at Hresp
  icases Hresp with ⟨%Hrnn, Hhd, #Hehd, Hkvs, Hsl, Hcap, Hkv, Hmore, Hcount⟩
  ihave #Hehd' := Hehd
  iunfold hdrFull at Hehd'
  icases Hehd' with ⟨%Hehnn, #He1, #He2, #He3, #He4, #He5⟩
  wp_auto
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hlk, HP⟩
  icases leaseCacheInv_open_w $$ HP with
    ⟨%st, Hown, HX, Hinst, Hrd, #Hfacts, %Hwf, Hclose⟩
  unfold lcPeek
  icases Hpeek $$ %st %_ HX with ⟨HX, #HQr⟩
  rw [lcOwn_def]
  icases Hown with ⟨Hentries, Hemap, Hrv, Hrmap, Hhdr, #HhdrOk, Hents, #Hfrozen⟩
  wp_join iprop(structFieldRef leaseCache go!"header" lc ↦
      (if decide (st.header = null ∨ sint.Z st.hm.revision < sint.Z e0.hm.revision) then e0.hdr
        else st.header) ∗ resp_ptr ↦ e0.resp ∗ lc_ptr ↦ lc ∗
      structFieldRef etcdserverpb.RangeResponse go!"Header" e0.resp ↦ e0.hdr) at next
      with [Hhdr Hhd resp lc] as ⟨Hhdr, resp, lc, Hhd⟩
  · by_cases hh : st.header = null
    · rw [hh]
      wp_auto
      simp only [true_or, decide_true, ↓reduceIte]
      iframe
    · unfold headerOk
      simp only [hh, ↓reduceIte]
      rw [hdrFull_def st.header]
      icases HhdrOk with ⟨-, -, -, #Hs3, -, -⟩
      wp_auto
      rw [decide_eq_false hh]
      wp_auto
      wp_if_destruct
      · simp only [Hif, _root_.or_true, decide_true, ↓reduceIte]
        iframe
      · simp only [Hif, _root_.or_false, decide_false, ↓reduceIte]
        iframe
  unfold leaseCacheReady
  ihave %Hle := monoNatLbOwn_valid $$ Hrd Hready
  have hmap : st.emap ≠ map.nil := by
    intro h; unfold LeaseCacheSt.readyN at Hle; rw [h] at Hle; simp at Hle
  unfold emapOwn
  simp only [hmap, ↓reduceIte]
  wp_apply wp_mapInsert $$ [$Hemap] as Hemap
  irename «$r0» => Hli
  generalize hli0 : «$r0_ptr» = li at *
  have hlk : ({ e0 with li := li, waitc := ch } : LeaseEntry).lk =
      { response' := e0.resp, rev' := e0.hm.revision, waitc' := ch } := by
    simp only [LeaseEntry.lk, He0.1]
  ihave Hresp : respOwn ({ e0 with li := li, waitc := ch } : LeaseEntry) (DFrac.own 1) $$
      [Hhd Hkvs Hsl Hcap Hkv Hmore Hcount]
  · rw [respOwn_def]; simp only; iframe; iframe #; ipureintro; exact Hrnn
  rw [← hlk]
  wp_apply hget $$ [$Hli $Hresp $Hop] as %ret ⟨Hli, Hresp, Hret⟩
  -- the new entry's resources, and the freshness of its `*leaseKey`
  ihave %Hlinn := typedPointsto_not_null $$ Hli
  icases (leaseKey_struct li _ _ Hlinn).2 $$ Hli with ⟨Hr, Hrev, Hwcf⟩
  icases keep_pure (entries_fresh st.entries li _) $$ [$Hents $Hrev] with ⟨%Hfr1, Hents, Hrev⟩
  icases keep_pure (frozen_fresh st.frozen li _) $$ [$Hfrozen $Hrev] with ⟨%Hfr2, -, Hrev⟩
  ihave Hentry : entryOwn ({ e0 with li := li, waitc := ch } : LeaseEntry) (DFrac.own 1) $$
      [Hr Hrev Hwcf Hresp]
  · rw [entryOwn_def]
    simp only
    iframe
    iframe #
    ipureintro; exact Hlinn
  imod entries_insert_freeze st.entries key _ $$ [$Hents $Hentry] with ⟨Hents, Hold⟩
  imod Hstep $$ %st %li %ch HX with ⟨HX, HQ⟩
  imod monoListAuthOwn_update_app [(key, li)] $$ Hinst with ⟨Hinst, -⟩
  obtain ⟨hemap', -, -, hinst'⟩ := add_other key ({ e0 with li := li, waitc := ch } : LeaseEntry) st
  have hready' : (st.add key ({ e0 with li := li, waitc := ch } : LeaseEntry)).readyN =
      st.readyN := by
    unfold LeaseCacheSt.readyN; rw [hemap']
  ihave #Hfacts' := add_facts pfx key ({ e0 with li := li, waitc := ch } : LeaseEntry) st $$
    [$Hfacts]
  · unfold entryFacts; iexact Hfacts0
  imod Hclose $$ %(st.add key ({ e0 with li := li, waitc := ch } : LeaseEntry))
    %(add_wf key _ st Hwf Hfr1 Hfr2 Hlinn hmap) Hfacts' [Hinst] [Hrd]
    [Hentries Hemap Hrv Hrmap Hhdr Hents Hold] HX with HP
  · rw [hinst']; iexact Hinst
  · rw [hready']; iexact Hrd
  · iapply lcOwn_add_intro lc st key _ hmap
    iframe
    iframe #
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk $HP]
  iapply HΦ
  iexists st
  iframe
  iframe #

end proof

end leasing
end EtcdGrove
end Perennial
