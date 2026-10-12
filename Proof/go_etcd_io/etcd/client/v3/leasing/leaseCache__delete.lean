/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leaseCache__delete.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__delete
public import Spec.go_etcd_io.etcd.client.v3.leasing.copyHeader
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

theorem leaseCache.delete.wp_proof (hcopy : copyHeader.spec (GF := GF) (hG := hG)) :
    leaseCache.delete.spec (GF := GF) (hG := hG) := by
  intro lc st key h hm
  wp_start as ⟨Hown, %Hwf, #Hh⟩
  rw [lcOwn_def]
  icases Hown with ⟨Hentries, Hemap, Hrv, Hrmap, Hhdr, #HhdrOk, Hents, #Hfrozen⟩
  wp_auto
  wp_apply wp_entries_lookup st _ key Hwf $$ [$Hemap] as Hemap
  cases hk : st.entries !! key with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    wp_auto
    iapply HΦ
    iexists null
    rw [modify_none key _ st hk, lcOwn_def]
    iframe
    iframe #
  | some e =>
    have hli : e.li ≠ null := Hwf.li_ne key e hk
    simp only [Option.map_some, Option.getD_some]
    icases (BigSepM.bigSepM_insert_acc hk) $$ Hents with ⟨He, Hback⟩
    ihave #Hok := headerOk_of_hdrFull h hm $$ Hh
    rw [entryOwn_def, respOwn_def, hdrFull_def e.hdr, hdrFull_def h]
    icases He with ⟨%-, Hr, Hrev, Hwc, ⟨%Hrnn, Hhd, #Hehd, Hkvs, Hsl, Hcap, Hkv, Hmore, Hcount⟩, #Hw⟩
    rw [decide_eq_false hli]
    icases Hh with ⟨%Hhnn, #Hh1, #Hh2, #Hh3, #Hh4, #Hh5⟩
    icases Hehd with ⟨%Hehnn, #He1, #He2, #He3, #He4, #He5⟩
    wp_auto
    wp_if_destruct
    · wp_apply hcopy $$ [$Hok] as %h' Hh'
      icases Hh' with (%Hc | ⟨%-, #Hh'⟩)
      · exact absurd Hc.1 Hhnn
      iapply HΦ
      iexists h'
      iapply lcOwn_modify_intro lc st key (fun e => e.del h' hm) e _ hk (fun e => by
        unfold LeaseEntry.del; split <;> rfl)
      iframe
      iframe #
      iapply Hback
      unfold LeaseEntry.del
      rw [ite_eq_left Hif, entryOwn_def, respOwn_def]
      simp only [List.map_nil]
      iframe
      iframe #
      isplitr
      · ipureintro; exact hli
      isplitr
      · ipureintro; exact Hrnn
      isplitl
      · iapply ownSlice_nil
      isplitl
      · iapply ownSliceCap_nil
      iapply BigSepL.bigSepL_nil.2
      iempintro
    · iapply HΦ
      iexists null
      have hdel : ∀ h', e.del h' hm = e := fun h' => by unfold LeaseEntry.del; rw [ite_eq_right Hif]
      iapply lcOwn_modify_intro lc st key (fun e => e.del null hm) e _ hk (fun e => by
        unfold LeaseEntry.del; split <;> rfl)
      iframe
      iframe #
      simp only [hdel]
      iapply Hback
      rw [entryOwn_def, respOwn_def, hdrFull_def e.hdr]
      iframe
      iframe #
      ipureintro; exact ⟨hli, Hrnn, Hehnn⟩

end proof

end leasing
end EtcdGrove
end Perennial
