/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leaseCache__LockRange.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__LockRange
public import Spec.go_etcd_io.etcd.client.v3.leasing.inRange
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseCacheWrite

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
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leaseCache.LockRange.wp_proof (hinRange : inRange.spec (GF := GF) (hG := hG)) :
    leaseCache.LockRange.spec (GF := GF) (hG := hG) := by
  intro lc γ pfx X Qr b e
  wp_start as ⟨#Hlc, #Hpeek, #Hstep⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold isLeaseCache
  icases Hlc with ⟨#Hguard, #Hcl⟩
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hwl, HP⟩
  icases leaseCacheInv_open_w $$ HP with ⟨%st, Hown, HX, Hinst, Hready, #Hfacts, %Hwf, Hclose⟩
  unfold lcPeek
  icases Hpeek $$ %st %_ HX with ⟨HX, #HQr⟩
  by_cases hnil : st.emap = map.nil
  · have hemp := Hwf.empty_if_nil hnil
    icases lcOwn_emap_acc $$ Hown with ⟨Hentries, Hemap, Hown⟩
    wp_auto
    ihave Hown := Hown $$ Hentries Hemap
    rw [hnil]
    wp_func_lits
    wp_auto
    imod Hclose $$ %st %Hwf Hfacts Hinst Hready Hown HX with HP
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl $HP]
    iapply HΦ
    iexists st, [], []
    iframe #
    rw [show (zero_val GoSlice) = slice.nil from rfl]
    isplitl
    · iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    isplitl
    · iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro
    refine ⟨List.nodup_nil, fun k => ?_, rfl⟩
    simp [hemp]
  · icases lcOwn_ents_emap_acc $$ Hown with ⟨Hentries, Hemap, Hents, Hown⟩
    wp_auto
    unfold emapOwn
    simp only [hnil, ↓reduceIte]
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range (fun (keys : List GoString) (i : Int) => iprop(∃ (ents : GMap GoString LeaseEntry)
        (sl : GoSlice) (cs : List GoChan) (kv : GoString) (lv : Loc),
        "Hents" ∷ ([∗map] _k ↦ en ∈ ents, entryOwn en (DFrac.own 1)) ∗
        "ret" ∷ ret_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* cs ∗ "Hcap" ∷ ownSliceCap GoChan sl (DFrac.own 1) ∗
        "Hcs" ∷ ([∗list] c ∈ cs, waitcClose c) ∗
        "k" ∷ k_ptr ↦ kv ∗ "li" ∷ li_ptr ↦ lv ∗ "Hbegin" ∷ begin_ptr ↦ b ∗ "Hend" ∷ end_ptr ↦ e ∗
        "%Hi" ∷ ⌜0 ≤ i⌝ ∗ "%Hw" ∷ ⌜WaitcOnlyEnts st ents⌝ ∗
        "%Hlen" ∷ ⌜cs.length = ((keys.take i.toNat).filter (fun k => leaseInRange k b e)).length⌝))
      $$ Hemap
    iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
    isplitl [Hents ret li k begin «end»]
    · iexists st.entries, _, [], _, _
      simp only [named]
      iframe
      rw [show (zero_val GoSlice) = slice.nil from rfl]
      isplitl
      · iapply ownSlice_nil
      isplitl
      · iapply ownSliceCap_nil
      isplitl
      · iapply BigSepL.bigSepL_nil.2; iempintro
      ipureintro
      exact ⟨Int.le_refl _, waitcOnlyEnts_refl st, by simp⟩
    isplitr
    · imodintro
      iintro %i %key %v ⟨%Hkey, %Hv⟩ HP
      iNamed HP
      wp_auto
      wp_apply hinRange
      have htake : List.take (i + 1).toNat keys = List.take i.toNat keys ++ [key] := by
        rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
      cases hr : leaseInRange key b e
      · wp_auto
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists ents, sl, cs, key, v
        simp only [named]
        iframe
        ipureintro
        refine ⟨by omega, Hw, ?_⟩
        rw [htake, List.filter_append]
        simp [hr, Hlen]
      · wp_auto
        wp_apply chan.wp_make1 (V := Unit) as %ch %γch ⟨#Hch, %_, Hoc⟩
        imod alloc_broadcast_chan waitQ γch ch $$ Hch Hoc with Hpend
        icases pending_unknown $$ Hpend with ⟨Hpend, #Hunk⟩
        obtain ⟨e0, he0, hli0⟩ : ∃ e0, st.entries !! key = some e0 ∧ e0.li = v := by
          simp only [LeaseCacheSt.lis, GMap.lookup_fmap, Option.map_eq_some_iff] at Hv
          exact Hv
        have hw0 := Hw key
        rw [he0] at hw0
        obtain ⟨e1, he1⟩ : ∃ e1, ents !! key = some e1 := by
          cases h1 : ents !! key with
          | none => rw [h1] at hw0; simp at hw0
          | some e1 => exact ⟨e1, rfl⟩
        obtain ⟨e0', he0', hli1, -⟩ := waitcOnlyEnts_lookup Hw he1
        rw [he0] at he0'; cases he0'
        icases (BigSepM.bigSepM_insert_acc he1) $$ Hents with ⟨He, Hents⟩
        unfold entryOwn
        icases He with ⟨%hnn, Hr, Hrev, Hwc, Hresp, #Hw0⟩
        rw [hli1, hli0]
        wp_auto
        wp_apply wp_slice_literal (V := GoChan) [ch]
        isplitr
        · ipureintro; rfl
        iintro %sl2 ⟨Hsl2, -⟩
        (try wp_auto)
        wp_apply wp_slice_append $$ [Hsl Hcap Hsl2] as %sl' ⟨Hsl, Hcap, -⟩
        · iframe
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        ihave Hents := Hents $$ %{ e1 with waitc := ch } [Hr Hrev Hwc Hresp]
        · have hresp : respOwn (GF := GF) { e1 with waitc := ch } (DFrac.own 1) =
            respOwn e1 (DFrac.own 1) := rfl
          rw [hresp]
          simp only
          rw [hli1, hli0]
          iframe
          isplitl
          · ipureintro; rw [← hli0, ← hli1]; exact hnn
          unfold waitcOk; iexists γch; iexact Hunk
        iexists _, sl', cs ++ [ch], key, v
        simp only [named]
        iframe
        isplitl
        · iapply BigSepL.bigSepL_singleton.2
          unfold waitcClose; iexists γch; iexact Hpend
        ipureintro
        refine ⟨by omega, waitcOnlyEnts_insert Hw key e1 he1 ch, ?_⟩
        rw [htake, List.filter_append]
        simp [hr, Hlen]
    iintro HP Hemap
    iNamed HP
    rw [show ((GMap.size st.lis : Nat) : Int).toNat = keys.length by omega, List.take_length] at Hlen
    wp_auto
    ihave Hown := Hown $$ %ents %(sameLis_of_waitc Hw) Hentries [Hemap] Hents
    · iexact Hemap
    unfold lcWaitcStep
    imod Hstep $$ %st %_ %(waitcOnly_ents Hw) HX with HX
    have hwf' := wf_sameLis Hwf (sameLis_of_waitc Hw) rfl rfl rfl
    ihave #Hfacts' := lcFacts_same pfx st _ (sameFacts_of_waitc Hw) $$ Hfacts
    ihave Hready : monoNatAuthOwn γ.ready 1 ({ st with entries := ents } : LeaseCacheSt).readyN
      $$ [Hready]
    · rw [show ({ st with entries := ents } : LeaseCacheSt).readyN = st.readyN from rfl]
      iexact Hready
    ihave Hinst : monoListAuthOwn γ.inst 1 ({ st with entries := ents } : LeaseCacheSt).installed
      $$ [Hinst]
    · rw [show ({ st with entries := ents } : LeaseCacheSt).installed = st.installed from rfl]
      iexact Hinst
    imod Hclose $$ %_ %hwf' Hfacts' Hinst Hready Hown HX with HP
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl $HP]
    iapply HΦ
    iexists st, keys.filter (fun k => leaseInRange k b e), cs
    iframe
    iframe #
    ipureintro
    refine ⟨Hknodup.filter _, fun k => ?_, Hlen⟩
    rw [List.mem_filter, Hkset]
    simp only [LeaseCacheSt.lis, GMap.lookup_fmap, Option.isSome_map]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨ent, hent⟩ := Option.isSome_iff_exists.1 h1
      exact ⟨ent, hent, h2⟩
    · rintro ⟨ent, hent, h2⟩
      exact ⟨by simp [hent], h2⟩

end proof

end leasing
end EtcdGrove
end Perennial
