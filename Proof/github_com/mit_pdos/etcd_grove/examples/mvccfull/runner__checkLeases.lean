/- Lean-first (no Rocq counterpart). The proof of `runner.checkLeases`: Draft, to come.

The outline: as mvccrand's `writer.checkLeases` over `lessorW` (`GetLease` through
`isLessor`'s clause or `lessor.GetLease.spec`, the owner's items `pendItems σ.log []` matching the
model's last state; `Leases`'s count against the live set; `Lookup`, `Lease.Keys`, `sort.Strings`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__checkLeases
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.history__snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__GetLease
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Leases
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Lookup
public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__Keys
public import Perennial.Spec.sort.Strings
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.CheckLeasesLemmas
public import Proof.go_etcd_io.etcd.server.v3.lease.LeaseOwnLeases

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option maxHeartbeats 2000000 in
theorem runner.checkLeases.wp_proof
    (wp_snapshot : history.snapshot.spec (GF := GF) (hG := hG))
    (wp_GetLease : lease.lessor.GetLease.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_Leases : lease.lessor.Leases.spec (GF := GF) (hG := hG))
    (wp_Lookup : lease.lessor.Lookup.spec (GF := GF) (hG := hG))
    (wp_Keys : lease.Lease.Keys.spec (GF := GF) (hG := hG))
    (wp_Strings : sort.Strings.spec (GF := GF) (hG := hG)) :
    runner.checkLeases.spec (GF := GF) (hG := hG) := by
  intro _ _ x ks cfg wr h γh ops i mp m f v qw nw k hlog
  wp_start as ⟨#Hctx, Hrd, #Hlb, Hc, Htok⟩
  ihave #Hctx2 := Hctx
  iunfold writerCtx at Hctx2
  icases Hctx2 with ⟨#Hrn, -, -, -, -, -, #Hlpkg, -, %Hkl, -, -, -, -, -, -, -, -, %Hcfg⟩
  ihave #Hrn2 := Hrn
  iunfold rnCtx at Hrn2
  icases Hrn2 with ⟨#Hpkg, #Hpm, #Hrk, -, #HH, #Hhist, -⟩
  iunfold runnerH at HH
  iunfold runnerKeys at Hrk
  icases Hrk with ⟨%keys, #Hkeys, #Hksl, %Hks⟩
  iunfold memCore at Hc
  icases Hc with ⟨Hid, Hhook, Hhok, Hpath, Hbe, Hle, Hkvf, Hrevf, Hcmpf, Hlsl, %Hvle, HincW,
    Hopen, Hmb, #Hhis, Hrds, Hbk, HlW, %HU⟩
  icases Hlsl with ⟨%lsl, Hlf, Hlsv, Hlcap⟩
  iunfold lessorW at HlW
  icases HlW with ⟨%rd, %r, #Hlpkg2, #Hlinv, #Hlcfg, #Hguard, #Hrevoc, #Hlok, Hlrd, Hlo, Hrvk, Hever,
    #Hreq, Hrdo, Hdel, Hlbe, Hrb, %Hrecs, Hstop, #Hpool⟩
  -- the model: the history's state at the member's revision
  obtain ⟨e, he, hM⟩ := hist_rev_match ks Hks.1 ops hlog v.ops Hvle
  have hpi : pendItems (σOf ks ops v.ops).log [] = leaseItemsOf (stateAfter (σOf ks ops v.ops).log) := by
    rw [pendItems_nil]
  generalize hIdef : pendItems (σOf ks ops v.ops).log [] = I at hpi
  wp_auto
  wp_apply (wp_snapshot h γh (histAt ks ops v.ops)) $$ [$Hrd $Hlb]
    as %s ⟨Hrd, %ms, %Hs, %Hpre, %Hcap, #Hlb', #Hms, #Hst⟩
  ihave %Hmlen : ⌜ms.length = Hs.length⌝ $$ [Hst]
  · iunfold statesP at Hst; icases Hst with ⟨%H, -⟩; ipureintro; exact H
  ihave %Hsl := ownSlice_len $$ Hms
  have hrl : revAfter ks ops v.ops < (histAt ks ops v.ops).length :=
    (List.getElem?_eq_some_iff.1 he).1
  have hrl' : (histAt ks ops v.ops).length ≤ Hs.length := Hpre.1.length_le
  have hHs : Hs[revAfter ks ops v.ops]? = some e := by
    obtain ⟨t, ht⟩ := Hpre.1; rw [← ht, List.getElem?_append_left hrl]; exact he
  have hr63 : (revAfter ks ops v.ops : Int) < 2 ^ 63 := by
    have h1 := Hsl.1; have : sint.nat s.len = (sint.Z s.len).toNat := rfl
    have : sint.Z s.len < 2 ^ 63 := by word
    omega
  have hrZ : sint.Z (W64 (revAfter ks ops v.ops : Int)) = revAfter ks ops v.ops := by word
  have hb : 0 ≤ sint.Z (W64 (revAfter ks ops v.ops : Int)) ∧
      sint.Z (W64 (revAfter ks ops v.ops : Int)) < sint.Z s.len := by
    rw [hrZ]; have h1 := Hsl.1; have : sint.nat s.len = (sint.Z s.len).toNat := rfl; omega
  simp only [hb, _root_.and_self, ↓reduceIte]
  have hi : (sint.Z (W64 (revAfter ks ops v.ops : Int))).toNat = revAfter ks ops v.ops := by
    rw [hrZ]; omega
  have hidx : revAfter ks ops v.ops < ms.length := by omega
  wp_apply wp_load_slice_index s (sint.Z (W64 (revAfter ks ops v.ops : Int))) ms DFrac.discard
    (ms[revAfter ks ops v.ops]'hidx) hb.1 $$ [Hms] as -
  · iframe #; ipureintro; rw [hi]; exact List.getElem?_eq_getElem hidx
  have hz : (ms.zip Hs)[revAfter ks ops v.ops]? = some (ms[revAfter ks ops v.ops]'hidx, e) := by
    rw [List.getElem?_zip_eq_some]
    exact ⟨List.getElem?_eq_getElem hidx, hHs⟩
  ihave #Hm : (ms[revAfter ks ops v.ops]'hidx ↦$□ e.1 : IProp GF) $$ [Hst]
  · iunfold statesP at Hst
    icases Hst with ⟨-, #Hst⟩
    iapply BigSepL.bigSepL_lookup hz $$ Hst
  generalize ms[revAfter ks ops v.ops]'hidx = mpv
  generalize hMdef : e.1 = M at hM
  ihave %Hksn := ownSlice_len $$ Hksl
  have hkslen : sint.Z keys.len = (ks.length : Int) := by
    have h1 := Hksn.1; have : sint.nat keys.len = (sint.Z keys.len).toNat := rfl
    have := Hksn.2; omega
  (try wp_auto)
  ihave HI : (∃ (j : w64) (kv0 : GoString),
      "i" ∷ i_ptr ↦ j ∗ "k" ∷ k_ptr ↦ kv0 ∗ "st" ∷ st_ptr ↦ mpv ∗
      "Hlrd" ∷ lease.lessorRd v.lp (mvccLeases v.ι.kv) ∗
      "Hlo" ∷ lease.leaseOwn (mvccLeases v.ι.kv) (leasesAfter ks ops v.ops)
        I ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z keys.len⌝ : IProp GF) $$ [i k st Hlrd Hlo]
  · iexists W64 0, _
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  by_cases Hlt : sint.Z j < sint.Z keys.len
  · -- an iteration: the key's lease
    rw [decide_eq_true Hlt]; simp only [↓reduceIte]
    list_elem ks (sint.nat j) as x
    have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z keys.len := ⟨Hj.1, Hlt⟩
    (try wp_auto)
    (try simp only [hb, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index keys (sint.Z j) ks DFrac.discard x Hj.1 $$ [Hksl] as -
    · iframe #; ipureintro; exact Hx_lookup
    (try wp_auto)
    wp_apply (wp_map_lookup2 go.string kvRec.ty mpv M x DFrac.discard) $$ [$Hm] as -
    (try wp_auto)
    have hl : (I.lookup
        (go_etcd_io.etcd.server.v3.lease.LeaseItem.mk x)).getD (W64 0) = leaseOfM M x := by
      rw [hpi]; exact leaseGet_eq ks M _ hM x
    cases hx : M !! x with
    | none =>
      have hlx : leaseOfM M x = W64 0 := by unfold leaseOfM; rw [hx]
      simp only [Option.isSome_none, Bool.false_eq_true, decide_false]
      (try wp_auto)
      wp_apply (wp_GetLease v.lp (mvccLeases v.ι.kv) (go_etcd_io.etcd.server.v3.lease.LeaseItem.mk x)
        _ _) $$ [$Hlrd $Hlo $Hlinv] as ⟨Hlrd, Hlo⟩
      (try wp_auto)
      wp_apply wp_check
      · ipureintro; simp only [decide_eq_true_eq]; rw [hl, hlx]; rfl
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, x
      iframe
      ipureintro; constructor <;> word
    | some ev =>
      have hlx : leaseOfM M x = ev.lease' := by unfold leaseOfM; rw [hx]
      simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
      (try wp_auto)
      wp_apply (wp_GetLease v.lp (mvccLeases v.ι.kv) (go_etcd_io.etcd.server.v3.lease.LeaseItem.mk x)
        _ _) $$ [$Hlrd $Hlo $Hlinv] as ⟨Hlrd, Hlo⟩
      (try wp_auto)
      wp_apply wp_check
      · ipureintro; simp only [decide_eq_true_eq]; rw [hl, hlx]
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, x
      iframe
      ipureintro; constructor <;> word
  · -- the keys' end: the number of live leases
    rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
    (try wp_auto)
    icases lease.leaseOwn_leases (mvccLeases v.ι.kv) _ _ $$ Hlo with ⟨%mL, #HlbL, Hback⟩
    have hTB : threadBound GF ≤ 2 ^ 30 - 1 := ThreadBoundLe.le_of (2 ^ 28) (by omega)
    have hRB : receiptBound GF ≤ 2 ^ 62 := by
      have : receiptBound GF ≤ 2 ^ 38 := ReceiptBoundLe.receiptBound_le
      omega
    wp_apply (wp_Leases v.lp (mvccLeases v.ι.kv) mL) $$ [Htok]
      as %sl %ls ⟨Htok, Hsl, ⟨%iL, %HiL, #Hmap⟩, -⟩
    · iframe #; iframe; ipureintro; exact ⟨hTB, hRB⟩
    ihave ⟨Hlo, %Hids⟩ := Hback $$ %iL %ls %HiL Hmap
    have hLnd : (leasesAfter ks ops v.ops).Nodup :=
      ((logOk_leases ks Hkl ops hlog v.ops).1).imp (fun h => by intro e; subst e; omega)
    have hlen : ls.length = (leasesAfter ks ops v.ops).length := by
      rw [← List.length_map (f := Prod.snd)]
      exact ((List.perm_ext_iff_of_nodup Hids.1 hLnd).2 Hids.2).length_eq
    ihave %Hsll := ownSlice_len $$ Hsl
    ihave %Hlsl := ownSlice_len $$ Hlsv
    (try wp_auto)
    wp_apply wp_check
    · ipureintro
      simp only [decide_eq_true_eq]
      rw [List.length_map] at Hsll
      have h1 : sint.nat sl.len = (sint.Z sl.len).toNat := rfl
      have h2 : sint.nat lsl.len = (sint.Z lsl.len).toNat := rfl
      have : sint.Z sl.len = sint.Z lsl.len := by omega
      word
    (try wp_auto)
    have hsort := stateAfter_sorted (σOf ks ops v.ops).log
    have hLeases := logOk_leases ks Hkl ops hlog v.ops
    have hlslZ : sint.Z lsl.len = ((leasesAfter ks ops v.ops).length : Int) := by
      have h1 := Hlsl.1; have : sint.nat lsl.len = (sint.Z lsl.len).toNat := rfl
      have := Hlsl.2; omega
    ihave HL : (∃ (jl : w64) (x0 : w64),
        "i" ∷ i_ptr ↦ jl ∗ "id" ∷ id_ptr ↦ x0 ∗ "Hlsv" ∷ lsl ↦* leasesAfter ks ops v.ops ∗
        "Hlrd" ∷ lease.lessorRd v.lp (mvccLeases v.ι.kv) ∗
        "Hlo" ∷ lease.leaseOwn (mvccLeases v.ι.kv) (leasesAfter ks ops v.ops)
          I ∗
        "%Hjl" ∷ ⌜0 ≤ sint.Z jl ∧ sint.Z jl ≤ sint.Z lsl.len⌝ : IProp GF) $$ [i id Hlsv Hlrd Hlo]
    · iexists W64 0, _
      iframe
      ipureintro; constructor <;> word
    wp_for HL
    by_cases Hlt2 : sint.Z jl < sint.Z lsl.len
    · rw [decide_eq_true Hlt2]; simp only [↓reduceIte]
      list_elem (leasesAfter ks ops v.ops) (sint.nat jl) as id0
      have hb2 : 0 ≤ sint.Z jl ∧ sint.Z jl < sint.Z lsl.len := ⟨Hjl.1, Hlt2⟩
      (try wp_auto)
      (try simp only [hb2, _root_.and_self, _root_.decide_true, ↓reduceIte])
      wp_apply wp_load_slice_index lsl (sint.Z jl) (leasesAfter ks ops v.ops) _ id0 Hjl.1 $$ [Hlsv]
        as Hlsv
      · iframe; ipureintro; exact Hid0_lookup
      (try wp_auto)
      have hidL : id0 ∈ leasesAfter ks ops v.ops := List.mem_of_getElem? Hid0_lookup
      have hid0 : id0 ≠ W64 0 := by
        intro h; have := (hLeases.2.1 id0 hidL).1; rw [h] at this; simp at this
      ihave ⟨Hlo, #Hlb0⟩ := lease.leaseOwn_lb (mvccLeases v.ι.kv) _ _ $$ Hlo
      wp_apply (wp_Lookup v.lp (mvccLeases v.ι.kv) id0 0
          (some (leasesAfter ks ops v.ops, I))) $$
        [Hlrd Hlo] as %l ⟨Hlrd, -, Ho⟩
      · iframe Hlinv Hlrd Hlb0; rw [lease.lookupView_some]; iexact Hlo
      ihave ⟨%Hl, Ho⟩ : iprop(⌜l = null ↔ id0 ∉ leasesAfter ks ops v.ops⌝ ∗
          ((⌜l = null⌝ ∗ lease.leaseOwn (mvccLeases v.ι.kv) (leasesAfter ks ops v.ops)
              I) ∨
            lease.leaseOwnOpen (mvccLeases v.ι.kv) (leasesAfter ks ops v.ops)
              I id0 l)) $$ [Ho]
      · rw [← lease.lookupViewAfter_some]; iexact Ho
      have hlnn : l ≠ null := fun h => (Hl.1 h) hidL
      icases Ho with (⟨%Hnl, -⟩ | Ho)
      · exact absurd Hnl hlnn
      iunfold lease.leaseOwnOpen at Ho
      icases Ho with ⟨%HIs, #Hlobj, Hio, Hslot, Hback2⟩
      (try wp_auto)
      wp_apply wp_check
      · ipureintro; simp [hlnn]
      (try wp_auto)
      wp_apply (wp_Keys (mvccLeases v.ι.kv) l id0 (.owner I))
        $$ [Hio Hslot] as %ksl %kl ⟨Hkl, Hpre2, Hpost, %Hnd⟩
      · iframe Hlobj; rw [lease.keysPre_owner]; iframe
      ihave %Hkm : ⌜∀ k : GoString, k ∈ kl ↔ I.lookup
          (go_etcd_io.etcd.server.v3.lease.LeaseItem.mk k) = some id0⌝ $$ [Hpost]
      · rw [← lease.keysPost_owner]; iexact Hpost
      ihave Hlo : lease.leaseOwn (mvccLeases v.ι.kv) (leasesAfter ks ops v.ops)
          I $$ [Hpre2 Hback2]
      · rw [lease.keysPre_owner]; iapply Hback2 $$ Hpre2
      rw [hpi] at Hkm
      have hsub : kl ⊆ ks := fun k hk => leaseKeys_sub ks M _ hM id0 k ((Hkm k).1 hk)
      have hklks : kl.length ≤ ks.length := (List.subperm_of_subset Hnd hsub).length_le
      (try wp_auto)
      wp_apply (wp_Strings ksl kl) $$ [Hkl] as %kl' ⟨Hkl, %Hperm, %Hsorted⟩
      · iframe Hkl; ipureintro; omega
      have hkl' : kl' = ks.filter (onLease M id0) := by
        rw [← leaseDelKeys_eq_onLease ks Hks.1 M _ hM hsort id0 hid0]
        apply leaseDelKeys_eq hsort id0 kl' (Hperm.nodup_iff.1 Hnd)
        · intro k; rw [← Hperm.mem_iff]; exact Hkm k
        · exact Hsorted
      (try wp_auto)
      -- `want`: the tester's keys on the lease, in its order
      ihave HW : (∃ (j : w64) (wsl : GoSlice) (kv0 : GoString),
          "i" ∷ i_ptr ↦ j ∗ "want" ∷ want_ptr ↦ wsl ∗
          "Hwl" ∷ wsl ↦* ((ks.take (sint.nat j)).filter (onLease M id0)) ∗
          "Hwc" ∷ ownSliceCap GoString wsl (DFrac.own 1) ∗ "k" ∷ k_ptr ↦ kv0 ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z keys.len⌝ : IProp GF) $$ [i want k]
      · iexists W64 0, slice.nil, _
        simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.filter_nil]
        iframe
        isplitl
        · iapply ownSlice_nil
        isplitl
        · iapply ownSliceCap_nil
        ipureintro; constructor <;> word
      wp_for HW
      have hmatch_succ : ∀ (n : Nat) (x : GoString) (pr : GoString → Bool), ks[n]? = some x →
          (ks.take (n + 1)).filter pr =
            (ks.take n).filter pr ++ (if pr x then [x] else []) := by
        intro n x pr hx
        rw [List.take_add_one, hx, List.filter_append]
        cases h : pr x <;> simp [List.filter, h]
      by_cases Hlt3 : sint.Z j < sint.Z keys.len
      · rw [decide_eq_true Hlt3]; simp only [↓reduceIte]
        list_elem ks (sint.nat j) as x
        have hb3 : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z keys.len := ⟨Hj.1, Hlt3⟩
        (try wp_auto)
        (try simp only [hb3, _root_.and_self, _root_.decide_true, ↓reduceIte])
        wp_apply wp_load_slice_index keys (sint.Z j) ks DFrac.discard x Hj.1 $$ [Hksl] as -
        · iframe #; ipureintro; exact Hx_lookup
        (try wp_auto)
        have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
        wp_apply (wp_map_lookup2 go.string kvRec.ty mpv M x DFrac.discard) $$ [$Hm] as -
        (try wp_auto)
        cases hx : M !! x with
        | none =>
          simp only [Option.isSome_none, Bool.false_eq_true, decide_false]
          (try wp_auto)
          wp_for_post
          iframe
          iexists j + W64 1, wsl, x
          rw [hj1, hmatch_succ (sint.nat j) x _ Hx_lookup]
          simp only [onLease, hx, Bool.false_eq_true, ↓reduceIte, List.append_nil]
          iframe
          ipureintro; constructor <;> word
        | some ev =>
          simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
          (try wp_auto)
          by_cases hev : ev.lease' = id0
          · simp only [hev, _root_.decide_true]
            (try wp_auto)
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %osl ⟨Hosl, -⟩
            (try wp_auto)
            wp_apply wp_slice_append $$ [$Hwl $Hwc $Hosl] as %wsl' ⟨Hwl, Hwc, -⟩
            wp_for_post
            iframe
            iexists j + W64 1, wsl', x
            rw [hj1, hmatch_succ (sint.nat j) x _ Hx_lookup]
            simp only [onLease, hx, hev, _root_.decide_true, ↓reduceIte]
            iframe
            ipureintro; constructor <;> word
          · simp only [hev, decide_false]
            (try wp_auto)
            wp_for_post
            iframe
            iexists j + W64 1, wsl, x
            rw [hj1, hmatch_succ (sint.nat j) x _ Hx_lookup]
            simp only [onLease, hx, hev, decide_false, Bool.false_eq_true, ↓reduceIte, List.append_nil]
            iframe
            ipureintro; constructor <;> word
      · rw [decide_eq_false Hlt3]; simp only [Bool.false_eq_true, ↓reduceIte]
        have hjn : sint.nat j = ks.length := by
          have h0 := Hj.2; have h4 : sint.nat j = (sint.Z j).toNat := rfl; rw [h4]; omega
        simp only [hjn, List.take_length]
        ihave Hwl : wsl ↦* kl' $$ [Hwl]
        · rw [hkl']; iexact Hwl
        (try wp_auto)
        ihave %Hgl := ownSlice_len $$ Hkl
        ihave %Hwll := ownSlice_len $$ Hwl
        have hn : ∀ x : w64, sint.nat x = (sint.Z x).toNat := fun _ => rfl
        have hlenw : sint.Z ksl.len = sint.Z wsl.len := by
          have h1 := Hgl.1; have h2 := Hwll.1; rw [hn] at h1 h2; omega
        wp_apply wp_check
        · ipureintro; simp only [decide_eq_true_eq]; word
        (try wp_auto)
        -- `got` and `want` are both `kl'`: every element's check passes
        ihave HV : (∃ (i0 jv : w64), "i" ∷ i_ptr ↦ i0 ∗ "j" ∷ j_ptr ↦ jv ∗
            "%Hi" ∷ ⌜0 ≤ sint.Z i0 ∧ sint.Z i0 ≤ sint.Z ksl.len⌝ : IProp GF) $$ [i j]
        · iexists W64 0, _
          simp only [named]
          iframe
          ipureintro; constructor <;> word
        wp_for HV
        wp_if_destruct
        · have hlt : sint.Z i0 < sint.Z ksl.len := by exact Hif
          have hb : 0 ≤ sint.Z i0 ∧ sint.Z i0 < sint.Z ksl.len := ⟨Hi.1, hlt⟩
          have hb4 : 0 ≤ sint.Z i0 ∧ sint.Z i0 < sint.Z wsl.len := ⟨Hi.1, by omega⟩
          simp only [hb, _root_.and_self, ↓reduceIte]
          list_elem kl' (sint.nat i0) as w
          wp_apply wp_load_slice_index ksl (sint.Z i0) kl' _ w hb.1 $$ [Hkl] as Hkl
          · iframe; ipureintro; exact Hw_lookup
          (try wp_auto)
          (try simp only [hb, _root_.and_self, ↓reduceIte])
          wp_apply wp_load_slice_index ksl (sint.Z i0) kl' _ w hb.1 $$ [Hkl] as Hkl
          · iframe; ipureintro; exact Hw_lookup
          (try wp_auto)
          (try simp only [hb, hb4, _root_.and_self, ↓reduceIte])
          wp_apply wp_load_slice_index wsl (sint.Z i0) kl' _ w hb.1 $$ [Hwl] as Hwl
          · iframe; ipureintro; exact Hw_lookup
          (try wp_auto)
          wp_apply wp_check
          · ipureintro; simp
          (try wp_auto)
          wp_for_post
          iframe
          iexists i0 + W64 1, _
          iframe
          ipureintro; constructor <;> word
        (try wp_auto)
        wp_for_post
        iframe
        iexists jl + W64 1, id0
        iframe
        ipureintro; constructor <;> word
    · rw [decide_eq_false Hlt2]; simp only [Bool.false_eq_true, ↓reduceIte]
      (try wp_auto)
      subst hIdef
      iapply HΦ
      iframe Hrd Htok
      iunfold memCore
      dsimp only
      iframe Hid Hhook Hhok Hpath Hbe Hle Hkvf Hrevf Hcmpf HincW Hopen Hmb Hhis Hrds Hbk
      isplitl [Hlf Hlsv Hlcap]
      · iexists lsl; iframe
      isplitr
      · ipureintro; exact Hvle
      isplitl
      · iunfold lessorW
        iexists rd, r
        iframe; iframe #
        ipureintro; exact Hrecs
      ipureintro; exact HU

end proof

end mvccfull
end EtcdGrove
end Perennial
