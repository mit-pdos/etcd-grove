/- Lean-first (no Rocq counterpart). The proof of `writer.checkLeases`: the snapshot's last map is
the last revision's state (`writerIdle`: the snapshot is the writer's revisions exactly), which
matches the store's state after its log (`lastSt_match`), whose item map the lease owner holds
(`writerOwn`: `pendItems σ.log [] = leaseItemsOf (stateAfter σ.log)`): `GetLease` of each key is the
tester's lease of it (`leaseGet_eq`); each of the model's live leases is in `L`, so `Lookup` (by the
owner) returns its lease, whose `Keys()` (by the owner) are the keys the item map puts on it, sorted
the store's `leaseDelKeys`, which are the tester's keys on it in order (`leaseDelKeys_eq`,
`leaseDelKeys_eq_onLease`). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__checkLeases
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.history__snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.check
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Lookup
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__GetLease
public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__Keys
public import Perennial.Spec.sort.Strings

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem writer.checkLeases.wp_proof
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_snapshot : history.snapshot.spec (GF := GF) (hG := hG))
    (wp_Lookup : lease.lessor.Lookup.spec (GF := GF) (hG := hG))
    (wp_GetLease : lease.lessor.GetLease.spec (GF := GF) (hG := hG))
    (wp_Keys : lease.Lease.Keys.spec (GF := GF) (hG := hG))
    (wp_Strings : sort.Strings.spec (GF := GF) (hG := hG)) :
    writer.checkLeases.spec (GF := GF) (hG := hG) := by
  intro w wv γ B f q σ Hs L n k T R
  wp_start as ⟨Hctx, Hown, Hle⟩
  iunfold writerCtx at Hctx
  icases Hctx with ⟨#Hpkg, #Hmpkg, #Htpkg, #Hw, #Hinv, #Hhist, -, -, -⟩
  iunfold writerOwn at Hown
  icases Hown with ⟨Htok, Hbk, Hrd, Hidle, Hg, ⟨%Lm, Hlm, %HLm⟩, Hlo⟩
  iunfold writerLe at Hle
  icases Hle with ⟨%lp, %rd, %r, #Hro, Hlrd, Hrvk, HR, HT, Hrdo, Hdel, Hbe, Hrb, %HlP, Hnext,
    %Hn⟩
  ihave #Hro2 := Hro
  iunfold writerLeRO at Hro2
  icases Hro2 with ⟨%Hle, #Hlpkg, #Hlinv, #Hlcfg, #Hguard, #Hlbe⟩
  ihave #Hw2 := Hw
  iunfold writerRO at Hw2
  icases Hw2 with ⟨#kvW, #leW, #hW, #rW, #leasesW, #applyingW, #savedW, #ticksW⟩
  iunfold writerIdle at Hidle
  icases Hidle with ⟨Hgσ, HW, Hpv, %Hid⟩
  obtain ⟨Hpend, Hlen, Hbound, Hmatch⟩ := Hid
  icases histW_lb γ.h Hs $$ HW with ⟨HW, #Hlb⟩
  -- the last state matches the store's, whose item map the owner holds
  have hM := lastSt_match σ.log Hs Hlen Hmatch
  have hsort := stateAfter_sorted σ.log
  wp_auto
  wp_apply wp_snapshot wv.h' γ.h Hs $$ [$Hrd $Hlb] as %s ⟨Hrd, %ms, %Hs', %Hpre, %Hcap, #Hlb', #Hms, #Hst⟩
  -- the snapshot is the writer's revisions
  ihave %Hle2 : ⌜Hs' <+: Hs⌝ $$ [HW]
  · iunfold histW at HW
    icases HW with ⟨%x, %Hx, -, Hl, -, -⟩
    ihave %H := mono_list_auth_lb_valid γ.h.l _ _ _ $$ Hl Hlb'
    ipureintro; exact H.2
  have hHs : Hs' = Hs :=
    List.IsPrefix.eq_of_length Hle2 (Nat.le_antisymm Hle2.length_le Hpre.1.length_le)
  subst hHs
  ihave %Hmlen : ⌜ms.length = Hs'.length⌝ $$ [Hst]
  · iunfold statesP at Hst; icases Hst with ⟨%H, -⟩; ipureintro; exact H
  ihave %Hsl := ownSlice_len $$ Hms
  have h2 := Hpre.2
  have hsl : sint.Z s.len = (Hs'.length : Int) := by
    have : sint.nat s.len = (sint.Z s.len).toNat := rfl
    omega
  have hb : 0 ≤ sint.Z (s.len - W64 1) ∧ sint.Z (s.len - W64 1) < sint.Z s.len := by
    constructor <;> word
  simp only [hb, _root_.and_self, ↓reduceIte]
  have hi : (sint.Z (s.len - W64 1)).toNat = Hs'.length - 1 := by word
  have hidx : Hs'.length - 1 < ms.length := by omega
  wp_apply wp_load_slice_index s (sint.Z (s.len - W64 1)) ms DFrac.discard
    (ms[Hs'.length - 1]'hidx) hb.1 $$ [Hms] as -
  · iframe #; ipureintro; rw [hi]; exact List.getElem?_eq_getElem hidx
  have hidx2 : Hs'.length - 1 < Hs'.length := by omega
  have hz : (ms.zip Hs')[Hs'.length - 1]? =
      some (ms[Hs'.length - 1]'hidx, Hs'[Hs'.length - 1]'hidx2) := by
    rw [List.getElem?_zip_eq_some]
    exact ⟨List.getElem?_eq_getElem hidx, List.getElem?_eq_getElem hidx2⟩
  ihave #Hm : (ms[Hs'.length - 1]'hidx ↦$□ (Hs'[Hs'.length - 1]'hidx2).1 : IProp GF) $$ [Hst]
  · iunfold statesP at Hst
    icases Hst with ⟨-, #Hst⟩
    iapply BigSepL.bigSepL_lookup hz $$ Hst
  have hlast : lastSt Hs' = (Hs'[Hs'.length - 1]'hidx2).1 := by
    unfold lastSt; rw [List.getElem?_eq_getElem hidx2]; rfl
  rw [← hlast]
  generalize ms[Hs'.length - 1]'hidx = mp
  generalize hMdef : lastSt Hs' = M at hM
  -- the keys
  ihave Hmi : (mvccrandInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iunfold mvccrandInit at Hmi
  icases Hmi with ⟨⟨%ks, #Hks, #Hksl⟩, -⟩
  ihave %Hksn := ownSlice_len $$ Hksl
  have hks6 : sint.Z ks.len = 6 := by
    have h := Hksn.1; simp only [keyList, List.length_cons, List.length_nil] at h
    have h4 : sint.nat ks.len = (sint.Z ks.len).toNat := rfl
    have := Hksn.2; omega
  rw [Hle]
  (try wp_auto)
  ihave HI : (∃ (j : w64) (kv0 : GoString),
      "i" ∷ i_ptr ↦ j ∗ "k" ∷ k_ptr ↦ kv0 ∗ "cur" ∷ cur_ptr ↦ mp ∗
      "Hlrd" ∷ lease.lessorRd lp (mvccLeases γ.kv) ∗
      "Hlo" ∷ lease.leaseOwn (mvccLeases γ.kv) L (pendItems σ.log []) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 6⌝ : IProp GF) $$ [i k cur Hlrd Hlo]
  · iexists W64 0, _
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  by_cases Hlt : sint.Z j < sint.Z ks.len
  · -- an iteration: the key's lease
    rw [decide_eq_true Hlt]; simp only [↓reduceIte]
    have hj6 : sint.Z j < 6 := by rw [← hks6]; exact Hlt
    list_elem keyList (sint.nat j) as x
    have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z ks.len := ⟨Hj.1, Hlt⟩
    (try wp_auto)
    (try simp only [hb, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index ks (sint.Z j) keyList DFrac.discard x Hj.1 $$ [Hksl] as -
    · iframe #; ipureintro; exact Hx_lookup
    (try wp_auto)
    wp_apply (wp_map_lookup2 go.string kvRec.ty mp M x DFrac.discard) $$ [$Hm] as -
    (try wp_auto)
    have hl : ((pendItems σ.log []).lookup (go_etcd_io.etcd.server.v3.lease.LeaseItem.mk x)).getD
        (W64 0) = leaseOfM M x := by
      rw [pendItems_nil]; exact leaseGet_eq M _ hM x
    have hl2 : ((findKey x (applyChanges (W64 (σ.log.length : Int)) (stateAfter σ.log) [])).bind
        kvLease).getD (W64 0) = leaseOfM M x := hl
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    cases hx : M !! x with
    | none =>
      have hlx : leaseOfM M x = W64 0 := by unfold leaseOfM; rw [hx]
      simp only [Option.isSome_none, Bool.false_eq_true, decide_false]
      (try wp_auto)
      wp_apply (wp_GetLease lp (mvccLeases γ.kv) (go_etcd_io.etcd.server.v3.lease.LeaseItem.mk x)
        L (pendItems σ.log [])) $$ [$Hlrd $Hlo $Hlinv] as ⟨Hlrd, Hlo⟩
      (try wp_auto)
      wp_apply wp_check
      · ipureintro; simp only [decide_eq_true_eq]; rw [hl2, hlx]; rfl
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, x
      iframe
      ipureintro; constructor <;> word
    | some e =>
      have hlx : leaseOfM M x = e.lease' := by unfold leaseOfM; rw [hx]
      simp only [Option.isSome_some, decide_true, Option.getD_some]
      (try wp_auto)
      wp_apply (wp_GetLease lp (mvccLeases γ.kv) (go_etcd_io.etcd.server.v3.lease.LeaseItem.mk x)
        L (pendItems σ.log [])) $$ [$Hlrd $Hlo $Hlinv] as ⟨Hlrd, Hlo⟩
      (try wp_auto)
      wp_apply wp_check
      · ipureintro; simp only [decide_eq_true_eq]; rw [hl2, hlx]
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, x
      iframe
      ipureintro; constructor <;> word
  · -- the keys' end: the live leases
    rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
    (try wp_auto)
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range (fun (_ : List w64) (_ : Int) => iprop(∃ (x : w64),
        "id" ∷ id_ptr ↦ x ∗ "cur" ∷ cur_ptr ↦ mp ∗ "w" ∷ w_ptr ↦ w ∗
        "Hlrd" ∷ lease.lessorRd lp (mvccLeases γ.kv) ∗
        "Hlo" ∷ lease.leaseOwn (mvccLeases γ.kv) L (pendItems σ.log []))) $$ Hlm
    iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
    isplitl [id cur w Hlrd Hlo]
    · iexists _
      simp only [named]
      iframe
    isplitr
    · imodintro
      iintro %i %id0 %vv ⟨%Hkey, %Hvv⟩ HP
      iNamed HP
      wp_auto
      have hidL : id0 ∈ L := (HLm id0).1 (by rw [Hvv]; rfl)
      have hid0 : id0 ≠ W64 0 := by
        intro h; have := (Hn.2 id0 hidL).1; rw [h] at this; simp at this
      ihave ⟨Hlo, #Hlb0⟩ := lease.leaseOwn_lb (mvccLeases γ.kv) L (pendItems σ.log []) $$ Hlo
      wp_apply (wp_Lookup lp (mvccLeases γ.kv) id0 0 (some (L, pendItems σ.log []))) $$
        [Hlrd Hlo] as %l ⟨Hlrd, -, Ho⟩
      · iframe Hlinv Hlrd Hlb0; rw [lease.lookupView_some]; iexact Hlo
      ihave ⟨%Hl, Ho⟩ : iprop(⌜l = null ↔ id0 ∉ L⌝ ∗
          ((⌜l = null⌝ ∗ lease.leaseOwn (mvccLeases γ.kv) L (pendItems σ.log [])) ∨
            lease.leaseOwnOpen (mvccLeases γ.kv) L (pendItems σ.log []) id0 l)) $$ [Ho]
      · rw [← lease.lookupViewAfter_some]; iexact Ho
      have hlnn : l ≠ null := fun h => (Hl.1 h) hidL
      icases Ho with (⟨%Hnl, -⟩ | Ho)
      · exact absurd Hnl hlnn
      iunfold lease.leaseOwnOpen at Ho
      icases Ho with ⟨%HIs, #Hlobj, Hio, Hslot, Hback⟩
      (try wp_auto)
      wp_apply wp_check
      · ipureintro; simp [hlnn]
      (try wp_auto)
      wp_apply (wp_Keys (mvccLeases γ.kv) l id0 (.owner (pendItems σ.log []))) $$ [Hio Hslot]
        as %ksl %kl ⟨Hkl, Hpre, Hpost, %Hnd⟩
      · iframe Hlobj; rw [lease.keysPre_owner]; iframe
      ihave %Hkm : ⌜∀ k : GoString, k ∈ kl ↔ (pendItems σ.log []).lookup
          (go_etcd_io.etcd.server.v3.lease.LeaseItem.mk k) = some id0⌝ $$ [Hpost]
      · rw [← lease.keysPost_owner]; iexact Hpost
      ihave Hlo : lease.leaseOwn (mvccLeases γ.kv) L (pendItems σ.log []) $$ [Hpre Hback]
      · rw [lease.keysPre_owner]; iapply Hback $$ Hpre
      -- the keys are the tester's: at most six
      have hsub : kl ⊆ keyList := fun k hk => leaseKeys_sub M _ hM id0 k ((Hkm k).1 hk)
      have hkl6 : kl.length ≤ 6 := by simpa [keyList] using (List.subperm_of_subset Hnd hsub).length_le
      (try wp_auto)
      wp_apply (wp_Strings ksl kl) $$ [Hkl] as %kl' ⟨Hkl, %Hperm, %Hsorted⟩
      · iframe Hkl; ipureintro; omega
      -- sorted: the store's `leaseDelKeys`, the tester's keys on the lease in order
      have hkl' : kl' = keyList.filter (onLease M id0) := by
        rw [← leaseDelKeys_eq_onLease M _ hM hsort id0 hid0]
        apply leaseDelKeys_eq hsort id0 kl' (Hperm.nodup_iff.1 Hnd)
        · intro k; rw [← Hperm.mem_iff]; exact Hkm k
        · exact Hsorted
      (try wp_auto)
      sorry
    iintro HP Hlm
    iNamed HP
    wp_auto
    sorry

end proof

end mvccrand
end EtcdGrove
end Perennial
