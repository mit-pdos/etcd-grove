/-
`DB.grow`'s `File.Truncate` and `File.Sync` of bbolt's file over its shares (`bMeta`, `bMetaT`,
`bBytes`), in either mode (W1 stage B of `plans/bbolt-crash-plan.md` §7, step 3; Lean-first, no Rocq
counterpart).

* `wp_bTruncate`: a growing truncate to a whole number of pages: outside a crash invariant
  `File.Truncate.spec`; inside one the local crash spec (`os.File.Truncate.specCrashIL`), the
  obligation from `bDur_trunc_idle`, the new bytes' exclusivity tokens added to the authority
  (`exMap_grow`). Grown, the share is `bMetaT` (the crash sizes the old size and the new one until the sync), the grown
  range joining the ranges since the last sync.
* `wp_bSync`: `File.Sync` from `bMetaT`, as `wp_bFdatasync` (`Inv/BFileSync.lean`).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.BFileSync
public import Proof.go_etcd_io.bbolt.Mmap.GrowRes
public import Spec.os.File__Truncate
public import Spec.os.File__Sync
public import Spec.os.CrashStILLong

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
open Iris Iris.BI Iris.ProofMode

section res
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

omit go_gctx sem in
/-- **The exclusivity tokens of `k` new bytes from `n`**, out of the authority of a file of `n`
bytes. -/
theorem exMap_grow (γ : GName) (n : Nat) : ∀ k : Nat,
    ⊢ ghostMapAuth (GF := GF) (K := Nat) (V := Unit) γ 1 (exMap n) ==∗
      ghostMapAuth (K := Nat) (V := Unit) γ 1 (exMap (n + k)) ∗
      [∗list] j ∈ List.range' n k, ghostMapElem (K := Nat) (V := Unit) γ j (DFrac.own 1) ()
  | 0 => by
    iintro H
    imodintro
    rw [Nat.add_zero, List.range'_zero]
    iframe
    iapply BigSepL.bigSepL_nil.2; iempintro
  | k + 1 => by
    iintro H
    imod exMap_grow γ n k $$ H with ⟨H, Hs⟩
    imod ghost_map_insert (n + k) () (exMap_lookup_ge (n + k) (n + k) (Nat.le_refl _)) $$ H
      with ⟨H, Hk⟩
    imodintro
    rw [show n + (k + 1) = (n + k) + 1 by omega, List.range'_1_concat,
      show exMap (n + k + 1) = (exMap (n + k)).insert (n + k) () from rfl]
    isplitl [H]
    · iexact H
    iapply BigSepL.bigSepL_append.2
    iframe Hs
    iapply BigSepL.bigSepL_singleton.2; iexact Hk

theorem rsPost_maps' (m : OsMeta) (sz : Nat) : (rsPost true m sz sz).maps = m.maps := by
  show (m.announce (min m.size sz) (rsHi true m.size sz) sz).maps = m.maps
  exact announce_maps _ _ _ _

variable [os.Assumptions] in
/-- **A growing `File.Truncate` of bbolt's file**, in either mode (see the file header). -/
theorem wp_bTruncate (hT : os.File.Truncate.spec (GF := GF) (hG := hG))
    (hTC : os.File.Truncate.specCrashIL (GF := GF) (hG := hG))
    (hTB : os.File.Truncate.specCrashILBig (GF := GF) (hG := hG))
    (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sz : w64) (dq : DFrac) (d : OsFd)
    (p : BFile) (C : CommitSt) (L : List (Nat × Nat)) (m : OsMeta)
    (hd : d.ino = p.ino) (hfd : 0 ≤ fd.toInt) (hwr : d.writable = true) (hsz0 : 0 ≤ sz.toInt)
    (hge : m.size ≤ sz.toNat) (hns : bNsOk p)
    (hcr : p.cs ≠ none → sz.toNat % 4096 = 0) :
    {{ osInv (GF := GF) ∗ bCsInv p ∗ os.ownFile (GF := GF) f fd name dqf ∗ osFd (GF := GF) fd dq d ∗
        bMeta p C L m ∗ mcellsAny (GF := GF) m.maps m.size (rsHi true m.size sz.toNat) }}
      (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Truncate")) (Val #sz))
    {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d ∗
        ((⌜err = interface.nil⌝ ∗ ∃ m' : OsMeta, ⌜m'.size = sz.toNat ∧ m'.maps = m.maps⌝ ∗
            bMetaT p C ((m.size, sz.toNat - m.size) :: L) m' ∗ zBytes p m.size (sz.toNat - m.size) ∗
            mcells (GF := GF) m.maps m.size (rsHi true m.size sz.toNat) (rsCell sz.toNat)) ∨
         (⌜err ≠ interface.nil⌝ ∗
          ((∃ m' : OsMeta, ⌜m'.size = sz.toNat ∧ m'.maps = m.maps⌝ ∗
            bMeta p C L m' ∗ zBytes p m.size (sz.toNat - m.size) ∗
            mcells (GF := GF) m.maps m.size (rsHi true m.size sz.toNat) (rsCell sz.toNat)) ∨
           (∃ m' : OsMeta, ⌜m'.size = m.size ∧ m'.maps = m.maps⌝ ∗
            bMeta p C L m' ∗ mcellsAny (GF := GF) m.maps m.size (rsHi true m.size sz.toNat))))) ∗
        fmtErrorOkOrNil err }} := by
  iintro %Φ ⟨#Hos, #Hinv, Hf, Hfd, Hm, Hc⟩ HΦ
  have hmin : min m.size sz.toNat = m.size := Nat.min_eq_left hge
  cases hc : p.cs with
  | none =>
    simp only [bMeta_none hc]
    rw [← hd]
    ihave Hnil : osBytes (GF := GF) d.ino (min m.size sz.toNat) (DFrac.own 1) [] $$ []
    · unfold osBytes; iapply bytesG_nil; iempintro
    iapply (hT f fd name dqf sz dq d m [] hfd hwr hsz0 (by simp only [List.length_nil]; omega))
      $$ [Hf Hfd Hm Hnil Hc]
    · rw [hmin]; iframe; iframe #
    inext
    iintro %err ⟨Hf, Hfd, Hr, Herr⟩
    iapply HΦ $$ %err
    iframe Hf Hfd Herr
    rw [hd]
    simp only [bMetaT_none hc, bMeta_none hc]
    have hdone : os.ftDone (GF := GF) p.ino m sz.toNat ⊢
        ∃ m' : OsMeta, ⌜m'.size = sz.toNat ∧ m'.maps = m.maps⌝ ∗
          osMeta p.ino (DFrac.own 1) m' ∗ zBytes p m.size (sz.toNat - m.size) ∗
          mcells (GF := GF) m.maps m.size (rsHi true m.size sz.toNat) (rsCell sz.toNat) := by
      unfold os.ftDone
      iintro ⟨%zs, %hzs, Hm, Hz, Hc⟩
      iexists rsPost true m sz.toNat sz.toNat
      isplitr
      · ipureintro; exact ⟨rfl, rsPost_maps' m sz.toNat⟩
      rw [hmin]
      iframe Hm Hc
      unfold zBytes
      iexists _
      ihave Hz := (bBytes_none hc _ _ _).2 $$ Hz
      iframe Hz
      ipureintro
      rw [List.map_map, ← hzs]; exact List.map_const'
    icases Hr with (⟨%he, Hr⟩ | ⟨%he, (Hr | Hr)⟩)
    · ileft; isplitr
      · ipureintro; exact he
      iapply hdone $$ Hr
    · iright; isplitr
      · ipureintro; exact he
      ileft; iapply hdone $$ Hr
    · iright
      isplitr
      · ipureintro; exact he
      iright
      unfold os.ftUndone
      icases Hr with ⟨%xs', -, Hm, -, Hc⟩
      iexists m.announce (min m.size sz.toNat) (rsHi true m.size sz.toNat) sz.toNat
      isplitr
      · ipureintro; exact ⟨announce_size _ _ _ _, announce_maps _ _ _ _⟩
      rw [hmin]
      iframe
  | some c =>
    have hal := hcr (by rw [hc]; exact fun h => nomatch h)
    ihave #Hci := bCsInv_some p c hc $$ Hinv
    icases bMeta_own p c hc C L m $$ Hm with ⟨%bs, %a, Hown, Ha, %Hf⟩
    obtain ⟨hph, hcur, hdur, hfs, hlh⟩ := Hf
    imod csOwnIL_ok c.N p.ino c.g c.ga c.gc bCsOk ⟨m, bs, 0, 0, .idle⟩ a ⊤ CoPset.subseteq_top
      $$ Hci Hown with ⟨Hown, %Hok⟩
    have hD : BDur a ⟨m, bs, 0, 0, .idle⟩ := Hok.1 hfs
    have hbl : bs.length = m.size := hD.1.1
    by_cases hmax : sz.toNat ≤ maxBytes
    rotate_left
    · -- past `maxBytes`: the truncate fails (`EFBIG`), the file as its first attempt announced it
      have hobl : ∀ m', (m' = m ∨ m' = m.announce (min m.size sz.toNat) (rsHi true m.size sz.toNat)
          sz.toNat) → bCsOk a ⟨m', bs, 0, 0, .idle⟩ ∧ ∀ t n, bCsOk a ⟨m', bs, 0, 0, .trunc t sz.toNat n⟩ := by
        intro m' hm'
        have hR : TReach m bs sz.toNat m' bs := by
          rcases hm' with rfl | rfl
          · exact .refl
          · exact .ann
        exact ⟨fun _ => (bDur_trunc_idle a hph m bs 0 0 sz.toNat hD hge hal m' bs hR).1,
          fun t n _ => (bDur_trunc_idle a hph m bs 0 0 sz.toNat hD hge hal m' bs hR).2 t n⟩
      iapply (hTB f fd name dqf sz dq d c.N p.ino c.g c.ga c.gc bCsOk a m bs hd hfd hwr hsz0 hge
        (by omega) (hns c hc) hobl) $$ [Hf Hfd Hown Hc]
      · iframe; iframe #
      inext
      iintro %err ⟨Hf, Hfd, %hne, #Herr, Hown, Hc⟩
      iapply HΦ $$ %err
      iframe Hf Hfd
      isplitl [Hown Ha Hc]
      · iright
        isplitr
        · ipureintro; exact hne
        iright
        iexists m.announce (min m.size sz.toNat) (rsHi true m.size sz.toNat) sz.toNat
        isplitr
        · ipureintro; exact ⟨announce_size _ _ _ _, announce_maps _ _ _ _⟩
        isplitl [Hown Ha]
        · iapply bMeta_of_own p c hc C L _ bs a ⟨hph, hcur, hdur, hfs, xsOne_announce hlh _ _ _⟩
            $$ [Hown Ha]
          rw [announce_size]; iframe
        iexact Hc
      iapply fmtErrorOkOrNil_of $$ Herr
    imod exMap_grow c.ex m.size (sz.toNat - m.size) $$ Ha with ⟨Ha, Hex⟩
    iapply (hTC f fd name dqf sz dq d c.N p.ino c.g c.ga c.gc bCsOk a m bs hd hfd hwr hsz0 hge hmax
      (hns c hc) (fun m' bs' hR =>
        ⟨fun _ => (bDur_trunc_idle a hph m bs 0 0 sz.toNat hD hge hal m' bs' hR).1,
         fun t n _ => (bDur_trunc_idle a hph m bs 0 0 sz.toNat hD hge hal m' bs' hR).2 t n⟩))
      $$ [Hf Hfd Hown Hc]
    · iframe; iframe #
    inext
    iintro %err ⟨Hf, Hfd, Hr⟩
    icases Hr with (⟨%he, %n, %m0, %hm0, Hg⟩ | ⟨%he, -⟩)
    rotate_left
    · exact absurd hfs he.2
    subst he
    iapply HΦ $$ %interface.nil
    iframe Hf Hfd
    have hm0s : m0.size = m.size ∧ m0.maps = m.maps := by
      rcases hm0 with rfl | rfl
      · exact ⟨rfl, rfl⟩
      · exact ⟨announce_size _ _ _ _, announce_maps _ _ _ _⟩
    unfold csGrownL
    icases Hg with ⟨%zs, %hzs, Hown, Hz, Hcm⟩
    isplitl
    · ileft
      isplitr
      · ipureintro; rfl
      iexists rsPost true m0 sz.toNat sz.toNat
      isplitr
      · ipureintro; exact ⟨rfl, (rsPost_maps' m0 sz.toNat).trans hm0s.2⟩
      ihave %hlo := csOwnL_locOk (csTokI c.g c.ga a) p.ino _ $$ Hown
      rw [hm0s.1, hm0s.2]
      have hdo : DurOut ((m.size, sz.toNat - m.size) :: L) (bs ++ grownBytes zs n) := by
        intro k x hk hko
        have hk' := hko (m.size, sz.toNat - m.size) List.mem_cons_self
        have hkl : k < m.size := by
          rcases hk' with h | h
          · exact h
          · exfalso
            have := (List.getElem?_eq_some_iff.1 hk).1
            simp only [List.length_append, List.length_map, hbl, hzs.1, hm0s.1] at this
            omega
        rw [List.getElem?_append_left (by omega)] at hk
        exact hdur k x hk (fun r hr => hko r (List.mem_cons_of_mem _ hr))
      isplitl [Hown Ha]
      · unfold bMetaT
        iapply bMetaG_of_own false p c hc C ((m.size, sz.toNat - m.size) :: L)
          (rsPost true m0 sz.toNat sz.toNat) (bs ++ grownBytes zs n) a
          ⟨hph, hcur, hdo, hfs, fun h => nomatch h⟩ $$ [Hown Ha]
        rw [show (rsPost true m0 sz.toNat sz.toNat).size = m.size + (sz.toNat - m.size) by
          show sz.toNat = _; omega]
        iframe
      isplitl [Hz Hex]
      · unfold zBytes
        iexists grownBytes zs n
        isplitl
        · iapply (bBytes_os p m.size (DFrac.own 1) _).2
          have hdq : p.dq (DFrac.own 1) = DFrac.own (1 : Qp).half := by
            unfold BFile.dq; rw [hc]; rfl
          rw [hdq]
          iframe Hz
          unfold bGhost; rw [hc]; dsimp only
          simp only [grownBytes, List.length_map, hzs.1, hm0s.1]
          iexact Hex
        ipureintro
        simp only [grownBytes, List.map_map, Function.comp_def]
        rw [List.map_const', hzs.1, hm0s.1]
      iexact Hcm
    unfold fmtErrorOkOrNil; itrivial

variable [os.Assumptions] in
/-- **`File.Sync` of bbolt's file after a growing truncate**, in either mode (`wp_bFdatasync`'s
shape, from `bMetaT`). -/
theorem wp_bSync (hS : os.File.Sync.specB (GF := GF) (hG := hG))
    (hSC : os.File.Sync.specCrashIL (GF := GF) (hG := hG))
    (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd) (p : BFile) (C : CommitSt)
    (L : List (Nat × Nat)) (m : OsMeta) (R : List (Nat × List ByteG)) (hd : d.ino = p.ino)
    (hns : bNsOk p) (hcov : RCov R L m.size) (hdisj : RDisj R)
    (hin : ∀ r ∈ R, r.1 + r.2.length ≤ m.size) :
    {{ osInv (GF := GF) ∗ bCsInv p ∗ os.ownFile (GF := GF) f fd name dqf ∗ osFd fd dq d ∗
        bMetaT p C L m ∗ bRanges p R }}
      (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Sync")) (Val #()))
    {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d ∗
        ((⌜err = interface.nil⌝ ∗ ∃ (m' : OsMeta) (R' : List (Nat × List ByteG)),
            bMeta p C [] m' ∗ bRanges p R' ∗ ⌜m'.size = m.size ∧ m'.maps = m.maps ∧ RSame R R'⌝) ∨
         (⌜err ≠ interface.nil ∧ ¬ FsNoErr⌝ ∗ bMetaT p C L m ∗ bRanges p R)) ∗
        fmtErrorOkOrNil err }} := by
  iintro %Φ ⟨#Hos, #Hinv, Hf, Hfd, Hm, HR⟩ HΦ
  cases hc : p.cs with
  | none =>
    simp only [bMetaT_none hc]
    rw [← hd]
    iapply (hS f fd name dqf dq d m) $$ [Hf Hfd Hm]
    · iframe; iframe #
    inext
    iintro %err ⟨Hf, Hfd, Hr, Herr⟩
    iapply HΦ $$ %err
    iframe Hf Hfd Herr
    icases Hr with (⟨%he, %c, Hm⟩ | ⟨%he, Hm⟩)
    · ileft
      isplitr
      · ipureintro; exact he
      iexists m.bsynced c, R
      rw [hd, bMeta_none hc]
      iframe
      ipureintro; exact ⟨rfl, rfl, RSame.refl R⟩
    · iright
      isplitr
      · ipureintro; exact he
      rw [hd]
      iframe
  | some c =>
    ihave #Hci := bCsInv_some p c hc $$ Hinv
    iunfold bMetaT at Hm
    icases bMetaG_own false p c hc C L m $$ Hm with ⟨%bs, %a, Hown, Ha, %Hf⟩
    obtain ⟨hph, hcur, hdur, hfs, -⟩ := Hf
    imod csOwnIL_ok c.N p.ino c.g c.ga c.gc bCsOk ⟨m, bs, 0, 0, .idle⟩ a ⊤ CoPset.subseteq_top
      $$ Hci Hown with ⟨Hown, %Hok⟩
    ihave %hlo := csOwnL_locOk (csTokI c.g c.ga a) p.ino ⟨m, bs, 0, 0, .idle⟩ $$ Hown
    have hbl : bs.length = m.size := hlo.1.1
    have hdq : p.dq (DFrac.own 1) = DFrac.own (1 : Qp).half := by unfold BFile.dq; rw [hc]; rfl
    icases (bRanges_os p R).1 $$ HR with ⟨HR, HG⟩
    rw [hdq]
    imod ranges_agree c.N p.ino c.g c.ga c.gc bCsOk ⟨m, bs, 0, 0, .idle⟩ a ⊤ CoPset.subseteq_top
      (DFrac.own (1 : Qp).half) R (fun r hr => by show _ ≤ bs.length; rw [hbl]; exact hin r hr)
      $$ Hci Hown HR with ⟨Hown, HR, %hag⟩
    have hruns : ∀ r ∈ R, r.1 + r.2.length ≤ bs.length ∧ r.2 = (bs.drop r.1).take r.2.length :=
      fun r hr => ⟨by rw [hbl]; exact hin r hr, hag r hr⟩
    ihave HR := (ranges_mask p.ino (DFrac.own (1 : Qp).half) bs R hruns hdisj).1 $$ HR
    have hok : bCsOk a (csSynced m [] [] bs 0 0) := fun hf =>
      bDur_sync_idle a hph m [] [] bs 0 0 (fun y hy => by cases hy) (by simpa using Hok.1 hf)
    have hcov' : ∀ b, b < m.size → m.dlo ≤ b → b < m.dhi →
        rMask R b = true ∨ ∃ x, bs[b]? = some x ∧ x = durB x.1 := by
      intro b hb _ _
      by_cases hL : ∃ r ∈ L, r.1 ≤ b ∧ b < r.1 + r.2
      · left; exact rMask_true.2 (hcov b hL hb)
      · right
        have hb' : b < bs.length := by omega
        refine ⟨bs[b], List.getElem?_eq_getElem hb', ?_⟩
        refine hdur b bs[b] (List.getElem?_eq_getElem hb') fun r hr => ?_
        apply Classical.byContradiction; intro hn
        exact hL ⟨r, hr, by omega, by omega⟩
    iapply (hSC f fd name dqf dq d c.N p.ino c.g c.ga c.gc bCsOk a m bs (rMask R) hd (hns c hc)
      hcov' hok) $$ [Hf Hfd Hown HR]
    · iframe; iframe #
    inext
    iintro %err ⟨Hf, Hfd, Hr⟩
    icases Hr with (⟨%he, Hown, HR⟩ | ⟨%he, -⟩)
    rotate_left
    · exact absurd hfs he.2
    subst he
    iapply HΦ $$ %interface.nil
    iframe Hf Hfd
    isplitl
    · ileft
      isplitr
      · ipureintro; rfl
      iexists m.synced, rDur R
      ihave HR := (ranges_mask p.ino (DFrac.own (1 : Qp).half) (bs.map (fun x => durB x.1)) (rDur R)
        (rDur_runs bs R hruns) (RDisj_rDur R hdisj)).2 $$ [HR]
      · have e : rMask (rDur R) = rMask R := by
          funext k
          simp [rMask, rDur, List.any_map, rIn, Function.comp_def]
        rw [e]; iexact HR
      have hGl : ([∗list] r ∈ R, bGhost (GF := GF) p r.1 (DFrac.own 1) r.2.length) ⊢
          [∗list] r ∈ rDur R, bGhost (GF := GF) p r.1 (DFrac.own 1) r.2.length := by
        unfold rDur
        rw [BigSepL.bigSepL_map]
        simp only [List.length_map]
        exact .rfl
      ihave HG := hGl $$ HG
      isplitl [Hown Ha]
      · iapply bMeta_of_own p c hc C [] m.synced (bs.map (fun x => durB x.1)) a
          ⟨hph, hcur, fun k x hk _ => by
            obtain ⟨y, -, rfl⟩ := List.mem_map.1 (List.mem_of_getElem? hk); rfl, hfs, xsOne_synced m⟩
          $$ [Hown Ha]
        iframe
      isplitl [HR HG]
      · iapply (bRanges_os p (rDur R)).2; rw [hdq]; iframe
      ipureintro; exact ⟨rfl, rfl, RSame_rDur R⟩
    unfold fmtErrorOkOrNil; itrivial

end res

end bbolt
end EtcdGrove
end Perennial
