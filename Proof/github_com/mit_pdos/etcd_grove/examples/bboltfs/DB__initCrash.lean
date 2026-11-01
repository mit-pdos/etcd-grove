/- Lean-first (no Rocq counterpart). The proof of `db.init()`'s crash-aware spec
(`DB.init.specCrash`): `DB__init.lean`'s, step by step, over the crash invariant. Each `WriteAt`
is `os.File.WriteAt.specCrashS`, whose obligation is `initW1_obl`, then `initW2_obl`; its post
gives the state the write reached (`WReach`), whose bytes `narrow_full0` computes on success. Each
`Fdatasync` is `syscall.Fdatasync.specCrashS` with nothing kept or frozen (`H = F = []`): on
success `initSync_ok`, on failure the write's last state, `initIdle`/`initMid` (which ignore
`ok`). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__initCrash
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__init
public import Proof.os.CrashStSpec

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section pure
variable [GooseExts]

/-- A write at 0 that succeeded: the size is the old one or the data's end, and the bytes are the
data, then the old ones past it. -/
theorem narrow_full0 {m m' : OsMeta} {bs bs' : List (w8 × Bool)} {D : List w8}
    (hN : Narrow m bs 0 D m' bs') (hl : bs.length = m.size) (hD : D.length ≤ m'.size)
    (hd : ∀ i < D.length, (bs'[0 + i]?).map Prod.fst = D[i]?) :
    m'.size = max m.size D.length ∧ bs'.map Prod.fst = D ++ (bs.map Prod.fst).drop D.length := by
  have h1 := hN.size
  have h2 := hN.szhi
  refine ⟨by omega, List.ext_getElem? fun i => ?_⟩
  rw [List.getElem?_map]
  by_cases hi : i < D.length
  · rw [List.getElem?_append_left hi, ← hd i hi, Nat.zero_add]
  · rw [List.getElem?_append_right (by omega), List.getElem?_drop, List.getElem?_map]
    by_cases hm : D.length ≤ m.size
    · rw [hN.suf (by omega) i (by omega), show D.length + (i - D.length) = i by omega]
    · rw [List.getElem?_eq_none (show bs'.length ≤ i by rw [hN.len]; omega),
        List.getElem?_eq_none (show bs.length ≤ D.length + (i - D.length) by omega)]

/-- A synced state whose name, `ok` and mappings are `m`'s. -/
theorem synced_eq {m m' : OsMeta} (h1 : m'.named = m.named) (h2 : m'.ok = m.ok)
    (h3 : m'.maps = m.maps) (hok : m.ok = true) (bs : List (w8 × Bool)) :
    m'.synced 0 bs =
      { m with size := m'.size, lo := m'.size, hi := m'.size, dur := durOf 0 bs,
               durHi := m'.size } := by
  cases m; cases m'; simp_all [OsMeta.synced]

/-- After a successful sync with nothing kept or frozen. -/
theorem csSynced_nil (m : OsMeta) (bs : List (w8 × Bool)) (hok : m.ok = true) :
    csSynced false m [] [] bs 0 0 = ⟨m.synced 0 bs, bs.map (fun x => (x.1, true)), 0, 0, .idle⟩ := by
  have e : m.syncedKeep 0 bs 0 [] = m.synced 0 bs := by
    simp only [OsMeta.syncedKeep, durOf, List.replicate_zero, List.nil_append, List.map_nil]
    rw [show ∀ a : List (Option w8), durOverlay a [] = a from fun a => by cases a <;> rfl]
  simp only [csSynced, List.nil_append, e, syncedBytes, hok, if_true]

theorem initBytes_page3 (k : Nat) (hk : k < 4096) :
    initBytes[4096 * 3 + k]? = some ((emptyPageBytes (W64 3) (W16 2))[k]?.getD 0) := by
  have h0 := metaPageBytes_length 0
  have h1 := metaPageBytes_length 1
  have h2 := emptyPageBytes_length (W64 2) (W16 16)
  have h3 := emptyPageBytes_length (W64 3) (W16 2)
  simp only [pageBytes] at h0 h1 h2 h3
  unfold initBytes
  rw [List.getElem?_append_right (by simp only [List.length_append]; omega)]
  simp only [List.length_append, h0, h1, h2]
  rw [show 4096 * 3 + k - (4096 + 4096 + 4096) = k by omega, List.getElem?_eq_getElem (by omega)]
  rfl

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

theorem DB.init.wp_proof_crash (wp_initPages : initPages.spec (GF := GF) (hG := hG))
    (wp_WriteAt : os.File.WriteAt.specCrashS (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Fdatasync : syscall.Fdatasync.specCrashS (GF := GF) (hG := hG)) :
    DB.init.specCrash (GF := GF) (hG := hG) := by
  intro db f fd p dqf dq N γ m xs hok hmaps hsz hI hcl hN
  have hil := initBytes_length
  simp only [pageBytes] at hil
  wp_start as ⟨#Hinv, #Hcs, #Hfile, Hfsz, Hf, Hfd, Hown⟩
  icases csOwn_wf' _ _ _ $$ Hown with ⟨Hown, %Hwf⟩
  have hxs : xs.length = m.size := Hwf.1
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) (W64 16384)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  wp_apply wp_initPages buf $$ [Hbuf] as Hbuf
  · iexact Hbuf
  (try wp_auto)
  ihave %Hbl := ownSlice_len $$ Hbuf
  have hbl : buf.len = W64 16384 := by
    have h1 := Hbl.1; rw [initBytes_length] at h1
    have h2 := Hbl.2
    have h3 : (sint.Z buf.len).toNat = 16384 := h1.symm
    have : sint.Z buf.len = 16384 := by omega
    word
  ihave %Hwf := ownSlice_wf $$ Hbuf
  wp_apply (wp_slice_make2 (V := w8) (W64 16384)) as %first ⟨Hfirst, -⟩
  · ipureintro; decide
  (try wp_auto)
  ihave %Hfl := ownSlice_len $$ Hfirst
  have hfl : first.len = W64 16384 := by
    have h1 := Hfl.1; rw [List.length_replicate] at h1
    have h2 := Hfl.2
    have h3 : (sint.Z first.len).toNat = 16384 := h1.symm
    have : sint.Z first.len = 16384 := by omega
    word
  ihave %Hfwf := ownSlice_wf $$ Hfirst
  rw [ite_eq_left (by rw [hfl]; exact ⟨by decide, by decide, by rw [← hfl]; exact Hfwf.2⟩)]
  (try wp_auto)
  rw [ite_eq_left (by rw [hbl]; exact ⟨by decide, by decide, by rw [← hbl]; exact Hwf.2⟩)]
  (try wp_auto)
  icases (ownSlice_split_all (W64 8192) buf _ _ ⟨by decide, by rw [hbl]; decide⟩).1 $$ Hbuf
    with ⟨Hbuf1, Hbuf2⟩
  icases (ownSlice_split_all (W64 8192) first _ _ ⟨by decide, by rw [hfl]; decide⟩).1 $$ Hfirst
    with ⟨Hfirst1, Hfirst2⟩
  have h8 : sint.nat (W64 8192) = 8192 := rfl
  rw [h8]
  generalize hI0 : initBytes = I at hil ⊢
  have hIl : (I.drop 8192).length = 8192 := by rw [List.length_drop]; omega
  have hZ1 : (List.replicate 16384 (zero_val w8)).take 8192 = List.replicate 8192 (zero_val w8) := by
    rw [List.take_replicate, show min 8192 16384 = 8192 from rfl]
  have hZ2 : (List.replicate 16384 (zero_val w8)).drop 8192 = List.replicate 8192 (zero_val w8) := by
    rw [List.drop_replicate, show 16384 - 8192 = 8192 from rfl]
  rw [hZ1, hZ2]
  generalize hZ : List.replicate 8192 (zero_val w8) = Z
  have hZl : Z.length = 8192 := by rw [← hZ, List.length_replicate]
  wp_apply wp_slice_copy (slice.slice first w8 (W64 8192) first.len) Z
      (slice.slice buf w8 (W64 8192) buf.len) (I.drop 8192) (DFrac.own 1) $$ [Hfirst2 Hbuf2]
    as %nc ⟨%_hnc, Hfirst2, Hbuf2⟩
  · isplitl [Hfirst2]
    · iexact Hfirst2
    · iexact Hbuf2
  rw [hZl, hIl, List.take_of_length_le (Nat.le_of_eq hIl), List.drop_of_length_le (Nat.le_of_eq hZl),
    List.append_nil]
  ihave Hfirst := (ownSlice_split_all (W64 8192) first (DFrac.own 1) (Z ++ I.drop 8192)
      ⟨by decide, by rw [hfl]; decide⟩).2 $$ [Hfirst1 Hfirst2]
  · rw [h8, List.take_left' hZl, List.drop_left' hZl]; iframe
  have hF : (Z ++ I.drop 8192).length = 16384 := by rw [List.length_append, hZl, hIl]
  have hFz : ∀ k < 8192, (Z ++ I.drop 8192)[k]? = some 0 := by
    intro k hk
    rw [List.getElem?_append_left (by omega), ← hZ, List.getElem?_replicate, if_pos hk]; rfl
  have hF3 : ∀ k < 4096, (Z ++ I.drop 8192)[4096 * 3 + k]? =
      some ((emptyPageBytes (W64 3) (W16 2))[k]?.getD 0) := by
    intro k hk
    rw [List.getElem?_append_right (by omega), hZl, List.getElem?_drop,
      show 8192 + (4096 * 3 + k - 8192) = 4096 * 3 + k by omega, ← hI0]
    exact initBytes_page3 k hk
  generalize hFd : Z ++ I.drop 8192 = F at hF hFz hF3 ⊢
  have hw00 : (W64 0).toNat = 0 := rfl
  have hw0' : 0 ≤ (W64 0).toInt := by word
  have hmc : ∀ (mm : OsMeta), mm.maps = ∅ → ∀ lo hi, mcellsAny (GF := GF) mm.maps lo hi ⊣⊢ emp := by
    intro mm hmm lo hi; unfold mcellsAny; rw [hmm]; exact BigSepM.bigSepM_empty
  ihave Hc := (hmc m hmaps (cfLo m (W64 0).toNat) ((W64 0).toNat + F.length)).2 $$ []
  · iempintro
  have hW1 : ∀ m' bs', WReach m xs (W64 0).toNat F m' bs' →
      CrashOkS (P1 p) p Good (some ⟨m', bs', 0, 0, .idle⟩) ∧
      ∀ t, CrashOkS (P1 p) p Good (some ⟨m', bs', 0, 0, .write t (W64 0).toNat F⟩) := by
    rw [hw00]; exact initW1_obl hI hxs hcl (by omega) (by omega) hFz 0 0
  wp_apply wp_WriteAt f fd p dqf first F (DFrac.own 1) (W64 0) dq ⟨p, true, true⟩ N γ
      (CrashOkS (P1 p) p Good) m xs 0 0 rfl hw0' (by omega) (by omega) hN (.inr (Nat.zero_le _))
      hW1 $$ [Hinv Hcs Hf Hfirst Hfd Hown Hc]
    as %n %err ⟨Hf, Hfirst, Hfd, Hc, %m1, %bs1, %Hres, Hown⟩
  · iframe Hf Hfirst Hfd Hown Hc; iframe #
  rw [hw00] at Hres
  obtain ⟨hR1, ⟨rfl, rfl, hsz1, hd1⟩ | ⟨rfl, hne⟩⟩ := Hres
  rotate_left
  · cases err with
    | nil => exact absurd rfl hne
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    iframe Hf Hfd
    iright
    isplitr
    · ipureintro; exact hne
    · iexists _, _; iframe
  have hN1 := hR1.narrow hxs
  have hl1 := hN1.len
  obtain ⟨hs1, hb1⟩ := narrow_full0 hN1 hxs (by omega) hd1
  rw [hF] at hs1 hb1
  have hI1 := initIdle_wreach hI hxs hR1 hcl (by omega) (by omega) hFz
  (try wp_auto)
  wp_apply wp_Fd f fd p dqf $$ [Hf] as Hf
  · iexact Hf
  (try wp_auto)
  have hok1 : m1.ok = true := by rw [hN1.ok]; exact hok
  have hb1i : ∀ i : Nat, (bs1.map Prod.fst)[i]? = (F ++ (xs.map Prod.fst).drop 16384)[i]? := by
    intro i; rw [hb1]
  have hS1 : CrashOkS (P1 p) p Good (some (csSynced false m1 [] [] bs1 0 0)) := by
    refine initSync_ok hok1 hl1 (by omega) (by omega) (fun i hi hv => ?_) (fun k hk => ?_)
    · refine absurd hv (slot_zero_invalid fun k hk => ?_)
      rw [hb1i, List.getElem?_append_left (by omega), hFz _ (by omega)]
    · rw [← List.getElem?_map, hb1i, List.getElem?_append_left (by omega), hF3 k hk]
  have hF1 : CrashOkS (P1 p) p Good (some ⟨{ m1 with ok := false }, [] ++ ([] ++ bs1), 0, 0, .idle⟩) :=
    initIdle_okS ⟨{ m1 with ok := false }, bs1, 0, 0, .idle⟩ hl1 rfl (initIdle_notOk hI1)
  ihave Hown := (show csOwn (GF := GF) p γ (some ⟨m1, bs1, 0, 0, .idle⟩) ⊢
      csOwn (GF := GF) p γ (some ⟨m1, [] ++ ([] ++ bs1), 0, 0, .idle⟩) from .rfl) $$ Hown
  wp_apply wp_Fdatasync fd dq ⟨p, true, true⟩ N γ (CrashOkS (P1 p) p Good) m1 [] [] bs1 0 0 false
      rfl rfl (by simp) hN hS1 hF1 $$ [Hinv Hcs Hfd Hown] as %e ⟨Hfd, Hs⟩
  · iframe Hfd Hown; iframe #
  icases Hs with (⟨%He, Hown⟩ | ⟨%He, Hown⟩)
  rotate_left
  · unfold errnoErr; rw [if_neg He]
    (try wp_auto)
    iapply HΦ
    iframe Hf Hfd
    iright
    isplitr
    · ipureintro; simp
    · iexists _, _; iframe
  subst He
  unfold errnoErr; rw [if_pos rfl]
  (try wp_auto)
  rw [csSynced_nil m1 bs1 hok1]
  -- the file after the first write and sync
  have hsy1 := initMid_synced hok1 hl1 (by omega) (by omega)
    (fun i hi hv => absurd hv (slot_zero_invalid fun k hk => by
      rw [hb1i, List.getElem?_append_left (by omega), hFz _ (by omega)]))
    (fun k hk => by rw [← List.getElem?_map, hb1i, List.getElem?_append_left (by omega), hF3 k hk])
  simp only [syncedBytes, hok1, if_true] at hsy1
  obtain ⟨hM1, -⟩ := hsy1
  generalize hM1d : m1.synced 0 bs1 = M1 at hM1 ⊢
  generalize hA : bs1.map (fun x => (x.1, true)) = A at hM1 ⊢
  have hM1s : M1.size = max m.size 16384 := by rw [← hM1d]; simp [OsMeta.synced, hs1]
  have hM1m : M1.maps = ∅ := by rw [← hM1d]; simp [OsMeta.synced, hN1.maps, hmaps]
  have hM1ok : M1.ok = true := by rw [← hM1d]; exact hok1
  have hAl : A.length = M1.size := by rw [← hA, List.length_map, hl1, ← hM1d]; rfl
  have hAcl : ∀ i < 2, ∀ k < 64, ∀ x, A[4096 * i + 16 + k]? = some x → x.2 = true := by
    intro i _ k _ x hx
    rw [← hA, List.getElem?_map] at hx
    cases hy : bs1[4096 * i + 16 + k]? with
    | none => rw [hy] at hx; cases hx
    | some y => rw [hy] at hx; cases hx; rfl
  have hAfst : A.map Prod.fst = F ++ (xs.map Prod.fst).drop 16384 := by
    rw [← hA, List.map_map, ← hb1]; rfl
  have hcap : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 8192) ∧
      sint.Z (W64 8192) ≤ sint.Z buf.cap := by
    have := Hwf.2; rw [hbl, show sint.Z (W64 16384) = 16384 from rfl] at this
    rw [show sint.Z (W64 8192) = 8192 from rfl, show sint.Z (W64 0) = 0 from rfl]
    exact ⟨by decide, by decide, by omega⟩
  rw [ite_eq_left hcap]
  (try wp_auto)
  have htl : (I.take 8192).length = 8192 := by rw [List.length_take]; omega
  have hDs : ∀ i < 2, fileMeta (I.take 8192) i =
      github_com.mit_pdos.etcd_grove.examples.bboltfs.initMeta i := by
    intro i hi
    rw [fileMeta_take _ _ _ (by omega), ← hI0]
    rcases i with _ | _ | i
    · exact initBytes_meta0
    · exact initBytes_meta1
    · omega
  ihave Hc := (hmc M1 hM1m (cfLo M1 (W64 0).toNat) ((W64 0).toNat + (I.take 8192).length)).2 $$ []
  · iempintro
  have hW2 : ∀ m' bs', WReach M1 A (W64 0).toNat (I.take 8192) m' bs' →
      CrashOkS (P1 p) p Good (some ⟨m', bs', 0, 0, .idle⟩) ∧
      ∀ t, CrashOkS (P1 p) p Good (some ⟨m', bs', 0, 0, .write t (W64 0).toNat (I.take 8192)⟩) := by
    rw [hw00]; exact initW2_obl hM1 hAl hAcl htl hDs (by omega) 0 0
  wp_apply wp_WriteAt f fd p dqf (slice.slice buf w8 (W64 0) (W64 8192)) (I.take 8192)
      (DFrac.own 1) (W64 0) dq ⟨p, true, true⟩ N γ (CrashOkS (P1 p) p Good) M1 A 0 0 rfl hw0'
      (by omega) (by omega) hN (.inr (Nat.zero_le _)) hW2 $$ [Hinv Hcs Hf Hbuf1 Hfd Hown Hc]
    as %n2 %err2 ⟨Hf, Hbuf1, Hfd, Hc, %m2, %bs2, %Hres2, Hown⟩
  · iframe Hf Hbuf1 Hfd Hown Hc; iframe #
  rw [hw00] at Hres2
  obtain ⟨hR2, ⟨rfl, rfl, hsz2, hd2⟩ | ⟨rfl, hne2⟩⟩ := Hres2
  rotate_left
  · cases err2 with
    | nil => exact absurd rfl hne2
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    iframe Hf Hfd
    iright
    isplitr
    · ipureintro; exact hne2
    · iexists _, _; iframe
  have hN2 := hR2.narrow hAl
  have hl2 := hN2.len
  obtain ⟨hs2, hb2⟩ := narrow_full0 hN2 hAl (by omega) hd2
  rw [htl] at hs2 hb2
  obtain ⟨hM2, hc2⟩ := initW2_reach hM1 hAl hAcl htl hDs (by omega) hR2
  (try wp_auto)
  wp_apply wp_Fd f fd p dqf $$ [Hf] as Hf
  · iexact Hf
  (try wp_auto)
  have hok2 : m2.ok = true := by rw [hN2.ok]; exact hM1ok
  have hb2i : ∀ i : Nat, (bs2.map Prod.fst)[i]? = (I.take 8192 ++ (A.map Prod.fst).drop 8192)[i]? := by
    intro i; rw [hb2]
  have hS2 : CrashOkS (P1 p) p Good (some (csSynced false m2 [] [] bs2 0 0)) := by
    refine initSync_ok hok2 hl2 (by omega) (by omega) (fun i hi _ => ?_) (fun k hk => ?_)
    · rw [hb2, ← fileMeta_take _ 8192 _ (by omega), List.take_left' htl, hDs i hi]
    · rw [← List.getElem?_map, hb2i, List.getElem?_append_right (by omega), htl,
        List.getElem?_drop, show 8192 + (4096 * 3 + k - 8192) = 4096 * 3 + k by omega,
        List.getElem?_map, hM1.page3 k hk]
      rfl
  have hF2 : CrashOkS (P1 p) p Good (some ⟨{ m2 with ok := false }, [] ++ ([] ++ bs2), 0, 0, .idle⟩) :=
    initMid_okS ⟨{ m2 with ok := false }, bs2, 0, 0, .idle⟩ hl2 rfl (initMid_notOk hM2) hc2
  ihave Hown := (show csOwn (GF := GF) p γ (some ⟨m2, bs2, 0, 0, .idle⟩) ⊢
      csOwn (GF := GF) p γ (some ⟨m2, [] ++ ([] ++ bs2), 0, 0, .idle⟩) from .rfl) $$ Hown
  wp_apply wp_Fdatasync fd dq ⟨p, true, true⟩ N γ (CrashOkS (P1 p) p Good) m2 [] [] bs2 0 0 false
      rfl rfl (by simp) hN hS2 hF2 $$ [Hinv Hcs Hfd Hown] as %e ⟨Hfd, Hs⟩
  · iframe Hfd Hown; iframe #
  icases Hs with (⟨%He, Hown⟩ | ⟨%He, Hown⟩)
  rotate_left
  · unfold errnoErr; rw [if_neg He]
    (try wp_auto)
    iapply HΦ
    iframe Hf Hfd
    iright
    isplitr
    · ipureintro; simp
    · iexists _, _; iframe
  subst He
  unfold errnoErr; rw [if_pos rfl]
  (try wp_auto)
  rw [csSynced_nil m2 bs2 hok2]
  have hfin : bs2.map (fun x => (x.1, true)) = initFile xs := by
    have key : bs2.map Prod.fst = I ++ (xs.map Prod.fst).drop 16384 := by
      rw [hb2, hAfst, ← hFd, List.append_assoc, List.drop_left' hZl, ← List.append_assoc,
        List.take_append_drop]
    unfold initFile
    rw [hI0, ← key, List.map_map]; rfl
  have hm2 : m2.synced 0 bs2 = initDoneMeta m xs := by
    have hnm : M1.named = m.named := by rw [← hM1d]; simp [OsMeta.synced, hN1.named]
    have hmm : M1.maps = m.maps := by rw [hM1m, hmaps]
    rw [synced_eq (hN2.named.trans hnm) (hN2.ok.trans (hM1ok.trans hok.symm))
      (hN2.maps.trans hmm) hok]
    unfold initDoneMeta
    rw [← hfin, durOf_map_clean, hs2, hM1s,
      show max (max m.size 16384) 8192 = max m.size 16384 by omega]
  rw [hm2, hfin]
  have hsz64 : sint.Z (W64 (m.size : Int)) = m.size := by
    have : (m.size : Int) < 2 ^ 63 := by omega
    word
  wp_if_destruct
  · iapply HΦ
    iframe Hf Hfd
    ileft
    isplitr
    · ipureintro; rfl
    · rw [hsz64, show sint.Z (W64 16384) = 16384 from rfl] at Hif
      rw [show max (m.size : Int) 16384 = 16384 by omega]
      iframe
  · iapply HΦ
    iframe Hf Hfd
    ileft
    isplitr
    · ipureintro; rfl
    · rw [hsz64, show sint.Z (W64 16384) = 16384 from rfl] at Hif
      rw [show max (m.size : Int) 16384 = m.size by omega]
      iframe

end proof

end bboltfs
end EtcdGrove
end Perennial
