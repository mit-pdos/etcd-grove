/- Lean-first (no Rocq counterpart). The proof of `db.init()`'s crash-aware spec
(`DB.init.specCrash`): `DB__init.lean`'s, step by step, over the crash invariant. Each `WriteAt`
is `os.File.WriteAt.specCrashS` with the no-tear cut (`NoTearCut`, `pwCut_noTear`), whose obligation
is `initW1_okS` (the first write: `initW1St_of_wreach`), then `initMid_okS`/`initMidW_okS` of phase
`false` (meta 1 at 4096) and of phase `true` (meta 0 at 0), through `initMid_wreach`; its post gives
the state the write reached (`WReach`), whose bytes `narrow_full0`/`narrow_mid` compute on
success. Each `Fdatasync` is `syscall.Fdatasync.specCrashS` with nothing kept or frozen
(`H = F = []`): on success `initMid_synced`, on failure the write's last state (`initW1St.notOk`,
`initMid.notOk`). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__initCrash
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__init
public import Proof.os.CrashStSpec

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs
open Fs

section pure
variable [GooseExts]

/-- A write at 0 that succeeded: the size is the old one or the data's end, and the bytes are the
data, then the old ones past it. -/
theorem narrow_full0 {m m' : OsMeta} {bs bs' : List ByteG} {D : List w8}
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

/-- A write inside the file that succeeded: the bytes before it, the data, the bytes after it. -/
theorem narrow_mid {m m' : OsMeta} {bs bs' : List ByteG} {off : Nat} {D : List w8}
    (hN : Narrow m bs off D m' bs') (hl : bs.length = m.size) (hin : off + D.length ≤ m.size)
    (hd : ∀ i < D.length, (bs'[off + i]?).map Prod.fst = D[i]?) :
    m'.size = m.size ∧
      bs'.map Prod.fst = (bs.map Prod.fst).take off ++ D ++ (bs.map Prod.fst).drop (off + D.length) := by
  have h1 := hN.size
  have h2 := hN.szhi
  have hsz : m'.size = m.size := by omega
  refine ⟨hsz, List.ext_getElem? fun i => ?_⟩
  rw [List.getElem?_map]
  by_cases hi : i < off
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
      List.getElem?_take, if_pos hi, List.getElem?_map, hN.pre _ (by simp only [cfLo]; omega)]
  · by_cases hj : i < off + D.length
    · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp; omega),
        List.length_take, show i - min off (bs.map Prod.fst).length = i - off by simp; omega,
        show i = off + (i - off) by omega, hd _ (by omega)]
      congr 1; omega
    · rw [List.getElem?_append_right (by simp; omega), List.getElem?_drop, List.getElem?_map,
        List.length_append, List.length_take, List.length_map,
        show off + D.length + (i - (min off bs.length + D.length)) = i by omega,
        hN.suf hin _ (by omega)]

/-- `map Prod.fst` of a byte read back, clean. -/
theorem map_clean_getElem {bs : List ByteG} {j : Nat} {b : w8}
    (h : (bs.map Prod.fst)[j]? = some b) : (bs.map fun x => (x.1, true))[j]? = some (b, true) := by
  rw [List.getElem?_map] at h ⊢
  cases hx : bs[j]? with
  | none => rw [hx] at h; cases h
  | some x => rw [hx] at h; simp only [Option.map_some, Option.some.injEq] at h ⊢; rw [h]

/-- A synced state whose `ok` and mappings are `m`'s. -/
theorem synced_eq {m m' : OsMeta} (h2 : True) (h3 : m'.maps = m.maps) (hok : True)
    (bs : List ByteG) :
    m'.synced 0 bs =
      { m with size := m'.size, lo := m'.size, hi := m'.size, dur := durOf 0 bs,
               vk := some [], dz := some (pageUp m'.size) } := by
  cases m; cases m'; simp_all [OsMeta.synced]

/-- After a successful sync with nothing kept or frozen. -/
theorem csSynced_nil (m : OsMeta) (bs : List ByteG) (hok : True) :
    csSynced false m [] [] bs 0 0 = ⟨m.synced 0 bs, bs.map (fun x => (x.1, true)), 0, 0, .idle⟩ := by
  have e : m.syncedKeep 0 bs 0 [] = m.synced 0 bs := by
    simp only [OsMeta.syncedKeep, durOf, List.replicate_zero, List.nil_append, List.map_nil]
    rw [show ∀ a : List (Option w8), durOverlay a [] = a from fun a => by cases a <;> rfl]
  simp only [csSynced, List.nil_append, syncedBytes, hok, if_true, e]

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

/-- The state of a write's attempt, as the obligation of `os.File.WriteAt.specCrashS` sees it. -/
theorem wf_idle00 (m : OsMeta) (bs : List ByteG) (hl : bs.length = m.size) :
    (⟨m, bs, 0, 0, .idle⟩ : CSt).Wf :=
  ⟨hl, Nat.le_refl _, Nat.zero_le _, trivial⟩

theorem wf_write00 (m : OsMeta) (bs : List ByteG) (t off : Nat) (data : List w8)
    (hl : bs.length = m.size) : (⟨m, bs, 0, 0, .write t off data⟩ : CSt).Wf :=
  ⟨hl, Nat.le_refl _, Nat.zero_le _, .inr (Nat.zero_le _)⟩

/-- `init`'s meta write of phase `ph`'s obligation: every state it reaches from a synced
`initMid ph` state. -/
theorem initW_obl {ph : Bool} {i : Ino} {m : OsMeta} {bs : List ByteG} {D : List w8}
    (h : initMid ph m bs) (hvk : m.vk = some []) (hD : initWData ph D) :
    ∀ nn m' bs', WReach NoTearCut m bs (4096 * initSlot ph) D nn m' bs' →
      dbOk (some (i, ⟨m', bs', 0, 0, .idle⟩)) ∧ (nn < D.length → ∀ t,
        dbOk (some (i, ⟨m', bs', 0, 0, .write t (4096 * initSlot ph + nn) (D.drop nn)⟩))) := by
  intro nn m' bs' hR
  obtain ⟨hm, hnn, -⟩ := initMid_wreach h hvk hD hR
  refine ⟨initMid_okS _ (wf_idle00 _ _ hm.len) rfl hm, fun hlt t => ?_⟩
  have h0 : nn = 0 := by have := hD.1; omega
  subst h0
  simp only [Nat.add_zero, List.drop_zero]
  exact initMidW_okS _ (wf_write00 _ _ _ _ _ hm.len) rfl hm hD

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [FsStepSat NoTearStep]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Assumptions]

set_option maxRecDepth 20000 in
theorem DB.init.wp_proof_crash (wp_initPages : initPages.spec (GF := GF) (hG := hG))
    (wp_WriteAt : os.File.WriteAt.specCrashS (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Fdatasync : syscall.Fdatasync.specCrashS (GF := GF) (hG := hG)) :
    DB.init.specCrash (GF := GF) (hG := hG) := by
  intro db f fd p dqf dq N P R γ i m xs hok hmaps hsz hI hN
  have hil := initBytes_length
  simp only [pageBytes] at hil
  have hil0 : initBytes.length = 16384 := by omega
  wp_start as ⟨#Hinv, #Hcs, #Hfile, Hfsz, Hf, Hfd, Hown⟩
  have hxs : xs.length = m.size := hI.len
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
  have hFz' : ∀ k < 8192, (Z ++ I.drop 8192).getD k 0 = 0 := by
    intro k hk; rw [List.getD_eq_getElem?_getD, hFz k hk]; rfl
  have hF3 : ∀ k < 4096, (Z ++ I.drop 8192)[4096 * 3 + k]? =
      some ((emptyPageBytes (W64 3) (W16 2))[k]?.getD 0) := by
    intro k hk
    rw [List.getElem?_append_right (by omega), hZl, List.getElem?_drop,
      show 8192 + (4096 * 3 + k - 8192) = 4096 * 3 + k by omega, ← hI0]
    exact initBytes_page3 k hk
  generalize hFd : Z ++ I.drop 8192 = F at hF hFz hFz' hF3 ⊢
  have hw00 : (W64 0).toNat = 0 := rfl
  have hw0' : 0 ≤ (W64 0).toInt := by word
  have hmc : ∀ (mm : OsMeta), mm.maps = ∅ → ∀ lo hi, mcellsAny (GF := GF) mm.maps lo hi ⊣⊢ emp := by
    intro mm hmm lo hi; unfold mcellsAny; rw [hmm]; exact BigSepM.bigSepM_empty
  ihave Hc := (hmc m hmaps (W64 0).toNat ((W64 0).toNat + F.length)).2 $$ []
  · iempintro
  have hW1 : ∀ nn m' bs', WReach NoTearCut m xs (W64 0).toNat F nn m' bs' →
      dbOk (some (i, ⟨m', bs', 0, 0, .idle⟩)) ∧ (nn < F.length → ∀ t,
        dbOk (some (i, ⟨m', bs', 0, 0, .write t ((W64 0).toNat + nn) (F.drop nn)⟩))) := by
    rw [hw00]
    intro nn m' bs' hR
    have hst := initW1St_of_wreach hI hF hR
    refine ⟨initW1_okS _ (wf_idle00 _ _ hst.len) hI hF hFz' hst rfl rfl (.inl rfl),
      fun hlt t => ?_⟩
    rw [Nat.zero_add]
    exact initW1_okS _ (wf_write00 _ _ _ _ _ hst.len) hI hF hFz' hst rfl rfl
      (.inr ⟨t, rfl, by rw [hF] at hlt; exact hlt⟩)
  wp_apply wp_WriteAt f fd p dqf first F (DFrac.own 1) (W64 0) dq ⟨i, true, true⟩ N P R γ Good
      dbOk m xs 0 0 NoTearCut pwCut_noTear rfl hw0' (by rw [hw00]; omega) (by rw [hw00, hF]; omega)
      (by rw [hF]; omega) (by rw [hF]; omega) hN (.inr (Nat.zero_le _)) hW1
      $$ [Hinv Hcs Hf Hfirst Hfd Hown Hc]
    as %n %err ⟨Hf, Hfirst, Hfd, Hc, %nn1, %m1, %bs1, %Hres, Hown⟩
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
  have hN1 := hR1.narrow hxs (Nat.zero_le _)
  have hl1 := hN1.len
  obtain ⟨hs1, hb1⟩ := narrow_full0 hN1 hxs (by omega) hd1
  rw [hF] at hs1 hb1
  have hst1 := initW1St_of_wreach hI hF hR1
  obtain ⟨-, -, hok1, hmaps1, -⟩ := hR1.meta_keep
  (try wp_auto)
  wp_apply wp_Fd f fd p dqf $$ [Hf] as Hf
  · iexact Hf
  (try wp_auto)
  have hok1' : True := by rw [hok1]; exact hok
  have hb1i : ∀ j : Nat, (bs1.map Prod.fst)[j]? = (F ++ (xs.map Prod.fst).drop 16384)[j]? := by
    intro j; rw [hb1]
  have hord1 : initOrd false (bs1.map fun x => (x.1, true)) := by
    intro k hk
    refine map_clean_getElem ?_
    rw [hb1i, List.getElem?_append_left (by simp only [initSlot]; omega),
      hFz _ (by simp only [initSlot]; omega)]
    rfl
  have hsy1 := initMid_synced (ph := false) hok1' hl1 (by omega) (by omega)
    (fun j hj hv => absurd hv (slot_zero_invalid fun k hk => by
      rw [hb1i, List.getElem?_append_left (by omega), hFz _ (by omega)]))
    (fun k hk => by rw [← List.getElem?_map, hb1i, List.getElem?_append_left (by omega), hF3 k hk])
    hord1
  have hS1 : dbOk (some (i, csSynced false m1 [] [] bs1 0 0)) := by
    rw [csSynced_nil m1 bs1 hok1']
    exact initMid_okS _ (wf_idle00 _ _ hsy1.1.len) rfl hsy1.1
  have hF1 : dbOk (some (i, ⟨m1, [] ++ ([] ++ bs1), 0, 0, .idle⟩)) :=
    initW1_okS _ (wf_idle00 _ _ hl1) hI hF hFz' hst1.notOk rfl rfl (.inl rfl)
  ihave Hown := (show csOwnF (GF := GF) γ (some (i, ⟨m1, bs1, 0, 0, .idle⟩)) ⊢
      csOwnF (GF := GF) γ (some (i, ⟨m1, [] ++ ([] ++ bs1), 0, 0, .idle⟩)) from .rfl) $$ Hown
  wp_apply wp_Fdatasync fd dq ⟨i, true, true⟩ N P R γ Good dbOk m1 [] [] bs1 0 0 false
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
  rw [csSynced_nil m1 bs1 hok1']
  obtain ⟨hM1, hM1vk⟩ := hsy1
  generalize hM1d : m1.synced 0 bs1 = M1 at hM1 hM1vk ⊢
  generalize hA : bs1.map (fun x => (x.1, true)) = A at hM1 ⊢
  have hM1s : M1.size = max m.size 16384 := by rw [← hM1d]; simp [OsMeta.synced, hs1]
  have hM1m : M1.maps = ∅ := by rw [← hM1d]; simp [OsMeta.synced, hmaps1, hmaps]
  have hM1ok : True := by rw [← hM1d]; exact hok1'
  have hAl : A.length = M1.size := by rw [← hA, List.length_map, hl1, ← hM1d]; rfl
  have hAfst : A.map Prod.fst = F ++ (xs.map Prod.fst).drop 16384 := by
    rw [← hA, List.map_map, ← hb1]; rfl
  -- the second write: meta 1 (`buf[4096:8192]`) at 4096, phase `false`
  have hcap : 0 ≤ sint.Z (W64 4096) ∧ sint.Z (W64 4096) ≤ sint.Z (W64 8192) ∧
      sint.Z (W64 8192) ≤ sint.Z buf.cap := by
    have := Hwf.2; rw [hbl, show sint.Z (W64 16384) = 16384 from rfl] at this
    rw [show sint.Z (W64 8192) = 8192 from rfl, show sint.Z (W64 4096) = 4096 from rfl]
    exact ⟨by decide, by decide, by omega⟩
  rw [ite_eq_left hcap]
  (try wp_auto)
  icases (ownSlice_split (W64 4096) buf (DFrac.own 1) (I.take 8192) (W64 0) (W64 8192)
      ⟨by decide, by decide, by decide⟩).1 $$ Hbuf1 with ⟨Hbuf0, Hbuf1⟩
  rw [show sint.nat (W64 4096) - sint.nat (W64 0) = 4096 from rfl]
  have hDd1 : initWData false ((I.take 8192).drop 4096) := by
    refine ⟨by simp only [List.length_drop, List.length_take]; omega, fun k hk => ?_⟩
    simp only [initSlot, List.getElem?_drop, List.getElem?_take]
    rw [if_pos (by omega), ← hI0]
    congr 1; omega
  have hDd0 : initWData true ((I.take 8192).take 4096) := by
    refine ⟨by simp only [List.length_take]; omega, fun k hk => ?_⟩
    simp only [initSlot, List.getElem?_take]
    rw [if_pos (by omega), if_pos (by omega), ← hI0]
  have hD01 : (I.take 8192).take 4096 ++ (I.take 8192).drop 4096 = I.take 8192 :=
    List.take_append_drop _ _
  generalize hD0 : (I.take 8192).take 4096 = D0 at hDd0 hD01 ⊢
  generalize hD1 : (I.take 8192).drop 4096 = D1 at hDd1 hD01 ⊢
  have hD0l := hDd0.1
  have hD1l := hDd1.1
  have hw4 : (W64 4096).toNat = 4096 * initSlot false := rfl
  have hw4' : 0 ≤ (W64 4096).toInt := by word
  ihave Hc := (hmc M1 hM1m (W64 4096).toNat ((W64 4096).toNat + D1.length)).2 $$ []
  · iempintro
  have hW2 : ∀ nn m' bs', WReach NoTearCut M1 A (W64 4096).toNat D1 nn m' bs' →
      dbOk (some (i, ⟨m', bs', 0, 0, .idle⟩)) ∧ (nn < D1.length → ∀ t,
        dbOk (some (i, ⟨m', bs', 0, 0, .write t ((W64 4096).toNat + nn) (D1.drop nn)⟩))) := by
    rw [hw4]
    exact initW_obl hM1 hM1vk hDd1
  wp_apply wp_WriteAt f fd p dqf (slice.slice buf w8 (W64 4096) (W64 8192)) D1
      (DFrac.own 1) (W64 4096) dq ⟨i, true, true⟩ N P R γ Good dbOk M1 A 0 0 NoTearCut pwCut_noTear
      rfl hw4' (by rw [hw4]; simp only [initSlot]; omega) (by rw [hw4]; simp only [initSlot]; omega)
      (by omega) (by omega) hN (.inr (Nat.zero_le _)) hW2 $$ [Hinv Hcs Hf Hbuf1 Hfd Hown Hc]
    as %n2 %err2 ⟨Hf, Hbuf1, Hfd, Hc, %nn2, %m2, %bs2, %Hres2, Hown⟩
  · iframe Hf Hbuf1 Hfd Hown Hc; iframe #
  rw [hw4] at Hres2
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
  have hN2 := hR2.narrow hAl (by simp only [initSlot]; omega)
  have hl2 := hN2.len
  obtain ⟨hs2, hb2⟩ := narrow_mid hN2 hAl (by simp only [initSlot]; omega) hd2
  obtain ⟨hM2, -, -⟩ := initMid_wreach hM1 hM1vk hDd1 hR2
  obtain ⟨-, -, hok2, hmaps2, -⟩ := hR2.meta_keep
  (try wp_auto)
  wp_apply wp_Fd f fd p dqf $$ [Hf] as Hf
  · iexact Hf
  (try wp_auto)
  have hok2' : True := by rw [hok2]; exact hM1ok
  -- the bytes after the second write: `D1` over page 1
  have hb2i : ∀ j : Nat, (bs2.map Prod.fst)[j]? =
      ((A.map Prod.fst).take 4096 ++ D1 ++ (A.map Prod.fst).drop (4096 + D1.length))[j]? := by
    intro j; rw [hb2]; simp only [initSlot, Nat.mul_one]
  have hA0 : ∀ k < 64, (A.map Prod.fst)[16 + k]? = some 0 := by
    intro k hk
    rw [hAfst, List.getElem?_append_left (by omega), hFz _ (by omega)]
  have hslot0 : ∀ k < 64, (bs2.map Prod.fst)[16 + k]? = some 0 := by
    intro k hk
    rw [hb2i, List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
      List.getElem?_take, if_pos (by omega), hA0 k hk]
  have hslot1 : ∀ k < 64, (bs2.map Prod.fst)[4096 + 16 + k]? = initBytes[4096 + 16 + k]? := by
    intro k hk
    rw [hb2i, List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp; omega)]
    simp only [List.length_take, List.length_map]
    rw [show 4096 + 16 + k - min 4096 A.length = 16 + k by omega]
    exact hDd1.2 k hk
  have hpage3 : ∀ k < 4096, (bs2[4096 * 3 + k]?).map Prod.fst =
      some ((emptyPageBytes (W64 3) (W16 2))[k]?.getD 0) := by
    intro k hk
    rw [← List.getElem?_map, hb2i, List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append, List.length_take, List.length_map]
    rw [List.getElem?_drop, show 4096 + D1.length + (4096 * 3 + k - (min 4096 A.length + D1.length)) =
      4096 * 3 + k by omega, hAfst, List.getElem?_append_left (by omega), hF3 k hk]
  have hsy2 := initMid_synced (ph := true) hok2' hl2 (by omega) (by omega)
    (fun j hj hv => by
      rcases j with _ | _ | j
      · exact absurd hv (slot_zero_invalid fun k hk => hslot0 k hk)
      · have e : fileMeta (bs2.map Prod.fst) 1 = fileMeta initBytes 1 :=
          fileMeta_of_slot (metaSlot_ext fun k hk => hslot1 k hk)
        rw [e, initBytes_meta1]
      · omega)
    hpage3
    (fun k hk => map_clean_getElem (by
      simp only [initSlot, initOrdByte, Nat.sub_zero, Nat.mul_one]
      rw [hslot1 k hk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      rfl))
  have hS2 : dbOk (some (i, csSynced false m2 [] [] bs2 0 0)) := by
    rw [csSynced_nil m2 bs2 hok2']
    exact initMid_okS _ (wf_idle00 _ _ hsy2.1.len) rfl hsy2.1
  have hF2 : dbOk (some (i, ⟨m2, [] ++ ([] ++ bs2), 0, 0, .idle⟩)) :=
    initMid_okS _ (wf_idle00 _ _ hl2) rfl hM2.notOk
  ihave Hown := (show csOwnF (GF := GF) γ (some (i, ⟨m2, bs2, 0, 0, .idle⟩)) ⊢
      csOwnF (GF := GF) γ (some (i, ⟨m2, [] ++ ([] ++ bs2), 0, 0, .idle⟩)) from .rfl) $$ Hown
  wp_apply wp_Fdatasync fd dq ⟨i, true, true⟩ N P R γ Good dbOk m2 [] [] bs2 0 0 false
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
  rw [csSynced_nil m2 bs2 hok2']
  obtain ⟨hM2', hM2vk⟩ := hsy2
  generalize hM2d : m2.synced 0 bs2 = M2 at hM2' hM2vk ⊢
  generalize hB : bs2.map (fun x => (x.1, true)) = B at hM2' ⊢
  have hM2s : M2.size = max m.size 16384 := by
    rw [← hM2d]; simp only [OsMeta.synced]; omega
  have hM2m : M2.maps = ∅ := by rw [← hM2d]; simp [OsMeta.synced, hmaps2, hM1m]
  have hM2ok : True := by rw [← hM2d]; exact hok2'
  have hBl : B.length = M2.size := by rw [← hB, List.length_map, hl2, ← hM2d]; rfl
  have hBfst : B.map Prod.fst = bs2.map Prod.fst := by rw [← hB, List.map_map]; rfl
  -- the third write: meta 0 (`buf[:4096]`) at 0, phase `true`
  have hcap0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 4096) ∧
      sint.Z (W64 4096) ≤ sint.Z buf.cap := by
    have := Hwf.2; rw [hbl, show sint.Z (W64 16384) = 16384 from rfl] at this
    rw [show sint.Z (W64 4096) = 4096 from rfl, show sint.Z (W64 0) = 0 from rfl]
    exact ⟨by decide, by decide, by omega⟩
  rw [ite_eq_left hcap0]
  (try wp_auto)
  have hw0 : (W64 0).toNat = 4096 * initSlot true := rfl
  ihave Hc := (hmc M2 hM2m (W64 0).toNat ((W64 0).toNat + D0.length)).2 $$ []
  · iempintro
  have hW3 : ∀ nn m' bs', WReach NoTearCut M2 B (W64 0).toNat D0 nn m' bs' →
      dbOk (some (i, ⟨m', bs', 0, 0, .idle⟩)) ∧ (nn < D0.length → ∀ t,
        dbOk (some (i, ⟨m', bs', 0, 0, .write t ((W64 0).toNat + nn) (D0.drop nn)⟩))) := by
    rw [hw0]
    exact initW_obl hM2' hM2vk hDd0
  wp_apply wp_WriteAt f fd p dqf (slice.slice buf w8 (W64 0) (W64 4096)) D0
      (DFrac.own 1) (W64 0) dq ⟨i, true, true⟩ N P R γ Good dbOk M2 B 0 0 NoTearCut pwCut_noTear
      rfl hw0' (by rw [hw00]; omega) (by rw [hw00]; omega) (by omega) (by omega) hN
      (.inr (Nat.zero_le _)) hW3 $$ [Hinv Hcs Hf Hbuf0 Hfd Hown Hc]
    as %n3 %err3 ⟨Hf, Hbuf0, Hfd, Hc, %nn3, %m3, %bs3, %Hres3, Hown⟩
  · iframe Hf Hbuf0 Hfd Hown Hc; iframe #
  rw [hw0] at Hres3
  obtain ⟨hR3, ⟨rfl, rfl, hsz3, hd3⟩ | ⟨rfl, hne3⟩⟩ := Hres3
  rotate_left
  · cases err3 with
    | nil => exact absurd rfl hne3
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    iframe Hf Hfd
    iright
    isplitr
    · ipureintro; exact hne3
    · iexists _, _; iframe
  have hN3 := hR3.narrow hBl (by simp only [initSlot]; omega)
  have hl3 := hN3.len
  obtain ⟨hs3, hb3⟩ := narrow_mid hN3 hBl (by simp only [initSlot]; omega) hd3
  obtain ⟨hM3, -, -⟩ := initMid_wreach hM2' hM2vk hDd0 hR3
  obtain ⟨-, -, hok3, hmaps3, -⟩ := hR3.meta_keep
  (try wp_auto)
  wp_apply wp_Fd f fd p dqf $$ [Hf] as Hf
  · iexact Hf
  (try wp_auto)
  have hok3' : True := by rw [hok3]; exact hM2ok
  have hfin : bs3.map (fun x => (x.1, true)) = initFile xs := by
    have key : bs3.map Prod.fst = I ++ (xs.map Prod.fst).drop 16384 := by
      have hAd : (A.map Prod.fst).drop 8192 = I.drop 8192 ++ (xs.map Prod.fst).drop 16384 := by
        rw [hAfst, ← hFd, List.append_assoc, List.drop_left' hZl]
      have hA4 : ((A.map Prod.fst).take 4096).length = 4096 := by
        rw [List.length_take, List.length_map]; omega
      rw [hb3, hBfst, hb2, hD0l, hD1l]
      simp only [initSlot, Nat.mul_zero, Nat.mul_one, List.take_zero, List.nil_append,
        Nat.zero_add]
      rw [List.append_assoc, List.drop_left' hA4, show 4096 + 4096 = 8192 from rfl, hAd,
        ← List.append_assoc D0, hD01, ← List.append_assoc, List.take_append_drop]
    unfold initFile
    rw [hI0, ← key, List.map_map]; rfl
  -- the bytes after the third write: `init`'s metas, page 3
  have hfst3 : bs3.map Prod.fst = initBytes ++ (xs.map Prod.fst).drop 16384 := by
    have := congrArg (List.map Prod.fst) hfin
    rw [List.map_map] at this
    unfold initFile at this
    rw [List.map_map] at this
    simpa [Function.comp_def] using this
  have hil' : initBytes.length = 16384 := by rw [hI0]; exact hil
  have hS3 : dbOk (some (i, csSynced false m3 [] [] bs3 0 0)) := by
    rw [csSynced_nil m3 bs3 hok3']
    have hsy3 := initMid_synced (ph := true) hok3' hl3 (by omega) (by omega)
      (fun j hj _ => by
        have e : fileMeta (bs3.map Prod.fst) j = fileMeta initBytes j := by
          rw [hfst3, ← fileMeta_take _ 16384 j (by omega), List.take_left' hil']
        rw [e]
        rcases j with _ | _ | j
        · exact initBytes_meta0
        · exact initBytes_meta1
        · omega)
      (fun k hk => by
        rw [← List.getElem?_map, hfst3, List.getElem?_append_left (by omega)]
        exact initBytes_page3 k hk)
      (fun k hk => map_clean_getElem (by
        simp only [initSlot, initOrdByte, Nat.sub_zero, Nat.mul_one]
        rw [hfst3, List.getElem?_append_left (by omega), List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by omega)]
        rfl))
    exact initMid_okS _ (wf_idle00 _ _ hsy3.1.len) rfl hsy3.1
  have hF3' : dbOk (some (i, ⟨m3, [] ++ ([] ++ bs3), 0, 0, .idle⟩)) :=
    initMid_okS _ (wf_idle00 _ _ hl3) rfl hM3.notOk
  ihave Hown := (show csOwnF (GF := GF) γ (some (i, ⟨m3, bs3, 0, 0, .idle⟩)) ⊢
      csOwnF (GF := GF) γ (some (i, ⟨m3, [] ++ ([] ++ bs3), 0, 0, .idle⟩)) from .rfl) $$ Hown
  wp_apply wp_Fdatasync fd dq ⟨i, true, true⟩ N P R γ Good dbOk m3 [] [] bs3 0 0 false
      rfl rfl (by simp) hN hS3 hF3' $$ [Hinv Hcs Hfd Hown] as %e ⟨Hfd, Hs⟩
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
  rw [csSynced_nil m3 bs3 hok3']
  have hm3 : m3.synced 0 bs3 = initDoneMeta m xs := by
    have hmm : m3.maps = m.maps := by
      rw [hmaps3, hM2m, hmaps]
    rw [synced_eq (hok3'.trans hok.symm) hmm hok]
    unfold initDoneMeta
    rw [← hfin, durOf_map_clean, hs3, hM2s]
  rw [hm3, hfin]
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

end osfs_bboltfs
end EtcdGrove
end Perennial
