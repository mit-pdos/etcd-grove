/- Lean-first (no Rocq counterpart). The proof of `db.init()`'s crash-aware spec
(`DB.init.specCrash`): `DB__init.lean`'s, step by step, over the crash invariant. Each `WriteAt` is
`os.File.WriteAt.specCrashS`, whose obligation (every state it reaches, idle and with its next
attempt in flight) comes from what those states know (`wreach_kw`, `CrashKc.lean`): the first
write's states have no slot that may validate (`initW1_obl`: the old slots, invalid, and zeros);
then the meta writes, of meta 1 at 4096 and of meta 0 at 0, over synced states (`midW_okS`); each
`Fdatasync` is `syscall.Fdatasync.specCrashS` with nothing kept or frozen, whose synced states
know every byte (`midS_okS`). -/
module

public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__initCrash
public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__init
public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.CrashKc
public import LinuxFs.Proof.os.CrashStSpec

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs
open github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs renaming initMeta → bInitMeta
open Fs

section pure
variable [GooseExts]


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







/-- The bytes `init` leaves: its four pages over the old ones. -/
theorem init_final (z : w8) (I rest : List w8) (hI : I.length = 16384) :
    (I.take 8192).take 4096 ++
      ((List.replicate 8192 z ++ I.drop 8192 ++ rest).take (4096 * 1) ++ (I.take 8192).drop 4096 ++
        (List.replicate 8192 z ++ I.drop 8192 ++ rest).drop (4096 * 1 + ((I.take 8192).drop 4096).length)).drop
        ((I.take 8192).take 4096).length = I ++ rest := by
  have h1 : ((I.take 8192).take 4096).length = 4096 := by simp; omega
  have h2 : ((I.take 8192).drop 4096).length = 4096 := by simp; omega
  have hz : (List.replicate 8192 z).length = 8192 := List.length_replicate
  rw [h1, h2, List.append_assoc (List.replicate 8192 z),
    List.take_append_of_le_length (by rw [hz]; omega),
    show 4096 * 1 + 4096 = 8192 from rfl, List.drop_left' hz,
    List.append_assoc, List.drop_left' (by rw [List.length_take, hz]; omega),
    ← List.append_assoc, ← List.append_assoc, List.take_append_drop, List.take_append_drop]


/-- **The bytes a successful `WriteAt` leaves**: the data over the old ones. -/
theorem written_fst {m m' : OsMeta} {bs bs' : List ByteG} {off : Nat} {data : List w8} {nn : Nat}
    (hR : WReach m bs off data nn m' bs') (hl : bs.length = m.size) (hoff : off ≤ m.size)
    (hsz : off + data.length ≤ m'.size)
    (hd : ∀ i < data.length, (bs'[off + i]?).map Prod.fst = data[i]?) :
    bs'.map Prod.fst = (bs.map Prod.fst).take off ++ data ++ (bs.map Prod.fst).drop (off + data.length) := by
  obtain ⟨hW, -, -⟩ := hR.wIn hl hoff
  have hl' : bs'.length = m'.size := hW.len
  apply List.ext_getElem?
  intro b
  rw [List.getElem?_map]
  by_cases h1 : b < off
  · rw [hW.out b (.inl h1), List.append_assoc, List.getElem?_append_left (by simp; omega),
      List.getElem?_take, if_pos h1, List.getElem?_map]
  · by_cases h2 : b < off + data.length
    · rw [show b = off + (b - off) by omega, hd _ (by omega), List.append_assoc,
        List.getElem?_append_right (by simp; omega), List.getElem?_append_left (by simp; omega)]
      congr 1; simp; omega
    · rw [hW.out b (.inr (by omega)), List.getElem?_append_right (by simp; omega),
        List.getElem?_drop, List.getElem?_map]
      congr 2; simp; omega

end pure

section obl
variable [GooseExts]

/-- **`init`'s first write's obligation**: every state it reaches, idle or with its next attempt
in flight, has no slot that may validate (the old ones, invalid, or the data's zeros). -/
theorem initW1_obl {i : Ino} {m : OsMeta} {xs : List ByteG} {F : List w8} (h0 : initIdle m xs)
    (hsz : m.size ≤ 2 ^ 30) (hF : F.length = 16384) (hFz : ∀ k < 8192, F.getD k 0 = 0) :
    ∀ nn m' bs', WReach m xs 0 F nn m' bs' →
      dbOk (some (i, ⟨m', bs', 0, 0, .idle⟩)) ∧ (nn < F.length → ∀ t n,
        PwFresh m' bs' (0 + nn) (F.drop nn) n →
        dbOk (some (i, ⟨m', bs', 0, 0, .write t (0 + nn) (F.drop nn) n⟩))) := by
  intro nn m' bs' hR
  have hl := h0.len
  obtain ⟨hW, hS, -⟩ := hR.wIn hl (Nat.zero_le _)
  have hK := wreach_kw 0 0 hR hl (Nat.zero_le _)
  have hD : ∀ j < 2, ¬ metaValid (decode ((List.range 64).map fun k =>
      F.getD (4096 * j + 16 + k - 0) 0) : Meta) := by
    intro j hj
    have : ((List.range 64).map fun k => F.getD (4096 * j + 16 + k - 0) 0) = slotOf F j := by
      simp [slotOf]
    rw [this]; exact slotOf_zero fun k hk => hFz _ (by omega)
  have hslots : ∀ s : CSt, ((∀ b c, (⟨m, xs, 0, 0, .idle⟩ : CSt).kc b = some c → s.kc b = some c) ∨
      KWr (⟨m, xs, 0, 0, .idle⟩ : CSt).kc s.kc 0 F) →
      ∀ j < 2, ∃ X D, SlotK s j X D ∧ ¬ metaValid (decode X : Meta) ∧ ¬ metaValid (decode D : Meta) := by
    intro s hs j hj
    obtain ⟨X, hXl, hXv, hX⟩ := h0.slots j hj
    exact ⟨X, _, kw_slotK hXl (by omega) (by rw [hF]; omega) hX hs, hXv, hD j hj⟩
  have hhi' : m'.hi ≤ 2 ^ 30 := by have := hW.hi; have := h0.hi; simp only [wT] at *; omega
  have hsz' : m'.size ≤ 2 ^ 30 := by have := hW.sz2; simp only [wT] at *; omega
  refine ⟨noValid_okS _ ⟨hW.len, Nat.le_refl _, Nat.zero_le _, trivial⟩ trivial hhi'
    (hslots _ (hK.2.imp (fun h => h.2) id)), fun hlt t n hfr => ?_⟩
  obtain ⟨-, hwr⟩ := kw_flight (t := t) hW.len hS hlt hfr hK
  refine noValid_okS _ ⟨hW.len, Nat.le_refl _, Nat.zero_le _, .inr (Nat.zero_le _)⟩ hS ?_
    (hslots _ (.inr hwr))
  show (cfMeta m' (0 + nn) (F.drop nn).length).hi ≤ 2 ^ 30
  simp only [cfMeta, announce_hi, List.length_drop]; omega

/-- A synced state of `init` (after a sync): its bytes `B`, durable; four pages at least, at most
1 GiB, the size durable. -/
structure midSt (M : OsMeta) (B : List w8) : Prop where
  len : B.length = M.size
  lo : 4 * 4096 ≤ M.lo
  los : M.lo ≤ M.size
  shi : M.size ≤ M.hi
  hi : M.hi ≤ 2 ^ 30

/-- **`init`'s synced states**: each slot invalid or `init`'s meta, slot 0 valid only if slot 1
is, page 3 `init`'s root page. -/
theorem midS_okS {i : Ino} {M : OsMeta} {B : List w8} (h : midSt M B)
    (hP : ∀ j < 2, metaValid (decode (slotOf B j) : Meta) → (decode (slotOf B j) : Meta) = bInitMeta j)
    (h01 : ¬ metaValid (decode (slotOf B 0) : Meta) ∨ metaValid (decode (slotOf B 1) : Meta))
    (hp3 : ∀ k < 4096, B.getD (4096 * 3 + k) 0 = (emptyPageBytes (W64 3) (W16 2)).getD k 0) :
    dbOk (some (i, ⟨M, B.map durB, 0, 0, .idle⟩)) := by
  have hl := h.len
  have hlo := h.lo
  have hlos := h.los
  have hK : ∀ j < 2, SlotK (⟨M, B.map durB, 0, 0, .idle⟩ : CSt) j (slotOf B j) (slotOf B j) :=
    fun j hj => ⟨slotOf_length _ _, slotOf_length _ _, .inl fun k hk => by
      rw [kc_synced hl (by omega), slotOf_getD _ _ _ hk]⟩
  refine initMid_okS _ ⟨by simp [hl], Nat.le_refl _, Nat.zero_le _, trivial⟩ trivial
    (by show 4 * 4096 ≤ M.lo; exact hlo) (by show M.hi ≤ 2 ^ 30; exact h.hi)
    (fun j hj => ⟨_, _, hK j hj, hP j hj, hP j hj⟩) ?_ (fun k hk => by
      rw [kc_synced hl (by omega), hp3 k hk])
  rcases h01 with h0 | h1
  · exact .inl ⟨_, _, hK 0 (by omega), h0, h0⟩
  · exact .inr ⟨_, hK 1 (by omega), h1⟩

/-- **`init`'s meta write of slot `js`** (the page `D` at `4096 js`) over a synced state: every
state it reaches, idle or with its next attempt in flight. The other slot and page 3 are out of
its range. -/
theorem midW_okS {i : Ino} {M : OsMeta} {B : List w8} {D : List w8} {js : Nat} (hjs : js < 2)
    (h : midSt M B) (hD : D.length = 4096)
    (hPB : ∀ j < 2, metaValid (decode (slotOf B j) : Meta) → (decode (slotOf B j) : Meta) = bInitMeta j)
    (hPD : metaValid (decode ((List.range 64).map fun k => D.getD (4096 * js + 16 + k - 4096 * js) 0) : Meta) →
      (decode ((List.range 64).map fun k => D.getD (4096 * js + 16 + k - 4096 * js) 0) : Meta) = bInitMeta js)
    (h01 : (js = 1 ∧ ¬ metaValid (decode (slotOf B 0) : Meta)) ∨
      (js = 0 ∧ metaValid (decode (slotOf B 1) : Meta)))
    (hp3 : ∀ k < 4096, B.getD (4096 * 3 + k) 0 = (emptyPageBytes (W64 3) (W16 2)).getD k 0) :
    ∀ nn m' bs', WReach M (B.map durB) (4096 * js) D nn m' bs' →
      dbOk (some (i, ⟨m', bs', 0, 0, .idle⟩)) ∧ (nn < D.length → ∀ t n,
        PwFresh m' bs' (4096 * js + nn) (D.drop nn) n →
        dbOk (some (i, ⟨m', bs', 0, 0, .write t (4096 * js + nn) (D.drop nn) n⟩))) := by
  intro nn m' bs' hR
  have hl : (B.map durB).length = M.size := by simp [h.len]
  have hlo := h.lo
  have hlos := h.los
  have hhi := h.hi
  have hshi := h.shi
  have hoff : 4096 * js ≤ M.size := by omega
  obtain ⟨hW, hS, -⟩ := hR.wIn hl hoff
  have hK := wreach_kw 0 0 hR hl hoff
  have hK0 : ∀ b, b < M.size → (⟨M, B.map durB, 0, 0, .idle⟩ : CSt).kc b = some [(B.getD b 0, 0)] :=
    fun b hb => kc_synced h.len hb
  -- the facts of a reached state, from what it knows
  have hfacts : ∀ s : CSt, s.Wf → BusyOk s → 4 * 4096 ≤ s.vmeta.lo → s.vmeta.hi ≤ 2 ^ 30 →
      (∀ b, ¬ (4096 * js ≤ b ∧ b < 4096 * js + D.length) → ∀ c,
        (⟨M, B.map durB, 0, 0, .idle⟩ : CSt).kc b = some c → s.kc b = some c) →
      ((∀ b c, (⟨M, B.map durB, 0, 0, .idle⟩ : CSt).kc b = some c → s.kc b = some c) ∨
        KWr (⟨M, B.map durB, 0, 0, .idle⟩ : CSt).kc s.kc (4096 * js) D) →
      dbOk (some (i, s)) := by
    intro s hwf hbz hlo' hhi' hout hin
    have hsj : SlotK s js (slotOf B js) _ :=
      kw_slotK (slotOf_length _ _) (by omega) (by rw [hD]; omega)
        (fun k hk => by rw [hK0 _ (by omega), slotOf_getD _ _ _ hk]) hin
    have hso : ∀ j < 2, j ≠ js → SlotK s j (slotOf B j) (slotOf B j) := fun j hj hne =>
      ⟨slotOf_length _ _, slotOf_length _ _, .inl fun k hk => by
        rw [hout _ (by rw [hD]; omega) _ (hK0 _ (by omega)), slotOf_getD _ _ _ hk]⟩
    refine initMid_okS s hwf hbz hlo' hhi' (fun j hj => ?_) ?_ (fun k hk => by
      rw [hout _ (by rw [hD]; omega) _ (hK0 _ (by omega)), hp3 k hk])
    · by_cases hj' : j = js
      · subst hj'
        exact ⟨_, _, hsj, hPB j hj, hPD⟩
      · exact ⟨_, _, hso j hj hj', hPB j hj, hPB j hj⟩
    · rcases h01 with ⟨rfl, h0⟩ | ⟨rfl, h1⟩
      · exact .inl ⟨_, _, hso 0 (by omega) (by omega), h0, h0⟩
      · exact .inr ⟨_, hso 1 (by omega) (by omega), h1⟩
  have hlo' : 4 * 4096 ≤ m'.lo := by have := hW.lo; simp only [wT] at *; omega
  have hhi' : m'.hi ≤ 2 ^ 30 := by have := hW.hi; have := hW.sz1; simp only [wT] at *; omega
  have hsz1 := hW.sz1
  have hsz2 : m'.size ≤ 2 ^ 30 := by have := hW.sz2; simp only [wT] at *; omega
  refine ⟨hfacts _ ⟨hW.len, Nat.le_refl _, Nat.zero_le _, trivial⟩ trivial hlo' hhi' hK.1
    (hK.2.imp (fun h => h.2) id), fun hlt t n hfr => ?_⟩
  obtain ⟨hout, hwr⟩ := kw_flight (t := t) hW.len hS hlt hfr hK
  refine hfacts _ ⟨hW.len, Nat.le_refl _, Nat.zero_le _, .inr (Nat.zero_le _)⟩ hS ?_ ?_ hout
    (.inr hwr)
  · show 4 * 4096 ≤ (cfMeta m' (4096 * js + nn) (D.drop nn).length).lo
    simp only [cfMeta, announce_lo, List.length_drop]; omega
  · show (cfMeta m' (4096 * js + nn) (D.drop nn).length).hi ≤ 2 ^ 30
    simp only [cfMeta, announce_hi, List.length_drop]; omega

end obl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
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
  intro db f fd p dqf dq N P R γ i m xs hmaps hsz hI hN
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

  have hW1 := initW1_obl (i := i) hI hsz hF hFz'
  wp_apply wp_WriteAt f fd p dqf first F (DFrac.own 1) (W64 0) dq ⟨i, true, true⟩ N P R γ Good
      dbOk m xs 0 0 rfl hw0' (by rw [hw00]; omega) (by rw [hw00, hF]; omega)
      (by rw [hF]; omega) (by rw [hF]; omega) hN (.inr (Nat.zero_le _)) (by rw [hw00]; exact hW1)
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
  obtain ⟨hWr1, -, -⟩ := hR1.wIn hxs (Nat.zero_le _)
  have hl1 : bs1.length = m1.size := hWr1.len
  have hb1 := written_fst hR1 hxs (Nat.zero_le _) hsz1 hd1
  simp only [List.take_zero, List.nil_append, Nat.zero_add, hF] at hb1 hsz1
  have hm1s : m1.size = max m.size 16384 := by
    have := hWr1.sz2; have := hWr1.sz1; simp only [wT, hF, Nat.zero_add] at *; omega
  have hm1m : m1.maps = m.maps := hWr1.maps
  generalize hB1 : F ++ (xs.map Prod.fst).drop 16384 = B1 at hb1
  have hB1l : B1.length = m1.size := by rw [← hb1, List.length_map, hl1]
  have hB1z : ∀ k < 8192, B1.getD k 0 = 0 := by
    intro k hk; rw [← hB1, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
      ← List.getD_eq_getElem?_getD]; exact hFz' k hk
  have hB13 : ∀ k < 4096, B1.getD (4096 * 3 + k) 0 = (emptyPageBytes (W64 3) (W16 2)).getD k 0 := by
    intro k hk; rw [← hB1, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), hF3 k hk,
      Option.getD_some, List.getD_eq_getElem?_getD]
  (try wp_auto)
  wp_apply wp_Fd f fd p dqf $$ [Hf] as Hf
  · iexact Hf
  (try wp_auto)
  have hsyn : ∀ (mm : OsMeta) (bs : List ByteG),
      csSynced mm [] [] bs 0 0 = ⟨mm.synced, (bs.map Prod.fst).map durB, 0, 0, .idle⟩ := by
    intro mm bs; simp [csSynced, List.map_map]
  have hmid1 : midSt m1.synced B1 :=
    ⟨by rw [hB1l]; rfl, by show 4 * 4096 ≤ m1.size; omega, Nat.le_refl _, Nat.le_refl _,
      by show m1.size ≤ 2 ^ 30; omega⟩
  have hzero : ∀ (B : List w8), (∀ k < 8192, B.getD k 0 = 0) → ∀ j < 2,
      ¬ metaValid (decode (slotOf B j) : Meta) := fun B hB j hj =>
    slotOf_zero fun k hk => hB _ (by omega)
  have hS1 : dbOk (some (i, csSynced m1 [] [] bs1 0 0)) := by
    rw [hsyn, hb1]
    exact midS_okS hmid1 (fun j hj hv => absurd hv (hzero B1 hB1z j hj)) (.inl (hzero B1 hB1z 0 (by omega)))
      hB13
  ihave Hown := (show csOwnF (GF := GF) γ (some (i, ⟨m1, bs1, 0, 0, .idle⟩)) ⊢
      csOwnF (GF := GF) γ (some (i, ⟨m1, [] ++ ([] ++ bs1), 0, 0, .idle⟩)) from .rfl) $$ Hown
  wp_apply wp_Fdatasync fd dq ⟨i, true, true⟩ N P R γ Good dbOk m1 [] [] bs1 0 0
      rfl rfl (by simp) hN hS1 $$ [Hinv Hcs Hfd Hown] as %e ⟨Hfd, Hs⟩
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
  rw [hsyn, hb1]
  generalize hM1 : m1.synced = M1 at hmid1 ⊢
  have hM1s : M1.size = max m.size 16384 := by rw [← hM1]; exact hm1s
  have hM1m : M1.maps = ∅ := by rw [← hM1]; show m1.maps = ∅; rw [hm1m, hmaps]
  -- the second write: meta 1 (`buf[4096:8192]`) at 4096
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
  have hD0l : ((I.take 8192).take 4096).length = 4096 := by
    simp only [List.length_take]; omega
  have hD1l : ((I.take 8192).drop 4096).length = 4096 := by
    simp only [List.length_drop, List.length_take]; omega
  have hD01 : (I.take 8192).take 4096 ++ (I.take 8192).drop 4096 = I.take 8192 :=
    List.take_append_drop _ _
  -- the metas' slots, `init`'s
  have hDs1 : ∀ k < 64, ((I.take 8192).drop 4096).getD (16 + k) 0 = initBytes.getD (4096 + 16 + k) 0 := by
    intro k hk
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_take,
      if_pos (by omega), ← hI0]
    congr 2; omega
  have hDs0 : ∀ k < 64, ((I.take 8192).take 4096).getD (16 + k) 0 = initBytes.getD (16 + k) 0 := by
    intro k hk
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_take,
      if_pos (by omega), if_pos (by omega), ← hI0]
  generalize hD0 : (I.take 8192).take 4096 = D0 at hD0l hD01 hDs0 ⊢
  generalize hD1 : (I.take 8192).drop 4096 = D1 at hD1l hD01 hDs1 ⊢
  have hinit : ∀ j < 2, (decode (slotOf initBytes j) : Meta) = bInitMeta j := by
    intro j hj
    rw [slotOf_fileMeta _ _ (by omega)]
    rcases j with _ | _ | j
    · exact initBytes_meta0
    · exact initBytes_meta1
    · omega
  have hslotD : ∀ (D : List w8) (j : Nat), (∀ k < 64, D.getD (16 + k) 0 = initBytes.getD (4096 * j + 16 + k) 0) →
      ((List.range 64).map fun k => D.getD (4096 * j + 16 + k - 4096 * j) 0) = slotOf initBytes j := by
    intro D j hDj
    apply List.ext_getElem (by simp [slotOf_length]); intro k h1 h2
    simp only [List.getElem_map, List.getElem_range, slotOf]
    rw [show 4096 * j + 16 + k - 4096 * j = 16 + k by omega]
    exact hDj k (by simpa using h1)
  have hw4 : (W64 4096).toNat = 4096 * 1 := rfl
  have hw4' : 0 ≤ (W64 4096).toInt := by word
  ihave Hc := (hmc M1 hM1m (W64 4096).toNat ((W64 4096).toNat + D1.length)).2 $$ []
  · iempintro
  have hW2 := midW_okS (i := i) (js := 1) (by omega) hmid1 hD1l
    (fun j hj hv => absurd hv (hzero B1 hB1z j hj))
    (fun _ => by rw [hslotD D1 1 (fun k hk => by rw [hDs1 k hk])]; exact hinit 1 (by omega))
    (.inl ⟨rfl, hzero B1 hB1z 0 (by omega)⟩) hB13
  wp_apply wp_WriteAt f fd p dqf (slice.slice buf w8 (W64 4096) (W64 8192)) D1
      (DFrac.own 1) (W64 4096) dq ⟨i, true, true⟩ N P R γ Good dbOk M1 (B1.map durB) 0 0
      rfl hw4' (by rw [hw4, ← hmid1.len]; simp; omega) (by rw [hw4]; omega)
      (by omega) (by omega) hN (.inr (Nat.zero_le _)) (by rw [hw4]; exact hW2)
      $$ [Hinv Hcs Hf Hbuf1 Hfd Hown Hc]
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
  have hA1l : (B1.map durB).length = M1.size := by rw [List.length_map]; exact hmid1.len
  obtain ⟨hWr2, -, -⟩ := hR2.wIn hA1l (by omega)
  have hl2 : bs2.length = m2.size := hWr2.len
  have hb2 := written_fst hR2 hA1l (by omega) hsz2 hd2
  have hfd1 : (B1.map durB).map Prod.fst = B1 := by rw [List.map_map]; exact List.map_id _
  rw [hfd1] at hb2
  have hm2s : m2.size = M1.size := by
    have := hWr2.sz1; have := hWr2.sz2; simp only [wT] at *; omega
  have hm2m : m2.maps = ∅ := by rw [hWr2.maps]; exact hM1m
  generalize hB2 : B1.take (4096 * 1) ++ D1 ++ B1.drop (4096 * 1 + D1.length) = B2 at hb2
  have hB2l : B2.length = m2.size := by rw [← hb2, List.length_map, hl2]
  have hB2g : ∀ b, B2.getD b 0 = if 4096 ≤ b ∧ b < 8192 then D1.getD (b - 4096) 0 else B1.getD b 0 := by
    intro b
    rw [← hB2]
    simp only [List.getD_eq_getElem?_getD, List.append_assoc]
    by_cases h1 : b < 4096
    · rw [if_neg (by omega), List.getElem?_append_left (by simp; omega), List.getElem?_take, if_pos (by omega)]
    · by_cases h2 : b < 8192
      · rw [if_pos ⟨by omega, h2⟩, List.getElem?_append_right (by simp; omega),
          List.getElem?_append_left (by simp; omega)]
        congr 2; simp; omega
      · rw [if_neg (by omega), List.getElem?_append_right (by simp; omega),
          List.getElem?_append_right (by simp; omega), List.getElem?_drop]
        congr 2; simp; omega
  have hB2s0 : ∀ k < 8192, k < 4096 → B2.getD k 0 = 0 := fun k hk h => by
    rw [hB2g, if_neg (by omega)]; exact hB1z k hk
  have hB2s1 : slotOf B2 1 = slotOf initBytes 1 := by
    apply List.ext_getElem (by simp [slotOf_length]); intro k h1 h2
    have hk : k < 64 := by rw [slotOf_length] at h1; exact h1
    simp only [slotOf, List.getElem_map, List.getElem_range]
    rw [hB2g, if_pos ⟨by omega, by omega⟩, show 4096 * 1 + 16 + k - 4096 = 16 + k by omega]
    exact hDs1 k hk
  have hB23 : ∀ k < 4096, B2.getD (4096 * 3 + k) 0 = (emptyPageBytes (W64 3) (W16 2)).getD k 0 := by
    intro k hk; rw [hB2g, if_neg (by omega)]; exact hB13 k hk
  have hB2z0 : ¬ metaValid (decode (slotOf B2 0) : Meta) :=
    slotOf_zero fun k hk => hB2s0 _ (by omega) (by omega)
  have hP2 : ∀ j < 2, metaValid (decode (slotOf B2 j) : Meta) → (decode (slotOf B2 j) : Meta) = bInitMeta j := by
    intro j hj hv
    rcases j with _ | _ | j
    · exact absurd hv hB2z0
    · rw [hB2s1]; exact hinit 1 (by omega)
    · omega
  (try wp_auto)
  wp_apply wp_Fd f fd p dqf $$ [Hf] as Hf
  · iexact Hf
  (try wp_auto)
  have hmid2 : midSt m2.synced B2 :=
    ⟨by rw [hB2l]; rfl, by show 4 * 4096 ≤ m2.size; rw [hm2s, hM1s]; omega, Nat.le_refl _,
      Nat.le_refl _, by show m2.size ≤ 2 ^ 30; rw [hm2s, hM1s]; omega⟩
  have hS2 : dbOk (some (i, csSynced m2 [] [] bs2 0 0)) := by
    rw [hsyn, hb2]
    exact midS_okS hmid2 hP2 (.inl hB2z0) hB23
  ihave Hown := (show csOwnF (GF := GF) γ (some (i, ⟨m2, bs2, 0, 0, .idle⟩)) ⊢
      csOwnF (GF := GF) γ (some (i, ⟨m2, [] ++ ([] ++ bs2), 0, 0, .idle⟩)) from .rfl) $$ Hown
  wp_apply wp_Fdatasync fd dq ⟨i, true, true⟩ N P R γ Good dbOk m2 [] [] bs2 0 0
      rfl rfl (by simp) hN hS2 $$ [Hinv Hcs Hfd Hown] as %e ⟨Hfd, Hs⟩
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
  rw [hsyn, hb2]
  generalize hM2 : m2.synced = M2 at hmid2 ⊢
  have hM2s : M2.size = max m.size 16384 := by rw [← hM2]; show m2.size = _; rw [hm2s, hM1s]
  have hM2m : M2.maps = ∅ := by rw [← hM2]; exact hm2m
  -- the third write: meta 0 (`buf[:4096]`) at 0
  have hcap0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 4096) ∧
      sint.Z (W64 4096) ≤ sint.Z buf.cap := by
    have := Hwf.2; rw [hbl, show sint.Z (W64 16384) = 16384 from rfl] at this
    rw [show sint.Z (W64 4096) = 4096 from rfl, show sint.Z (W64 0) = 0 from rfl]
    exact ⟨by decide, by decide, by omega⟩
  rw [ite_eq_left hcap0]
  (try wp_auto)
  have hw0z : (W64 0).toNat = 4096 * 0 := rfl
  have hw0z' : 0 ≤ (W64 0).toInt := by word
  ihave Hc := (hmc M2 hM2m (W64 0).toNat ((W64 0).toNat + D0.length)).2 $$ []
  · iempintro
  have hW3 := midW_okS (i := i) (js := 0) (by omega) hmid2 hD0l hP2
    (fun _ => by rw [hslotD D0 0 (fun k hk => by rw [hDs0 k hk])]; exact hinit 0 (by omega))
    (.inr ⟨rfl, by rw [hB2s1, hinit 1 (by omega)]; exact initMeta_valid 1⟩) hB23
  wp_apply wp_WriteAt f fd p dqf (slice.slice buf w8 (W64 0) (W64 4096)) D0
      (DFrac.own 1) (W64 0) dq ⟨i, true, true⟩ N P R γ Good dbOk M2 (B2.map durB) 0 0
      rfl hw0z' (by rw [hw0z]; omega) (by rw [hw0z]; omega)
      (by omega) (by omega) hN (.inr (Nat.zero_le _)) (by rw [hw0z]; exact hW3)
      $$ [Hinv Hcs Hf Hbuf0 Hfd Hown Hc]
    as %n3 %err3 ⟨Hf, Hbuf0, Hfd, Hc, %nn3, %m3, %bs3, %Hres3, Hown⟩
  · iframe Hf Hbuf0 Hfd Hown Hc; iframe #
  rw [hw0z] at Hres3
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
  have hA2l : (B2.map durB).length = M2.size := by rw [List.length_map]; exact hmid2.len
  obtain ⟨hWr3, -, -⟩ := hR3.wIn hA2l (Nat.zero_le _)
  have hl3 : bs3.length = m3.size := hWr3.len
  have hb3 := written_fst hR3 hA2l (Nat.zero_le _) hsz3 hd3
  have hfd2 : (B2.map durB).map Prod.fst = B2 := by rw [List.map_map]; exact List.map_id _
  rw [hfd2] at hb3
  simp only [Nat.mul_zero, List.take_zero, List.nil_append, Nat.zero_add] at hb3
  have hm3s : m3.size = M2.size := by
    have := hWr3.sz1; have := hWr3.sz2; simp only [wT] at *; omega
  have hm3m : m3.maps = ∅ := by rw [hWr3.maps]; exact hM2m
  -- the file's bytes: `init`'s pages, then the old ones
  have hfst3 : bs3.map Prod.fst = initBytes ++ (xs.map Prod.fst).drop 16384 := by
    have e := init_final (zero_val w8) I ((xs.map Prod.fst).drop 16384) (by rw [← hI0]; exact hil0)
    rw [hD0, hD1, hZ, hFd, hB1, hD0l] at e
    rw [hb3, hI0, ← e, hB2, hD0l]
  (try wp_auto)
  wp_apply wp_Fd f fd p dqf $$ [Hf] as Hf
  · iexact Hf
  (try wp_auto)
  have hB3 : (bs3.map Prod.fst) = initBytes ++ (xs.map Prod.fst).drop 16384 := hfst3
  have hmid3 : midSt m3.synced (bs3.map Prod.fst) :=
    ⟨by rw [List.length_map, hl3]; rfl, by show 4 * 4096 ≤ m3.size; rw [hm3s, hM2s]; omega,
      Nat.le_refl _, Nat.le_refl _, by show m3.size ≤ 2 ^ 30; rw [hm3s, hM2s]; omega⟩
  have hS3 : dbOk (some (i, csSynced m3 [] [] bs3 0 0)) := by
    rw [hsyn]
    rw [hB3]
    have hil' : 16384 ≤ initBytes.length := by omega
    refine midS_okS (by rw [← hB3]; exact hmid3) (fun j hj _ => ?_) (.inr ?_) (fun k hk => ?_)
    · rw [slotOf_append_left _ _ _ (by omega)]; exact hinit j hj
    · rw [slotOf_append_left _ _ _ (by omega), hinit 1 (by omega)]; exact initMeta_valid 1
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), initBytes_page3 k hk,
        Option.getD_some, List.getD_eq_getElem?_getD]
  ihave Hown := (show csOwnF (GF := GF) γ (some (i, ⟨m3, bs3, 0, 0, .idle⟩)) ⊢
      csOwnF (GF := GF) γ (some (i, ⟨m3, [] ++ ([] ++ bs3), 0, 0, .idle⟩)) from .rfl) $$ Hown
  wp_apply wp_Fdatasync fd dq ⟨i, true, true⟩ N P R γ Good dbOk m3 [] [] bs3 0 0
      rfl rfl (by simp) hN hS3 $$ [Hinv Hcs Hfd Hown] as %e ⟨Hfd, Hs⟩
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
  rw [hsyn, hfst3]
  have hm3 : m3.synced = initDoneMeta m :=
    synced_eq _ _ (by rw [hm3s, hM2s]) (by rw [hm3m, hmaps]) (by rw [hR3.cut, ← hM2]; show m2.cut = _; rw [hR2.cut, ← hM1]; show m1.cut = _; rw [hR1.cut])
      (by rw [hR3.cz, ← hM2]; show m2.cz = _; rw [hR2.cz, ← hM1]; show m1.cz = _; rw [hR1.cz])
  have hfin : (initBytes ++ (xs.map Prod.fst).drop 16384).map durB = initFile xs := rfl
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
