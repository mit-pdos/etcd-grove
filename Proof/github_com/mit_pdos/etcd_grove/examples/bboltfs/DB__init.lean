/- Lean-first (no Rocq counterpart). The proof of `db.init()`: `initPages` into a fresh buffer, then each half of it written with `WriteAt` (the second half first, which may extend the file: a zero gap before it if the file is shorter than two pages) and the whole file synced with `Fdatasync`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__init
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.initPages
public import Spec.os.File__WriteAt
public import Spec.os.File__Fd
public import Spec.syscall.Fdatasync

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

theorem pwSize_full (sz off n : Nat) (h : 0 < n) : pwSize sz off n = max sz (off + n) := by
  unfold pwSize; rw [if_neg (by omega)]

/-- A whole `pwrite` of `data` at `off`: the range's bytes are the zero gap, then `data`. -/
theorem pwBytes_full (sz off : Nat) (data : List w8) (xs : List (w8 × Bool)) (h : 0 < data.length) :
    (pwBytes sz off data data.length xs).map Prod.fst =
      List.replicate (off - min off sz) 0 ++ data := by
  have hs := pwSize_full sz off data.length h
  have hl : (pwBytes sz off data data.length xs).length = off - min off sz + data.length := by
    rw [pwBytes_length, hs]; omega
  apply List.ext_getElem
  · simp only [List.length_map, hl, List.length_append, List.length_replicate]
  · intro i h1 h2
    simp only [List.getElem_map]
    rw [pwBytes_getElem _ _ _ _ _ _ (by simpa using h1)]
    simp only [List.length_map, hl] at h1
    simp only [List.length_append, List.length_replicate] at h2
    unfold pwByte
    by_cases hi : min off sz + i < off
    · rw [if_pos hi, List.getElem_append_left (by simp; omega)]; simp
    · rw [if_neg hi, if_pos (by omega), List.getElem_append_right (by simp; omega)]
      simp only [List.length_replicate, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (by omega)]
      simp only [Option.getD_some]; congr 1; omega

section osbytes
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

theorem osBytes_append (p : GoString) (off : Nat) (dq : DFrac) (xs ys : List (w8 × Bool)) :
    osBytes (L := L) p off dq (xs ++ ys) ⊣⊢
      osBytes (L := L) p off dq xs ∗ osBytes (L := L) p (off + xs.length) dq ys := by
  unfold osBytes; exact bytesG_append _ _ _ _ _ _

/-- After the first write: the bytes before its range, its range, and those after it, as one. -/
theorem init_join1 (p : GoString) (xs ys : List (w8 × Bool)) (sz : Nat) (hxs : xs.length = sz)
    (hys : ys.length = 16384 - min 8192 sz) :
    osBytes (L := L) p 0 (DFrac.own 1) (xs.take (min 8192 sz)) ∗
      osBytes (L := L) p (min 8192 sz) (DFrac.own 1) ys ∗
      osBytes (L := L) p (min 8192 sz + (min 16384 sz - min 8192 sz)) (DFrac.own 1)
        ((xs.drop (min 8192 sz)).drop (min 16384 sz - min 8192 sz)) ⊢
    osBytes (L := L) p 0 (DFrac.own 1) (xs.take (min 8192 sz) ++ ys ++ xs.drop 16384) := by
  iintro ⟨H0, H1, H2⟩
  ihave H2 : osBytes (L := L) p 16384 (DFrac.own 1) (xs.drop 16384) $$ [H2]
  · by_cases h : 16384 ≤ sz
    · rw [show min 8192 sz + (min 16384 sz - min 8192 sz) = 16384 by omega, List.drop_drop,
        show min 8192 sz + (min 16384 sz - min 8192 sz) = 16384 by omega]
      iexact H2
    · rw [List.drop_eq_nil_of_le (show xs.length ≤ 16384 by omega)]
      unfold osBytes; iapply (bytesG_nil _ _ _ _).2; iempintro
  iapply (osBytes_append p 0 _ _ _).2
  isplitl [H0 H1]
  · iapply (osBytes_append p 0 _ _ _).2
    rw [List.length_take, show min (min 8192 sz) xs.length = min 8192 sz by omega, Nat.zero_add]
    iframe
  · rw [List.length_append, List.length_take, hys,
      show 0 + (min (min 8192 sz) xs.length + (16384 - min 8192 sz)) = 16384 by omega]
    iexact H2

end osbytes

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

theorem DB.init.wp_proof (wp_initPages : initPages.spec (GF := GF) (hG := hG))
    (wp_WriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Fdatasync : syscall.Fdatasync.spec (GF := GF) (hG := hG)) :
    DB.init.spec (GF := GF) (hG := hG) := by
  intro db f fd p dqf dq m xs hok hmaps hxs hsz
  have hil := initBytes_length
  simp only [pageBytes] at hil
  have hw8 : (W64 8192).toNat = 8192 := by word
  have hw0 : 0 ≤ (W64 8192).toInt := by word
  have hd0 : 0 < (initBytes.drop 8192).length := by rw [List.length_drop]; omega
  have hd1 : (initBytes.drop 8192).length ≤ 0x40000000 := by rw [List.length_drop]; omega
  have hd2 : ((xs.drop (min 8192 m.size)).take (min 16384 m.size - min 8192 m.size)).length =
      min ((W64 8192).toNat + (initBytes.drop 8192).length) m.size - min (W64 8192).toNat m.size := by
    rw [List.length_take, List.length_drop, List.length_drop, show (W64 8192).toNat = 8192 from rfl]
    omega
  wp_start as ⟨#Hinv, #Hfile, Hfsz, Hf, Hfd, Hm, Hb⟩
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
  rw [ite_eq_left (by rw [hbl]; exact ⟨by decide, by decide, by rw [← hbl]; exact Hwf.2⟩)]
  (try wp_auto)
  icases (ownSlice_split_all (W64 8192) buf _ _ ⟨by decide, by rw [hbl]; decide⟩).1 $$ Hbuf
    with ⟨Hbuf1, Hbuf2⟩
  have h8 : sint.nat (W64 8192) = 8192 := rfl
  rw [h8]
  -- the file's bytes around the window `[a, b)` the first write takes
  have hab : min 8192 m.size + (min 16384 m.size - min 8192 m.size) ≤ xs.length := by omega
  icases (osBytes_window p _ xs (min 8192 m.size) (min 16384 m.size - min 8192 m.size) hab).1 $$ Hb
    with ⟨Hb0, Hw, Hb2⟩
  have hmc : ∀ lo hi, mcellsAny (GF := GF) m.maps lo hi ⊣⊢ emp := by
    intro lo hi; unfold mcellsAny; rw [hmaps]; exact BigSepM.bigSepM_empty
  ihave Hc := (hmc (min (W64 8192).toNat m.size) ((W64 8192).toNat + (initBytes.drop 8192).length)).2 $$ []
  · iempintro
  generalize hI : initBytes = I at hil hd0 hd1 hd2 ⊢
  wp_apply wp_WriteAt f fd p dqf (slice.slice buf w8 (W64 8192) buf.len) (I.drop 8192)
      (DFrac.own 1) (W64 8192) dq ⟨p, true, true⟩ 1 m ((xs.drop (min 8192 m.size)).take
        (min 16384 m.size - min 8192 m.size)) rfl hw0 hd0 hd1
      hd2 (fun _ => rfl) $$ [Hinv Hf Hbuf2 Hfd Hm Hw Hc]
    as %n %err ⟨Hf, Hbuf2, Hfd, %j, %ys, %h, %Hres, Hm, Hw, Hc⟩
  · rw [hw8]; iframe Hf Hm Hw Hc Hbuf2 Hfd; iframe #
  rw [hw8] at Hres
  try rw [hw8]
  obtain ⟨hj, hys, hh, ⟨rfl, rfl, rfl⟩ | ⟨rfl, hne⟩⟩ := Hres
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
  have hdl : (I.drop 8192).length = 8192 := by rw [List.length_drop]; omega
  have hys' := hys.trans (pwBytes_full _ _ _ _ hd0)
  simp only [hdl] at hys ⊢
  have hysl : ys.length = 16384 - min 8192 m.size := by
    have := congrArg List.length hys'
    simp only [List.length_map, List.length_append, List.length_replicate] at this; omega
  ihave Hb := init_join1 p xs ys m.size hxs hysl $$ [Hb0 Hw Hb2]
  · iframe
  (try wp_auto)
  wp_apply wp_Fd f fd p dqf $$ [Hf] as Hf
  · iexact Hf
  (try wp_auto)
  wp_apply wp_Fdatasync fd dq ⟨p, true, true⟩ { m with size := pwSize m.size 8192 8192, hi := h } 0
      _ $$ [Hinv Hfd Hm Hb] as %e ⟨Hfd, Hs⟩
  · iframe; iframe #
  icases Hs with (⟨%He, Hm, Hb⟩ | ⟨%He, Hm, -⟩)
  rotate_left
  · unfold errnoErr; rw [if_neg He.1]
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
  -- the file after the first write and sync: `A`, of size `S`
  have hS : pwSize m.size 8192 8192 = max m.size 16384 := by rw [pwSize_full _ _ _ (by decide)]
  have hm1 : ({ m with size := pwSize m.size 8192 8192, hi := h } : OsMeta).synced =
      { m with size := max m.size 16384, lo := max m.size 16384, hi := max m.size 16384 } := by
    simp only [OsMeta.synced, hS]
  rw [hm1]
  generalize hm1' :
    ({ m with size := max m.size 16384, lo := max m.size 16384, hi := max m.size 16384 } : OsMeta) = m1
  have hm1s : m1.size = max m.size 16384 := by rw [← hm1']
  have hm1m : m1.maps = ∅ := by rw [← hm1']; exact hmaps
  have hm1ok : m1.ok = true := by rw [← hm1']; exact hok
  simp only [syncedBytes, hok, if_true]
  generalize hA : List.map (fun x => (x.1, true))
    (List.take (min 8192 m.size) xs ++ ys ++ List.drop 16384 xs) = A
  have hAl : A.length = max m.size 16384 := by
    rw [← hA, List.length_map, List.length_append, List.length_append, List.length_take,
      List.length_drop, hysl]; omega
  have hAfst : A.map Prod.fst =
      (xs.take (min 8192 m.size)).map Prod.fst ++ (List.replicate (8192 - min 8192 m.size) 0 ++
        I.drop 8192) ++ (xs.drop 16384).map Prod.fst := by
    rw [← hA, List.map_map, ← hys', List.map_append, List.map_append]; rfl
  have hcap : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 8192) ∧
      sint.Z (W64 8192) ≤ sint.Z buf.cap := by
    have := Hwf.2; rw [hbl, show sint.Z (W64 16384) = 16384 from rfl] at this
    rw [show sint.Z (W64 8192) = 8192 from rfl, show sint.Z (W64 0) = 0 from rfl]
    exact ⟨by decide, by decide, by omega⟩
  rw [ite_eq_left hcap]
  (try wp_auto)
  icases (osBytes_append p 0 (DFrac.own 1) (A.take 8192) (A.drop 8192)).1 $$
    [Hb] with ⟨Hb0, Hb1⟩
  · rw [List.take_append_drop]; iexact Hb
  rw [List.length_take, show 0 + min 8192 A.length = 8192 by omega]
  have hw00 : (W64 0).toNat = 0 := rfl
  have hw0' : 0 ≤ (W64 0).toInt := by word
  have he0 : 0 < (I.take 8192).length := by rw [List.length_take]; omega
  have he1 : (I.take 8192).length ≤ 0x40000000 := by rw [List.length_take]; omega
  have he2 : (A.take 8192).length =
      min ((W64 0).toNat + (I.take 8192).length) m1.size - min (W64 0).toNat m1.size := by
    rw [List.length_take, List.length_take, hw00, hm1s]; omega
  have hmc1 : ∀ lo hi, mcellsAny (GF := GF) m1.maps lo hi ⊣⊢ emp := by
    intro lo hi; unfold mcellsAny; rw [hm1m]; exact BigSepM.bigSepM_empty
  ihave Hc := (hmc1 (min (W64 0).toNat m1.size) ((W64 0).toNat + (I.take 8192).length)).2 $$ []
  · iempintro
  wp_apply wp_WriteAt f fd p dqf (slice.slice buf w8 (W64 0) (W64 8192)) (I.take 8192)
      (DFrac.own 1) (W64 0) dq ⟨p, true, true⟩ 1 m1 (A.take 8192) rfl hw0' he0 he1
      he2 (fun _ => rfl) $$ [Hinv Hf Hbuf1 Hfd Hm Hb0 Hc]
    as %n2 %err2 ⟨Hf, Hbuf1, Hfd, %j2, %ys2, %h2, %Hres2, Hm, Hw, Hc⟩
  · rw [hw00, Nat.zero_min]; iframe Hf Hm Hb0 Hc Hbuf1 Hfd; iframe #
  rw [hw00, Nat.zero_min] at *
  obtain ⟨hj2, hys2, hh2, ⟨rfl, rfl, rfl⟩ | ⟨rfl, hne2⟩⟩ := Hres2
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
  have htl : (I.take 8192).length = 8192 := by rw [List.length_take]; omega
  have hys2' := hys2.trans (pwBytes_full _ _ _ _ he0)
  simp only [htl, Nat.zero_min, Nat.sub_self, List.replicate_zero, List.nil_append] at hys2' ⊢
  have hys2l : ys2.length = 8192 := by
    have := congrArg List.length hys2'; simp only [List.length_map, htl] at this; exact this
  ihave Hb := (osBytes_append p 0 (DFrac.own 1) ys2 (A.drop 8192)).2 $$ [Hw Hb1]
  · rw [hys2l]; iframe
  (try wp_auto)
  wp_apply wp_Fd f fd p dqf $$ [Hf] as Hf
  · iexact Hf
  (try wp_auto)
  wp_apply wp_Fdatasync fd dq ⟨p, true, true⟩ { m1 with size := pwSize m1.size 0 8192, hi := h2 } 0
      _ $$ [Hinv Hfd Hm Hb] as %e ⟨Hfd, Hs⟩
  · iframe; iframe #
  icases Hs with (⟨%He, Hm, Hb⟩ | ⟨%He, Hm, -⟩)
  rotate_left
  · unfold errnoErr; rw [if_neg He.1]
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
  have hm2 : ({ m1 with size := pwSize m1.size 0 8192, hi := h2 } : OsMeta).synced = m1 := by
    rw [← hm1']
    simp only [OsMeta.synced, pwSize_full _ _ _ (by decide : 0 < 8192)]
    rw [show max (max m.size 16384) (0 + 8192) = max m.size 16384 by omega]
  have hfin : (ys2 ++ A.drop 8192).map (fun x => (x.1, true)) = initFile xs := by
    have key : (ys2 ++ A.drop 8192).map Prod.fst = I ++ (xs.map Prod.fst).drop 16384 := by
      rw [List.map_append, hys2', List.map_drop, hAfst]
      have hlen1 : ((xs.take (min 8192 m.size)).map Prod.fst ++
          List.replicate (8192 - min 8192 m.size) (0 : w8)).length = 8192 := by
        simp only [List.length_append, List.length_map, List.length_take, List.length_replicate]
        omega
      rw [show ∀ (X R D T : List w8), X ++ (R ++ D) ++ T = (X ++ R) ++ (D ++ T) by
        intro X R D T; simp only [List.append_assoc]]
      rw [List.drop_left' hlen1, ← List.append_assoc, List.take_append_drop, List.map_drop]
    unfold initFile
    rw [hI, ← key, List.map_map]; rfl
  have hsz64 : sint.Z (W64 (m.size : Int)) = m.size := by
    have : (m.size : Int) < 2 ^ 63 := by omega
    word
  rw [hm2]
  simp only [syncedBytes, hm1ok, if_true]
  rw [hfin]
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
