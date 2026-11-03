/- Lean-first (no Rocq counterpart). The proof of `db.init()`: `initPages` into a fresh buffer `buf`; a second buffer `first`, zero, with `buf`'s last two pages copied in; `first` written at 0 with `WriteAt` (all four pages, the metas zero; it may extend the file), `Fdatasync`, then `buf`'s page 1 (meta 1) at 4096, `Fdatasync`, then `buf`'s page 0 (meta 0) at 0, `Fdatasync`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__init
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.initPages
public import Spec.os.File__WriteAt
public import Spec.os.File__Fd
public import Spec.syscall.Fdatasync
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.Writer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section osbytes
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

theorem osBytes_append (p : GoString) (off : Nat) (dq : DFrac) (xs ys : List (w8 × Bool)) :
    osBytes (L := L) p off dq (xs ++ ys) ⊣⊢
      osBytes (L := L) p off dq xs ∗ osBytes (L := L) p (off + xs.length) dq ys := by
  unfold osBytes; exact bytesG_append _ _ _ _ _ _

/-- After the first write: its four pages, then the bytes after them, as one. -/
theorem init_join1 (p : GoString) (xs ys : List (w8 × Bool)) (n : Nat) (hys : ys.length = n) :
    osBytes (L := L) p 0 (DFrac.own 1) ys ∗
      osBytes (L := L) p (0 + (xs.take n).length) (DFrac.own 1) (xs.drop n) ⊢
    osBytes (L := L) p 0 (DFrac.own 1) (ys ++ xs.drop n) := by
  iintro ⟨H1, H2⟩
  ihave H2 : osBytes (L := L) p n (DFrac.own 1) (xs.drop n) $$ [H2]
  · by_cases h : n ≤ xs.length
    · rw [List.length_take, show 0 + min n xs.length = n by omega]; iexact H2
    · rw [List.drop_eq_nil_of_le (show xs.length ≤ n by omega)]
      unfold osBytes; iapply (bytesG_nil _ _ _ _).2; iempintro
  iapply (osBytes_append p 0 _ _ _).2
  rw [hys, Nat.zero_add]; iframe

theorem durOf_map_clean (lo : Nat) (xs : List (w8 × Bool)) :
    durOf lo (xs.map (fun x => (x.1, true))) = durOf lo xs := by
  simp only [durOf, List.map_map]; rfl

end osbytes

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

set_option maxRecDepth 20000 in
theorem DB.init.wp_proof (wp_initPages : initPages.spec (GF := GF) (hG := hG))
    (wp_WriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Fdatasync : syscall.Fdatasync.spec (GF := GF) (hG := hG)) :
    DB.init.spec (GF := GF) (hG := hG) := by
  intro db f fd p dqf dq m xs hok hmaps hxs hsz
  have hil := initBytes_length
  simp only [pageBytes] at hil
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
  generalize hI : initBytes = I at hil ⊢
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
  generalize hFd : Z ++ I.drop 8192 = F at hF ⊢
  have hw00 : (W64 0).toNat = 0 := rfl
  have hw0' : 0 ≤ (W64 0).toInt := by word
  have hmc : ∀ lo hi, mcellsAny (GF := GF) m.maps lo hi ⊣⊢ emp := by
    intro lo hi; unfold mcellsAny; rw [hmaps]; exact BigSepM.bigSepM_empty
  ihave Hc := (hmc (min (W64 0).toNat m.size) ((W64 0).toNat + F.length)).2 $$ []
  · iempintro
  icases (osBytes_append p 0 (DFrac.own 1) (xs.take 16384) (xs.drop 16384)).1 $$
    [Hb] with ⟨Hw, Hb2⟩
  · rw [List.take_append_drop]; iexact Hb
  have he2 : (xs.take 16384).length =
      min ((W64 0).toNat + F.length) m.size - min (W64 0).toNat m.size := by
    rw [List.length_take, hw00, hF]; omega
  wp_apply wp_WriteAt f fd p dqf first F (DFrac.own 1) (W64 0) dq ⟨p, true, true⟩ 1 m
      (xs.take 16384) rfl hw0' (by omega) (by omega) he2 (fun _ => rfl)
      $$ [Hinv Hf Hfirst Hfd Hm Hw Hc]
    as %n %err ⟨Hf, Hfirst, Hfd, %j, %ys, %h, %Hres, Hm, Hw, Hc⟩
  · rw [hw00, Nat.zero_min]; iframe Hf Hm Hw Hc Hfirst Hfd; iframe #
  rw [hw00, Nat.zero_min] at *
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
  have hys' := hys.trans (pwBytes_full _ _ _ _ (by omega : 0 < F.length))
  simp only [Nat.zero_min, Nat.sub_self, List.replicate_zero, List.nil_append] at hys'
  simp only [hF] at hys' ⊢
  have hysl : ys.length = 16384 := by
    have := congrArg List.length hys'; simp only [List.length_map, hF] at this; exact this
  ihave Hb := init_join1 p xs ys 16384 hysl $$ [Hw Hb2]
  · iframe
  (try wp_auto)
  wp_apply wp_Fd f fd p dqf $$ [Hf] as Hf
  · iexact Hf
  (try wp_auto)
  wp_apply wp_Fdatasync fd dq ⟨p, true, true⟩ { m with size := pwSize m.size 0 16384, hi := h } 0
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
  -- the file after the first write and sync: `A`, of size `max m.size 16384`
  have hS : pwSize m.size 0 16384 = max m.size 16384 := by rw [pwSize_full _ _ _ (by decide)]
  have hm1 : ({ m with size := pwSize m.size 0 16384, hi := h } : OsMeta).synced 0
        (ys ++ xs.drop 16384) =
      { m with size := max m.size 16384, lo := max m.size 16384, hi := max m.size 16384,
               dur := durOf 0 (ys ++ xs.drop 16384),
               durHi := max m.size 16384 } := by
    simp only [OsMeta.synced, hS, hok, if_true]
  rw [hm1]
  generalize hm1' :
    ({ m with size := max m.size 16384, lo := max m.size 16384, hi := max m.size 16384,
               dur := durOf 0 (ys ++ xs.drop 16384),
               durHi := max m.size 16384 } : OsMeta) = m1
  have hm1s : m1.size = max m.size 16384 := by rw [← hm1']
  have hm1m : m1.maps = ∅ := by rw [← hm1']; exact hmaps
  have hm1ok : m1.ok = true := by rw [← hm1']; exact hok
  simp only [syncedBytes, hok, if_true]
  generalize hA : List.map (fun x => (x.1, true)) (ys ++ List.drop 16384 xs) = A
  have hAl : A.length = max m.size 16384 := by
    rw [← hA, List.length_map, List.length_append, List.length_drop, hysl]; omega
  have hAfst : A.map Prod.fst = F ++ (xs.drop 16384).map Prod.fst := by
    rw [← hA, List.map_map, ← hys', List.map_append]; rfl
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
  generalize hD0 : (I.take 8192).take 4096 = D0 at hD0l hD01 ⊢
  generalize hD1 : (I.take 8192).drop 4096 = D1 at hD1l hD01 ⊢
  icases (osBytes_append p 0 (DFrac.own 1) (A.take 4096) (A.drop 4096)).1 $$
    [Hb] with ⟨HbA, HbB⟩
  · rw [List.take_append_drop]; iexact Hb
  rw [List.length_take, show 0 + min 4096 A.length = 4096 by omega]
  have hA8 : (A.drop 4096).drop 4096 = A.drop 8192 := by rw [List.drop_drop]
  icases (osBytes_append p 4096 (DFrac.own 1) ((A.drop 4096).take 4096) (A.drop 8192)).1 $$
    [HbB] with ⟨HbW, HbC⟩
  · rw [← hA8, List.take_append_drop]; iexact HbB
  rw [List.length_take, List.length_drop, show 4096 + min 4096 (A.length - 4096) = 8192 by omega]
  have hw4 : (W64 4096).toNat = 4096 := rfl
  have hw4' : 0 ≤ (W64 4096).toInt := by word
  have hm4 : min (W64 4096).toNat m1.size = 4096 := by rw [hw4, hm1s]; omega
  have he2 : ((A.drop 4096).take 4096).length =
      min ((W64 4096).toNat + D1.length) m1.size - min (W64 4096).toNat m1.size := by
    rw [List.length_take, List.length_drop, hw4, hD1l, hm1s]; omega
  have hmc1 : ∀ lo hi, mcellsAny (GF := GF) m1.maps lo hi ⊣⊢ emp := by
    intro lo hi; unfold mcellsAny; rw [hm1m]; exact BigSepM.bigSepM_empty
  ihave Hc := (hmc1 (min (W64 4096).toNat m1.size) ((W64 4096).toNat + D1.length)).2 $$ []
  · iempintro
  wp_apply wp_WriteAt f fd p dqf (slice.slice buf w8 (W64 4096) (W64 8192)) D1
      (DFrac.own 1) (W64 4096) dq ⟨p, true, true⟩ 1 m1 ((A.drop 4096).take 4096) rfl hw4'
      (by omega) (by omega) he2 (fun _ => rfl) $$ [Hinv Hf Hbuf1 Hfd Hm HbW Hc]
    as %n2 %err2 ⟨Hf, Hbuf1, Hfd, %j2, %ys2, %h2, %Hres2, Hm, Hw, Hc⟩
  · rw [hm4]; iframe Hf Hm HbW Hc Hbuf1 Hfd; iframe #
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
  rw [show min 4096 m1.size = 4096 by rw [hm1s]; omega]
  have hys2' := hys2.trans (pwBytes_full _ _ _ _ (by omega : 0 < D1.length))
  rw [hw4, show 4096 - min 4096 m1.size = 0 by rw [hm1s]; omega, List.replicate_zero,
    List.nil_append] at hys2'
  have hys2l : ys2.length = 4096 := by
    have := congrArg List.length hys2'; simp only [List.length_map, hD1l] at this; exact this
  ihave Hb := (osBytes_append p 0 (DFrac.own 1) (A.take 4096) (ys2 ++ A.drop 8192)).2 $$
      [HbA Hw HbC]
  · rw [List.length_take, show 0 + min 4096 A.length = 4096 by omega]
    isplitl [HbA]
    · iexact HbA
    · iapply (osBytes_append p 4096 (DFrac.own 1) ys2 (A.drop 8192)).2
      rw [hys2l]; iframe
  (try wp_auto)
  wp_apply wp_Fd f fd p dqf $$ [Hf] as Hf
  · iexact Hf
  (try wp_auto)
  wp_apply wp_Fdatasync fd dq ⟨p, true, true⟩
      { m1 with size := pwSize m1.size (W64 4096).toNat D1.length, hi := h2 } 0
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
  have hS2 : pwSize m1.size 4096 D1.length = max m.size 16384 := by
    rw [pwSize_full _ _ _ (by omega), hD1l, hm1s]; omega
  have hm2 : ({ m1 with size := pwSize m1.size 4096 D1.length, hi := h2 } : OsMeta).synced 0
        (A.take 4096 ++ (ys2 ++ A.drop 8192)) =
      { m with size := max m.size 16384, lo := max m.size 16384, hi := max m.size 16384,
               dur := durOf 0 (A.take 4096 ++ (ys2 ++ A.drop 8192)),
               durHi := max m.size 16384 } := by
    rw [hS2, ← hm1']
    simp only [OsMeta.synced, hok, if_true]
  rw [hm2]
  generalize hm2' :
    ({ m with size := max m.size 16384, lo := max m.size 16384, hi := max m.size 16384,
               dur := durOf 0 (A.take 4096 ++ (ys2 ++ A.drop 8192)),
               durHi := max m.size 16384 } : OsMeta) = m2
  have hm2s : m2.size = max m.size 16384 := by rw [← hm2']
  have hm2m : m2.maps = ∅ := by rw [← hm2']; exact hmaps
  have hm2ok : m2.ok = true := by rw [← hm2']; exact hok
  simp only [syncedBytes, hm1ok, if_true]
  generalize hB : List.map (fun x => (x.1, true)) (A.take 4096 ++ (ys2 ++ A.drop 8192)) = B
  have hBl : B.length = max m.size 16384 := by
    rw [← hB, List.length_map, List.length_append, List.length_append, List.length_take,
      List.length_drop, hys2l]; omega
  have hBfst : (B.drop 4096).map Prod.fst = D1 ++ (A.map Prod.fst).drop 8192 := by
    have e : B.map Prod.fst = (A.take 4096).map Prod.fst ++ (D1 ++ (A.drop 8192).map Prod.fst) := by
      rw [← hB, List.map_map, ← hys2', List.map_append, List.map_append]; rfl
    rw [List.map_drop, e, List.drop_left' (by rw [List.length_map, List.length_take]; omega),
      List.map_drop]
  -- the third write: meta 0 (`buf[:4096]`) at 0
  have hcap0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 4096) ∧
      sint.Z (W64 4096) ≤ sint.Z buf.cap := by
    have := Hwf.2; rw [hbl, show sint.Z (W64 16384) = 16384 from rfl] at this
    rw [show sint.Z (W64 4096) = 4096 from rfl, show sint.Z (W64 0) = 0 from rfl]
    exact ⟨by decide, by decide, by omega⟩
  have hw0z : (W64 0).toNat = 0 := rfl
  have hw0z' : 0 ≤ (W64 0).toInt := by word
  rw [ite_eq_left hcap0]
  (try wp_auto)
  icases (osBytes_append p 0 (DFrac.own 1) (B.take 4096) (B.drop 4096)).1 $$
    [Hb] with ⟨Hb0, Hb1⟩
  · rw [List.take_append_drop]; iexact Hb
  rw [List.length_take, show 0 + min 4096 B.length = 4096 by omega]
  have he0 : 0 < D0.length := by omega
  have he3 : (B.take 4096).length =
      min ((W64 0).toNat + D0.length) m2.size - min (W64 0).toNat m2.size := by
    rw [List.length_take, hw0z, hm2s, hD0l]; omega
  have hmc2 : ∀ lo hi, mcellsAny (GF := GF) m2.maps lo hi ⊣⊢ emp := by
    intro lo hi; unfold mcellsAny; rw [hm2m]; exact BigSepM.bigSepM_empty
  ihave Hc := (hmc2 (min (W64 0).toNat m2.size) ((W64 0).toNat + D0.length)).2 $$ []
  · iempintro
  wp_apply wp_WriteAt f fd p dqf (slice.slice buf w8 (W64 0) (W64 4096)) D0
      (DFrac.own 1) (W64 0) dq ⟨p, true, true⟩ 1 m2 (B.take 4096) rfl hw0z' he0 (by omega)
      he3 (fun _ => rfl) $$ [Hinv Hf Hbuf0 Hfd Hm Hb0 Hc]
    as %n3 %err3 ⟨Hf, Hbuf0, Hfd, %j3, %ys3, %h3, %Hres3, Hm, Hw, Hc⟩
  · rw [hw0z, Nat.zero_min]; iframe Hf Hm Hb0 Hc Hbuf0 Hfd; iframe #
  rw [hw0z, Nat.zero_min] at *
  obtain ⟨hj3, hys3, hh3, ⟨rfl, rfl, rfl⟩ | ⟨rfl, hne3⟩⟩ := Hres3
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
  have hys3' := hys3.trans (pwBytes_full _ _ _ _ he0)
  simp only [Nat.zero_min, Nat.sub_self, List.replicate_zero, List.nil_append] at hys3'
  have hys3l : ys3.length = 4096 := by
    have := congrArg List.length hys3'; simp only [List.length_map, hD0l] at this; exact this
  ihave Hb := (osBytes_append p 0 (DFrac.own 1) ys3 (B.drop 4096)).2 $$ [Hw Hb1]
  · rw [hys3l]; iframe
  (try wp_auto)
  wp_apply wp_Fd f fd p dqf $$ [Hf] as Hf
  · iexact Hf
  (try wp_auto)
  wp_apply wp_Fdatasync fd dq ⟨p, true, true⟩ { m2 with size := pwSize m2.size 0 D0.length, hi := h3 } 0
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
  have hfin : (ys3 ++ B.drop 4096).map (fun x => (x.1, true)) = initFile xs := by
    have key : (ys3 ++ B.drop 4096).map Prod.fst = I ++ (xs.map Prod.fst).drop 16384 := by
      rw [List.map_append, hys3', hBfst, hAfst, ← hFd, List.append_assoc Z,
        List.drop_left' hZl, ← List.append_assoc, hD01, ← List.append_assoc,
        List.take_append_drop, List.map_drop]
    unfold initFile
    rw [hI, ← key, List.map_map]; rfl
  have hm3 : ({ m2 with size := pwSize m2.size 0 D0.length, hi := h3 } : OsMeta).synced 0
        (ys3 ++ B.drop 4096) =
      { m with size := max m.size 16384, lo := max m.size 16384, hi := max m.size 16384,
               dur := durOf 0 (initFile xs), durHi := max m.size 16384 } := by
    rw [← hm2']
    simp only [OsMeta.synced, pwSize_full _ _ _ he0, hok, if_true]
    rw [hD0l, show max (max m.size 16384) (0 + 4096) = max m.size 16384 by omega, ← hfin,
      durOf_map_clean]
  have hsz64 : sint.Z (W64 (m.size : Int)) = m.size := by
    have : (m.size : Int) < 2 ^ 63 := by omega
    word
  rw [hm3]
  simp only [syncedBytes, hm2ok, if_true]
  rw [hfin]
  wp_if_destruct
  · iapply HΦ
    iframe Hf Hfd
    ileft
    isplitr
    · ipureintro; rfl
    · rw [hsz64, show sint.Z (W64 16384) = 16384 from rfl] at Hif
      rw [show max (m.size : Int) 16384 = 16384 by omega]
      simp only [hok]
      iframe
  · iapply HΦ
    iframe Hf Hfd
    ileft
    isplitr
    · ipureintro; rfl
    · rw [hsz64, show sint.Z (W64 16384) = 16384 from rfl] at Hif
      rw [show max (m.size : Int) 16384 = m.size by omega]
      simp only [hok]
      iframe

end proof

end bboltfs
end EtcdGrove
end Perennial
