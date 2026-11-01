/- Lean-first (no Rocq counterpart). The proof of `db.init()`: `initPages` into a fresh buffer `buf`; a second buffer `first`, zero, with `buf`'s last two pages copied in; `first` written at 0 with `WriteAt` (all four pages, the metas zero; it may extend the file), `Fdatasync`, then `buf`'s first two pages (the metas) at 0, `Fdatasync`. -/
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
  have hm1 : ({ m with size := pwSize m.size 0 16384, hi := h } : OsMeta).synced =
      { m with size := max m.size 16384, lo := max m.size 16384, hi := max m.size 16384 } := by
    simp only [OsMeta.synced, hS]
  rw [hm1]
  generalize hm1' :
    ({ m with size := max m.size 16384, lo := max m.size 16384, hi := max m.size 16384 } : OsMeta) = m1
  have hm1s : m1.size = max m.size 16384 := by rw [← hm1']
  have hm1m : m1.maps = ∅ := by rw [← hm1']; exact hmaps
  have hm1ok : m1.ok = true := by rw [← hm1']; exact hok
  simp only [syncedBytes, hok, if_true]
  generalize hA : List.map (fun x => (x.1, true)) (ys ++ List.drop 16384 xs) = A
  have hAl : A.length = max m.size 16384 := by
    rw [← hA, List.length_map, List.length_append, List.length_drop, hysl]; omega
  have hAfst : A.map Prod.fst = F ++ (xs.drop 16384).map Prod.fst := by
    rw [← hA, List.map_map, ← hys', List.map_append]; rfl
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
      rw [List.map_append, hys2', List.map_drop, hAfst, ← hFd, List.append_assoc,
        List.drop_left' hZl, ← List.append_assoc, List.take_append_drop,
        List.map_drop]
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
