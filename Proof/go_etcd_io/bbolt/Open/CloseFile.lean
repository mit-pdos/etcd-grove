/-
**The file a closed database gives back** (session bbolt-inv, `DB.Close_own.spec`): the page-cache
bytes `Close` holds once it has taken the store's slots (`store_close`), the writer side's `W` slots
(`wBytes`) and the two halves of the metas (`metaOsBytes`, the writer side's and `metaR`'s), as one
run of the file's bytes from offset 0, whose values are `closeBytes` (`Inv/CloseImage`): the file
is whole pages (`wdbOK`), each slot one of the three.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.CloseImage
public import Proof.go_etcd_io.bbolt.Open.CloseMapDefs
public import Proof.go_etcd_io.bbolt.Mmap.RemapBase
public import Proof.go_etcd_io.bbolt.Mmap.Cells
public import Proof.go_etcd_io.bbolt.Mmap.RemapCells
public import Proof.go_etcd_io.bbolt.Commit.MetaBytes
public import Proof.go_etcd_io.bbolt.Open.Close
public import Proof.go_etcd_io.bbolt.Mmap.MunmapNoErr
public import Spec.os.File__Close
public import Spec.syscall.Flock

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section bytes
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- Two runs of a file's bytes, one after the other, as one. -/
theorem osBytes_app' (p : BFile) (off : Nat) (dq : DFrac) (xs ys : List ByteG) :
    bBytes (GF := GF) p off dq xs ∗ bBytes p (off + xs.length) dq ys ⊢
      bBytes p off dq (xs ++ ys) := by
  exact (bBytes_append _ off _ xs ys).2

/-- A run of a file's bytes, split. -/
theorem osBytes_split' (p : BFile) (off : Nat) (dq : DFrac) (xs ys : List ByteG) :
    bBytes (GF := GF) p off dq (xs ++ ys) ⊢
      bBytes p off dq xs ∗ bBytes p (off + xs.length) dq ys := by
  exact (bBytes_append _ off _ xs ys).1

/-- **Slots `0 … n - 1`, each a whole page, as the file's first `4096 · n` bytes.** -/
theorem osSlots_range (p : BFile) (g : Nat → List w8) :
    ∀ n, (∀ s, s < n → (g s).length = 4096) →
    ([∗list] s ∈ List.range n, osSlot (GF := GF) p s (g s)) ⊢
      ∃ xs : List ByteG, bBytes p 0 (DFrac.own 1) xs ∗
        ⌜xs.map Prod.fst = (List.range' 0 n).flatMap g ∧ xs.length = 4096 * n⌝
  | 0, _ => by
    iintro -
    iexists []
    isplitl
    · iapply (osBytes_nil' (GF := GF) p 0 _).2; iempintro
    · ipureintro; simp
  | n + 1, hg => by
    rw [List.range_succ]
    iintro H
    icases BigSepL.bigSepL_append.1 $$ H with ⟨H, Hn⟩
    icases osSlots_range p g n (fun s hs => hg s (by omega)) $$ H with ⟨%xs, Hxs, %hxs⟩
    icases BigSepL.bigSepL_singleton.1 $$ Hn with Hn
    unfold osSlot
    icases Hn with ⟨%ys, Hys, %hys⟩
    have hyl : ys.length = 4096 := by
      rw [← List.length_map (f := Prod.fst), hys]; exact hg n (by omega)
    iexists xs ++ ys
    isplitl [Hxs Hys]
    · iapply osBytes_app' p 0 _ xs ys
      iframe Hxs
      rw [Nat.zero_add, hxs.2]; iexact Hys
    · ipureintro
      refine ⟨?_, by rw [List.length_append, hxs.2, hyl]; omega⟩
      rw [List.map_append, hxs.1, hys,
        show List.range' 0 (n + 1) = List.range' 0 n ++ List.range' (0 + n) 1 from
          List.range'_append_1.symm, List.flatMap_append, List.range'_one, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, Nat.zero_add]

/-- **The metas' two halves, as slots 0 and 1** (the writer side's and `metaR`'s). -/
theorem metaOsBytes_slots (p : BFile) (C : CommitSt) (h0 : C.m0.length = 4096)
    (h1 : C.m1.length = 4096) :
    metaOsBytes (GF := GF) p (DFrac.own (1 : Qp).half) C ∗
      metaOsBytes (GF := GF) p (DFrac.own (1 : Qp).half) C ⊢
      osSlot p 0 C.m0 ∗ osSlot p 1 C.m1 := by
  unfold metaOsBytes
  iintro ⟨⟨%xs, H1, %hx⟩, ⟨%ys, H2, %hy⟩⟩
  have hl : xs.length = ys.length := by
    have h1 := congrArg List.length hx
    have h2 := congrArg List.length hy
    simp only [List.length_map] at h1 h2
    omega
  ihave H := osBytes_join_h p xs ys 0 hl $$ [H1 H2]
  · iframe
  have hxl : (xs.take 4096).length = 4096 := by
    have := congrArg List.length hx
    simp only [List.length_map, List.length_append] at this
    simp only [List.length_take]; omega
  rw [← List.take_append_drop 4096 xs]
  icases osBytes_split' p 0 _ (xs.take 4096) (xs.drop 4096) $$ H with ⟨Ha, Hb⟩
  have hmap : (xs.take 4096).map Prod.fst = C.m0 ∧ (xs.drop 4096).map Prod.fst = C.m1 := by
    rw [List.map_take, List.map_drop, hx, List.take_left' h0, List.drop_left' h0]
    exact ⟨rfl, rfl⟩
  unfold osSlot
  isplitl [Ha]
  · iexists _; rw [Nat.mul_zero]; iframe Ha; ipureintro; exact hmap.1
  · iexists _; rw [Nat.zero_add, hxl, Nat.mul_one]; iframe Hb; ipureintro; exact hmap.2

/-- **The closed file's bytes** (see the file header): the metas, the store's slots `bs` and the
writer side's `W` slots of an idle writer side `w` (`wdbOK`), one run from offset 0 holding
`closeBytes`, `w.m.size` long. -/
theorem close_file_bytes (p : BFile) (w : WDb) (hok : wdbOK w) (bs : Nat → List w8)
    (hm0 : w.C.m0.length = 4096) (hm1 : w.C.m1.length = 4096)
    (hbs : ∀ s ∈ slotsOf w.C w.fl, 2 ≤ s ∧ (bs s).length = 4096) (h2 : 2 ≤ w.m.size / 4096)
    (hal : w.m.size % 4096 = 0) (W' : List Nat) (hW' : ∀ s ∈ w.W, s ∈ W') :
    osSlot (GF := GF) p 0 w.C.m0 ∗ osSlot p 1 w.C.m1 ∗
      ([∗list] s ∈ slotsOf w.C w.fl, osSlot p s (bs s)) ∗ wBytes p W' w.wb w.m.size ⊢
      ∃ xs : List ByteG, bBytes p 0 (DFrac.own 1) xs ∗
        ⌜xs.map Prod.fst = closeBytes w.C w.fl bs w.wb (w.m.size / 4096) ∧
          xs.length = w.m.size⌝ := by
  have hsz : w.m.size = 4096 * (w.m.size / 4096) := by omega
  generalize hn : w.m.size / 4096 = n at *
  have hW : ∀ s, s ∈ wSlots n w.C w.fl → s ∈ w.W := by
    intro s hs
    obtain ⟨a, b, c⟩ := (mem_wSlots _ _ _ s).1 hs
    refine (wdbOK_mem_W w hok s).2 ⟨a, ?_, c⟩
    have := Nat.le_max_right (mapLen w.ms) w.m.size
    have : n ≤ max (mapLen w.ms) w.m.size / 4096 := by
      rw [← hn]; exact Nat.div_le_div_right this
    omega
  -- the store slots lie below the high-water mark, inside the file
  have hS : ∀ s ∈ slotsOf w.C w.fl, 2 ≤ s ∧ s < n := by
    intro s hs
    refine ⟨(hbs s hs).1, ?_⟩
    have h1 := hok.2.2.2.2.2.2.2.2.2.2.1 s ((mem_slotsOf _ _ s).1 hs)
    have h3 := hok.2.2.1
    have : w.C.hwm ≤ n := by
      rw [← hn]; exact (Nat.le_div_iff_mul_le (by decide)).2 (by omega)
    omega
  have hP := slots_partition n (slotsOf w.C w.fl) (wSlots n w.C w.fl) h2 (slotsOf_nodup _ _)
    (wSlots_nodup _ _ _) hS (fun s => mem_wSlots _ _ _ s)
  -- each slot's bytes, as `closeSlot`'s
  have hcs : ∀ s ∈ slotsOf w.C w.fl, closeSlot w.C w.fl bs w.wb s = bs s := by
    intro s hs
    have := (hbs s hs).1
    unfold closeSlot; rw [if_neg (by omega), if_neg (by omega), if_pos hs]
  have hcw : ∀ s ∈ wSlots n w.C w.fl, closeSlot w.C w.fl bs w.wb s = w.wb s := by
    intro s hs
    obtain ⟨a, -, c⟩ := (mem_wSlots _ _ _ s).1 hs
    unfold closeSlot; rw [if_neg (by omega), if_neg (by omega), if_neg c]
  have hlen : ∀ s, s < n → (closeSlot w.C w.fl bs w.wb s).length = 4096 := by
    intro s hs
    unfold closeSlot
    by_cases h0 : s = 0
    · rw [if_pos h0]; exact hm0
    rw [if_neg h0]
    by_cases h1 : s = 1
    · rw [if_pos h1]; exact hm1
    rw [if_neg h1]
    by_cases h2 : s ∈ slotsOf w.C w.fl
    · rw [if_pos h2]; exact (hbs s h2).2
    · rw [if_neg h2]
      exact hok.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 s (hW s ((mem_wSlots _ _ _ s).2 ⟨by omega, hs, h2⟩))
        (by omega)
  iintro ⟨H0, H1, HS, HW⟩
  ihave HW := wBytes_restrict p W' (wSlots n w.C w.fl) w.wb w.m.size (wSlots_nodup _ _ _)
    (fun s hs _ => hW' s (hW s hs)) $$ HW
  ihave HW : [∗list] s ∈ wSlots n w.C w.fl, osSlot (GF := GF) p s
      (closeSlot w.C w.fl bs w.wb s) $$ [HW]
  · unfold wBytes
    iapply BigSepL.bigSepL_mono (Φ := fun _ s => iprop(if 4096 * (s + 1) ≤ w.m.size then
        iprop(∃ xs : List ByteG, bBytes p (4096 * s) (DFrac.own 1) xs ∗
          ⌜xs.map Prod.fst = w.wb s⌝)
      else if 4096 * s < w.m.size then
        iprop(∃ xs : List ByteG, bBytes p (4096 * s) (DFrac.own 1) xs ∗
          ⌜xs.map Prod.fst = (w.wb s).take (w.m.size - 4096 * s)⌝)
      else iprop(emp))) ?_ $$ HW
    intro k s hks
    have hs := List.mem_of_getElem? hks
    have hlt := ((mem_wSlots _ _ _ s).1 hs).2.1
    rw [if_pos (by omega), hcw s hs]
    unfold osSlot; exact .rfl
  ihave HS : [∗list] s ∈ slotsOf w.C w.fl, osSlot (GF := GF) p s
      (closeSlot w.C w.fl bs w.wb s) $$ [HS]
  · iapply BigSepL.bigSepL_mono (Φ := fun _ s => osSlot (GF := GF) p s (bs s)) ?_ $$ HS
    intro k s hks
    rw [hcs s (List.mem_of_getElem? hks)]
  ihave Hall : [∗list] s ∈ List.range n, osSlot (GF := GF) p s (closeSlot w.C w.fl bs w.wb s)
    $$ [H0 H1 HS HW]
  · iapply (BigSepL.bigSepL_perm hP).1
    iapply BigSepL.bigSepL_cons.2
    isplitl [H0]
    · unfold closeSlot; simp only [↓reduceIte]; iexact H0
    iapply BigSepL.bigSepL_cons.2
    isplitl [H1]
    · unfold closeSlot; simp only [show (1 : Nat) ≠ 0 from by decide, ↓reduceIte]; iexact H1
    iapply BigSepL.bigSepL_append.2
    iframe
  icases osSlots_range p (closeSlot w.C w.fl bs w.wb) n hlen $$ Hall with ⟨%xs, Hxs, %hxs⟩
  iexists xs
  iframe Hxs
  ipureintro
  exact ⟨hxs.1, by rw [hxs.2]; omega⟩

end bytes


section closeM
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem closeMapResM_res (p : BFile) (C : CommitSt) (L : List (Nat × Nat)) (m : OsMeta)
    (ms : MapSt) : closeMapResM (GF := GF) p C L m ms ⊢ closeMapRes p ms := by
  rcases ms with _ | ⟨b, l⟩
  · simp only [closeMapResM, closeMapRes]; exact .rfl
  · simp only [closeMapResM, closeMapRes]
    iintro ⟨%h, #Hinv, Hm, %vf, Hc⟩
    iexists C, L, m, vf
    iframe
    isplitr
    · ipureintro; exact h
    iexact Hinv

/-- `db.munmap()` of what `close` unmaps, with no error: the fields cleared, the `OsMeta` back. -/
theorem DB.munmap.wp_closeResNoErrM (hMunmap : DB.munmap.specNoErr (GF := GF) (hG := hG))
    (hne : FsNoErr) (db : Loc) (lg : GoInterface) (ms : MapSt) (p : BFile) (C : CommitSt)
    (L : List (Nat × Nat)) (m : OsMeta) (hdb : db ≠ null) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗
        db.[DB, go!"logger"] ↦□ lg ∗ boltLogger lg ∗
        mapFields db (DFrac.own 1) ms ∗ db.[DB, go!"datasz"] ↦ W64 (mapLen ms : Int) ∗
        closeMapResM p C L m ms }}
      (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"munmap")) (Val #()))
    {{ RET #(interface.nil : GoInterface); mapFields db (DFrac.own 1) (none : MapSt) ∗
        db.[DB, go!"datasz"] ↦ W64 0 ∗ closeMapBack p C L m ms }} := by
  iintro %Φ ⟨#Hpkg, #Hos, #Hlg, #Hlgok, Hmf, Hdsz, Hmr⟩ HΦ
  rcases ms with _ | ⟨b, l⟩
  · simp only [closeMapResM, closeMapBack, mapLen]
    wp_apply DB.munmap.wp_proof_none db (W64 ((0 : Nat) : Int)) $$ [Hmf Hdsz] as ⟨Hmf, Hdsz⟩
    · iframe
    iapply HΦ
    iframe
  · simp only [closeMapResM, closeMapBack, mapLen]
    icases Hmr with ⟨%hm, #Hinv, Hosm, %vf, Hc⟩
    wp_apply hMunmap hne db b l lg p C L m vf hdb hm.1 hm.2.1 hm.2.2 $$ [Hmf Hdsz Hosm Hc]
      as ⟨Hmf, Hdsz, Hosm⟩
    · iframe; iframe #
    iapply HΦ
    iframe

/-- **`db.close()` over owned fields, with no error, the file's `OsMeta` back** (as
for `DB.Close`; the file non-nil): under `FsNoErr`, which refutes the callees' error arms. -/
abbrev DB.close.spec_ownedNoErrM : Prop :=
  FsNoErr →
  ∀ (db : Loc) (lg : GoInterface) (dqr : DFrac) (fli : GoInterface) (wa : GoFunc) (s : GoString)
    (ms : MapSt) (p : BFile) (C : CommitSt) (L : List (Nat × Nat)) (m : OsMeta) (f : Loc) (fd : w64)
    (name : GoString) (d : OsFd),
  db ≠ null → f ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗
      db.[DB, go!"logger"] ↦□ lg ∗ boltLogger lg ∗ db.[DB, go!"readOnly"] ↦{dqr} false ∗
      db.[DB, go!"opened"] ↦ true ∗ db.[DB, go!"freelist"] ↦ fli ∗
      (db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦ wa ∗ db.[DB, go!"path"] ↦ s ∗
      mapFields db (DFrac.own 1) ms ∗ db.[DB, go!"datasz"] ↦ W64 (mapLen ms : Int) ∗
      closeMapResM p C L m ms ∗
      db.[DB, go!"file"] ↦ f ∗ fileOwn f fd name (DFrac.own 1) ∗
        osFd fd (DFrac.own 1) d ∗ lockToks fd d }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"close")) (Val #()))
  {{ RET #(interface.nil : GoInterface); db.[DB, go!"readOnly"] ↦{dqr} false ∗
      db.[DB, go!"opened"] ↦ false ∗ db.[DB, go!"freelist"] ↦ interface.nil ∗
      (db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦ func.nil ∗ db.[DB, go!"path"] ↦ (go!"" : GoString) ∗
      mapFields db (DFrac.own 1) (none : MapSt) ∗ db.[DB, go!"datasz"] ↦ W64 0 ∗
      db.[DB, go!"file"] ↦ null ∗ closeMapBack p C L m ms }}

theorem DB.close.wp_proof_ownedNoErrM [os.Assumptions] [syscall.Assumptions]
    (hMunmap : DB.munmap.specNoErr (GF := GF) (hG := hG))
    (hFd : os.File.Fd.spec (GF := GF) (hG := hG))
    (hFlock : syscall.Flock.spec (GF := GF) (hG := hG))
    (hClose : os.File.Close.spec (GF := GF) (hG := hG)) :
    DB.close.spec_ownedNoErrM (GF := GF) (hG := hG) := by
  intro hne db lg dqr fli wa s ms p C L m f fd name d hdb hf
  wp_start as ⟨#Hos, #Hlg, #Hlgok, Hro, Hop, Hfl, Hwa, Hpath, Hmf, Hdsz, Hmr, Hfile, Hfo, Hfd, Hlt⟩
  wp_auto
  -- `munmap`: `nil`, nothing appended, the `OsMeta` back
  wp_apply DB.munmap.wp_closeResNoErrM hMunmap hne db lg ms p C L m hdb $$ [Hmf Hdsz Hmr]
    as ⟨Hmf, Hdsz, Hback⟩
  · iframe; iframe #
  try wp_auto
  rw [decide_eq_false hf]
  iunfold lockToks at Hlt
  icases Hlt with ⟨Hlo, Hfl⟩
  try wp_auto
  wp_func_call
  try wp_auto
  wp_apply hFd f fd name (DFrac.own 1) $$ [Hfo] as Hfo
  · rw [← fileOwn_eq]; iexact Hfo
  try wp_auto
  wp_apply hFlock fd (W64 8) d none false rfl (fun h => absurd rfl h)
    $$ [Hfd Hfl] as %e ⟨%he, Hout⟩
  · iframe; iframe #
  have he0 : e = 0 := by
    rcases he with he | ⟨hn, -⟩ | hn
    · exact he
    · exact absurd rfl hn
    · exact absurd (FsNoErr.on hne) hn
  subst he0
  unfold lockOut
  icases Hout with ⟨%d', Hfd, Hfl, %hd'⟩
  ihave Hlo : lockTok LockKind.ofd fd d' $$ [Hlo]
  · rcases hd'.1 with rfl | rfl
    · iexact Hlo
    · iapply (lockTok_setLk_ne fd d none (by decide)).2; iexact Hlo
  simp only [errnoErr, ↓reduceIte]
  try wp_auto
  wp_apply hClose f fd name d' $$ [Hfo Hfd Hlo Hfl] as %cerr ⟨Hfo, %hc, -⟩
  · unfold lockToks; iframe; iframe #
  obtain rfl : cerr = interface.nil := hc.resolve_right (fun h => h hne)
  try wp_auto
  iapply HΦ
  iframe

end closeM

end bbolt
end EtcdGrove
end Perennial
