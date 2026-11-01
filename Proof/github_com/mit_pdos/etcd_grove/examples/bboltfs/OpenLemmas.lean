/- Lean-first (no Rocq counterpart). `Open`'s lemmas: a file of clean bytes holding an open
database's meta pages as a stored database (`dbStored`: its committed pages discarded,
`pageIs`), for a fresh file with a valid meta and for the file `init` lays out. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.Open
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__init
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.Writer
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.MapLoan
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.InitLayout

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section pure
variable [GooseExts]

/-- Page `r` of the bytes `F`. -/
abbrev pageOf (F : List w8) (r : Nat) : List w8 := (F.drop (4096 * r)).take 4096

theorem pageOf_length (F : List w8) (r : Nat) (h : 4096 * (r + 1) ≤ F.length) :
    (pageOf F r).length = 4096 := by
  simp only [pageOf, List.length_take, List.length_drop]; omega

/-- The file `init` lays out (`initFile`), as bytes. -/
theorem initFile_fst (xs : List (w8 × Bool)) :
    (initFile xs).map Prod.fst = initBytes ++ (xs.map Prod.fst).drop 16384 := by
  unfold initFile; rw [List.map_map]; exact List.map_id _

theorem initFile_take (xs : List (w8 × Bool)) :
    ((initFile xs).map Prod.fst).take 8192 = initBytes.take 8192 := by
  rw [initFile_fst, List.take_append_of_le_length (by rw [initBytes_length]; decide)]

theorem initFile_clean (xs : List (w8 × Bool)) :
    initFile xs = ((initFile xs).map Prod.fst).map (·, true) := by
  unfold initFile; simp only [List.map_map, Function.comp_def]

theorem initFile_length (xs : List (w8 × Bool)) :
    (initFile xs).length = max xs.length 16384 := by
  unfold initFile
  simp only [List.length_map, List.length_append, List.length_drop, initBytes_length, pageBytes]
  omega

theorem initFile_root (xs : List (w8 × Bool)) :
    pageVal (pageOf ((initFile xs).map Prod.fst) 3) = none := by
  rw [initFile_fst, pageOf]
  have hI : initBytes = (metaPageBytes 0 ++ metaPageBytes 1 ++ emptyPageBytes (W64 2) (W16 16)) ++
      emptyPageBytes (W64 3) (W16 2) := rfl
  have h1 : (initBytes ++ (xs.map Prod.fst).drop 16384).drop (4096 * 3) =
      emptyPageBytes (W64 3) (W16 2) ++ (xs.map Prod.fst).drop 16384 := by
    rw [hI, List.append_assoc, List.drop_left' (by simp [metaPageBytes_length, emptyPageBytes_length, pageBytes])]
  rw [h1, List.take_left' (by rw [emptyPageBytes_length])]
  exact initRoot_val

end pure

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

/-- Clean bytes of pages `[s, s + k)` of `F`, as committed pages. -/
theorem pages_of_bytes (p : GoString) (dq : DFrac) (F : List w8) :
    ∀ k s, 4096 * (s + k) ≤ F.length →
    osBytes (GF := GF) p (4096 * s) dq (((F.drop (4096 * s)).take (4096 * k)).map (·, true)) ⊢
      |==> [∗list] r ∈ List.range' s k, pageIs (GF := GF) p r (pageOf F r)
  | 0, s, _ => by
    iintro _; imodintro; simp only [List.range'_zero]; iapply BigSepL.bigSepL_nil.2; iempintro
  | k + 1, s, h => by
    iintro H
    rw [show 4096 * (k + 1) = 4096 + 4096 * k by omega, List.take_add, List.map_append]
    icases (osBytes_app p (4096 * s) dq _ _).1 $$ H with ⟨H1, H2⟩
    rw [List.length_map, List.length_take, List.length_drop,
      show 4096 * s + min 4096 (F.length - 4096 * s) = 4096 * (s + 1) by omega, List.drop_drop,
      show 4096 * s + 4096 = 4096 * (s + 1) by omega] at *
    imod pageIs_of p s dq (pageOf F s) (pageOf_length F s (by omega)) $$ H1 with H1
    imod pages_of_bytes p dq F k (s + 1) (by omega) $$ H2 with H2
    imodintro
    rw [List.range'_succ]
    iapply BigSepL.bigSepL_cons.2
    iframe

/-- Committed pages, forgetting their contents. -/
theorem pages_ex (p : GoString) (G : Nat → List w8) :
    ∀ k s, ([∗list] r ∈ List.range' s k, pageIs (GF := GF) p r (G r)) ⊢
      [∗list] r ∈ List.range' s k, ∃ B', pageIs (GF := GF) p r B'
  | 0, s => by iintro _; simp only [List.range'_zero]; iapply BigSepL.bigSepL_nil.2; iempintro
  | k + 1, s => by
    iintro H
    rw [List.range'_succ]
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H2⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [H1]
    · iexists G s; iexact H1
    · iapply pages_ex p G k (s + 1) $$ H2

/-- A file of clean bytes `F` holding an open database's meta pages, as a stored database at its
current meta. -/
theorem stored_of_bytes (p : GoString) (m : OsMeta) (F : List w8) (hl : F.length = m.size)
    (hmp : metaPagesOk (F.take 8192)) (hpg : 4096 * curPgid (F.take 8192) ≤ m.size)
    (hok : m.ok = true) (hmaps : m.maps = ∅) (h16 : 4 * 4096 ≤ m.size) (h40 : m.size ≤ 2 ^ 40) :
    osMeta (GF := GF) p (DFrac.own 1) (some m) ∗ osBytes (GF := GF) p 0 (DFrac.own 1) (F.map (·, true)) ⊢
      |==> dbStored (GF := GF) p (curMeta (F.take 8192)).txid'.toNat
        (pageVal (pageOf F (curRoot (F.take 8192)))) := by
  have hl8 := hmp.1
  have hr2 := hmp.2.2.1
  have hrp := hmp.2.2.2.1
  generalize hn : curPgid (F.take 8192) = n at hpg hr2 hrp
  generalize hrt : curRoot (F.take 8192) = rt at hr2 hrp
  have hF : F.map (·, true) = (F.take 8192).map (·, true) ++
      (((F.drop (4096 * 2)).take (4096 * (n - 2))).map (·, true) ++ (F.drop (4096 * n)).map (·, true)) := by
    rw [← List.map_append, ← List.map_append]
    congr 1
    conv => lhs; rw [← List.take_append_drop 8192 F]
    congr 1
    conv => lhs; rw [← List.take_append_drop (4096 * (n - 2)) (F.drop 8192)]
    rw [List.drop_drop, show 8192 + 4096 * (n - 2) = 4096 * n by omega]
  rw [hF]
  iintro ⟨Hm, Hb⟩
  icases (osBytes_app p 0 _ _ _).1 $$ Hb with ⟨Hb0, Hb⟩
  icases (osBytes_app p _ _ _ _).1 $$ Hb with ⟨Hb1, Hb2⟩
  simp only [List.length_map, List.length_take, List.length_drop]
  rw [show 0 + min 8192 F.length = 4096 * 2 by omega,
    show 4096 * 2 + min (4096 * (n - 2)) (F.length - 4096 * 2) = 4096 * n by omega]
  imod pages_of_bytes p (DFrac.own 1) F (n - 2) 2 (by omega) $$ Hb1 with #Hps
  ihave Hr := pages_acc (fun r => pageIs (GF := GF) p r (pageOf F r)) rt n (by omega) (by omega) $$ Hps
  icases Hr with ⟨#Hr, -⟩
  imodintro
  unfold dbStored
  iexists m, F.take 8192, (F.take 8192).map (·, true), (F.drop (4096 * n)).map (·, true), pageOf F rt
  rw [hn, hrt]
  iframe Hm Hb0 Hb2
  isplitr
  · iapply pages_ex p (pageOf F) (n - 2) 2 $$ Hps
  iframe Hr
  ipureintro
  refine ⟨⟨?_, ?_, hmp, by rw [hn]; exact hpg, ?_, hok, hmaps, h16, h40⟩, rfl, rfl⟩
  · rw [List.map_map]; exact List.map_id _
  · intro x hx; simp only [List.mem_map] at hx; obtain ⟨_, _, rfl⟩ := hx; rfl
  · rw [hn, List.length_map, List.length_drop, hl]

end lemmas

end bboltfs
end EtcdGrove
end Perennial
