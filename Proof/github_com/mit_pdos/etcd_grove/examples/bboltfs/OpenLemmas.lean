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
    osBytes (GF := GF) p 0 (DFrac.own 1) (F.map (·, true)) ⊢
      |==> dbStoredAt (GF := GF) p (curMeta (F.take 8192)).txid'.toNat
        (pageVal (pageOf F (curRoot (F.take 8192)))) m := by
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
  iintro Hb
  icases (osBytes_app p 0 _ _ _).1 $$ Hb with ⟨Hb0, Hb⟩
  icases (osBytes_app p _ _ _ _).1 $$ Hb with ⟨Hb1, Hb2⟩
  simp only [List.length_map, List.length_take, List.length_drop]
  rw [show 0 + min 8192 F.length = 4096 * 2 by omega,
    show 4096 * 2 + min (4096 * (n - 2)) (F.length - 4096 * 2) = 4096 * n by omega]
  imod pages_of_bytes p (DFrac.own 1) F (n - 2) 2 (by omega) $$ Hb1 with #Hps
  ihave Hr := pages_acc (fun r => pageIs (GF := GF) p r (pageOf F r)) rt n (by omega) (by omega) $$ Hps
  icases Hr with ⟨#Hr, -⟩
  imodintro
  unfold dbStoredAt
  iexists F.take 8192, (F.take 8192).map (·, true), (F.drop (4096 * n)).map (·, true), pageOf F rt
  rw [hn, hrt]
  iframe Hb0 Hb2
  isplitr
  · iapply pages_ex p (pageOf F) (n - 2) 2 $$ Hps
  iframe Hr
  ipureintro
  refine ⟨⟨?_, ?_, hmp, by rw [hn]; exact hpg, ?_, hok, hmaps, h16, h40⟩, rfl, rfl⟩
  · rw [List.map_map]; exact List.map_id _
  · intro x hx; simp only [List.mem_map] at hx; obtain ⟨_, _, rfl⟩ := hx; rfl
  · rw [hn, List.length_map, List.length_drop, hl]

/-- A file `init` lays out: of `OsMeta` `m` (no mapping, no byte lost, at most 1 TiB) and bytes
`xs`, shorter than four pages or with no valid meta. -/
def initAt (p : GoString) (m : OsMeta) : IProp GF :=
  iprop(∃ xs : List (w8 × Bool), osBytes (GF := GF) p 0 (DFrac.own 1) xs ∗
    ⌜xs.length = m.size ∧ m.maps = ∅ ∧ m.ok = true ∧ m.size ≤ 2 ^ 30 ∧
      (m.size < 4 * 4096 ∨ (¬ metaValid (fileMeta ((xs.map Prod.fst).take 8192) 0) ∧
        ¬ metaValid (fileMeta ((xs.map Prod.fst).take 8192) 1)))⌝)

/-- The file once open, of `OsMeta` `m`: one `init` lays out (at transaction 1, with no value), or
a stored database. -/
def openSt (p : GoString) (t : Nat) (vo : Option w64) (m : OsMeta) : IProp GF :=
  iprop((⌜t = 1 ∧ vo = none⌝ ∗ initAt (GF := GF) p m) ∨ dbStoredAt (GF := GF) p t vo m)

/-- The `OsMeta` of a file after an open that may create it. -/
def openMetaOf : Option OsMeta → OsMeta
  | some m => m
  | none => newMeta

theorem openMeta_of (mo : Option OsMeta) : openMeta mo true = some (openMetaOf mo) := by
  cases mo <;> rfl

theorem fst_clean (F : List w8) : (F.map (·, true)).map Prod.fst = F := by
  rw [List.map_map]; exact List.map_id _

theorem clean_of (xs : List (w8 × Bool)) (h : ∀ x ∈ xs, x.2 = true) :
    xs = (xs.map Prod.fst).map (·, true) := by
  rw [List.map_map]
  conv => lhs; rw [← List.map_id xs]
  apply List.map_congr_left
  intro x hx; simp only [id, Function.comp_def]; rw [← h x hx]

/-- `Open`'s precondition, as the file to open and what it will be once open. -/
theorem dbFile_norm (p : GoString) (t : Nat) (vo : Option w64) :
    dbFile (GF := GF) p t vo ⊢
      |==> ∃ mo, osMeta (GF := GF) p (DFrac.own 1) mo ∗ openSt (GF := GF) p t vo (openMetaOf mo) := by
  unfold dbFile dbFresh dbStored openSt openMetaOf
  iintro (⟨%mo, %xs, Hm, Hb, %H⟩ | ⟨%m, Hm, Hs⟩)
  · obtain ⟨hnone, hsome, htx⟩ := H
    rcases mo with _ | m
    · have := hnone rfl; subst this
      imodintro
      iexists none; iframe Hm
      ileft
      isplitr
      · ipureintro; simp only [freshTx, List.length_nil] at htx
        rw [if_neg (by omega)] at htx; cases htx; exact ⟨rfl, rfl⟩
      unfold initAt
      iexists []
      isplitl
      · iapply (osBytes_nil p 0 _).2; iempintro
      · ipureintro; refine ⟨rfl, rfl, rfl, by decide, Or.inl (by decide)⟩
    · obtain ⟨hl, hmaps, hok, hsz, hfok⟩ := hsome m rfl
      dsimp only
      by_cases hc : 4 * 4096 ≤ xs.length ∧ (metaValid (fileMeta ((xs.map Prod.fst).take 8192) 0) ∨
          metaValid (fileMeta ((xs.map Prod.fst).take 8192) 1))
      · simp only [freshTx] at htx
        rw [if_pos hc] at htx
        cases htx
        rcases hfok with hshort | ⟨hclean, hno | ⟨hmp, hpg⟩⟩
        · omega
        · exfalso; rcases hc.2 with h | h
          · exact hno.1 h
          · exact hno.2 h
        obtain ⟨F, rfl⟩ : ∃ F : List w8, xs = F.map (·, true) := ⟨_, clean_of xs hclean⟩
        rw [fst_clean] at hmp hpg ⊢
        rw [List.length_map] at hl hpg hc
        imod stored_of_bytes p m F hl hmp (by rw [← hl]; exact hpg) hok hmaps (by omega) (by omega)
          $$ Hb with Hs
        imodintro
        iexists some m; iframe Hm
        iright; iexact Hs
      · simp only [freshTx] at htx
        rw [if_neg hc] at htx
        cases htx
        imodintro
        iexists some m; iframe Hm
        ileft
        isplitr
        · ipureintro; exact ⟨rfl, rfl⟩
        unfold initAt
        iexists xs; iframe Hb
        ipureintro
        refine ⟨hl, hmaps, hok, hsz, ?_⟩
        by_cases h16 : m.size < 4 * 4096
        · exact Or.inl h16
        · right
          have : ¬ (metaValid (fileMeta ((xs.map Prod.fst).take 8192) 0) ∨
              metaValid (fileMeta ((xs.map Prod.fst).take 8192) 1)) := fun h => hc ⟨by omega, h⟩
          exact ⟨fun h => this (Or.inl h), fun h => this (Or.inr h)⟩
  · imodintro
    iexists some m; iframe Hm
    iright; iexact Hs

/-- The file `init` laid out, as a stored database at transaction 1 with no value. -/
theorem stored_of_init (p : GoString) (m : OsMeta) (xs : List (w8 × Bool)) (hl : xs.length = m.size)
    (hok : m.ok = true) (hmaps : m.maps = ∅) (hsz : m.size ≤ 2 ^ 30) :
    osBytes (GF := GF) p 0 (DFrac.own 1) (initFile xs) ⊢
      |==> dbStoredAt (GF := GF) p 1 none
        { m with size := max m.size 16384, lo := max m.size 16384, hi := max m.size 16384 } := by
  iintro Hb
  rw [initFile_clean xs]
  have ht : (((initFile xs).map Prod.fst).take 8192).take 8192 = initBytes.take 8192 := by
    rw [List.take_take, Nat.min_self]; exact initFile_take xs
  have hl' : ((initFile xs).map Prod.fst).length = max m.size 16384 := by
    rw [List.length_map, initFile_length, hl]
  have hmp := metaPagesOk_init _ ht (by rw [List.length_take, hl']; omega)
  have hc := curMeta_init _ ht
  have hpg : curPgid (((initFile xs).map Prod.fst).take 8192) = 4 := by
    unfold curPgid; rw [hc, initMeta_pgid]; rfl
  have hrt : curRoot (((initFile xs).map Prod.fst).take 8192) = 3 := by
    unfold curRoot; rw [hc, initMeta_root]; rfl
  have htx : (curMeta (((initFile xs).map Prod.fst).take 8192)).txid'.toNat = 1 := by
    rw [hc, initMeta_txid]; rfl
  have Hst := stored_of_bytes (GF := GF) p
    { m with size := max m.size 16384, lo := max m.size 16384, hi := max m.size 16384 }
    ((initFile xs).map Prod.fst) hl' hmp
    (by rw [hpg]; simp only; omega) hok hmaps (by simp only; omega) (by simp only; omega)
  imod Hst $$ Hb with Hs
  rw [htx, hrt, initFile_root]
  iexact Hs

end lemmas

end bboltfs
end EtcdGrove
end Perennial
