/- Lean-first (no Rocq counterpart). The proof of `Open`'s crash-aware spec (`OpenCrash.lean` in
`Spec`): as `Open.lean`'s, over the crash invariant. The file `OpenFile` opens is the generation's
(`openStart`: all bytes clean and durable, a `Good` image); `Stat` and `readPageSize` read it
through the client's halves (`csOwn_idle00`); a file with no valid meta (`noValid`) is laid out by
`DB.init.specCrash`, a committed one (`committedImg`) is used as it is; either way the file is then
one a commit may start from (`openReady`), whose committed pages `cs_freeze` makes discarded
(`ready_pages`), and `DB.mmap.specCrash` maps it. -/
module

public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.OpenCrash
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__mmapCrash
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.flock
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__close
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__readPageSize
public import LinuxFs.Spec.os.OpenFile
public import LinuxFs.Spec.os.File__Name
public import LinuxFs.Spec.os.File__Close
public import LinuxFs.Spec.os.File__Stat
public import LinuxFs.Spec.os.fileStat__Size
public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.OpenLemmas
public import LinuxFs.Proof.os.CrashStSpec

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs
open Fs

section pure
variable [GooseExts]

/-- No meta slot held whole is valid: `Open` lays the file out with `init`. -/
def noValid (F : List w8) : Prop :=
  ∀ i < 2, 4096 * i + 80 ≤ F.length → ¬ metaValid (fileMeta F i)

/-- `goodImg`'s committed case. -/
def committedImg (F : List w8) : Prop :=
  4 * 4096 ≤ F.length ∧ metaPagesOk (imgMetas F) ∧ 4096 * curPgid (imgMetas F) ≤ F.length ∧
    bootOk (curMeta (imgMetas F)).txid'.toNat
      (pageVal ((F.drop (4096 * curRoot (imgMetas F))).take 4096)) ∧
    curInSlot (imgMetas F) ∧ txOk (imgMetas F)

theorem goodImg_cases {F : List w8} (h : goodImg F) : noValid F ∨ committedImg F := by
  obtain ⟨-, h | ⟨h4, h0, h1⟩ | h⟩ := h
  · exact Or.inl h.2
  · refine Or.inl fun i hi hl hv => ?_
    simp only [imgMetas] at h0 h1
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact h0 (by rw [fileMeta_take _ _ _ (by omega)]; exact hv)
    · exact h1 (by rw [fileMeta_take _ _ _ (by omega)]; exact hv)
  · exact Or.inr h

theorem fst_clean' (F : List w8) : (F.map durB).map Prod.fst = F := by
  rw [List.map_map]; exact List.map_id _

theorem clean_of' (xs : List ByteG) (h : ∀ x ∈ xs, x = durB x.1) :
    xs = (xs.map Prod.fst).map durB := by
  rw [List.map_map]
  conv => lhs; rw [← List.map_id xs]
  refine List.map_congr_left fun x hx => ?_
  exact h x hx

theorem clean_get (F : List w8) (k : Nat) (hk : k < F.length) :
    ∃ b, (F.map durB)[k]? = some (durB b) :=
  ⟨F[k], by rw [List.getElem?_map, List.getElem?_eq_getElem hk]; rfl⟩

/-- The file `Open` opened, of `OsMeta` `m` and bytes `F`, all clean and durable, a good image;
if `init` must lay it out, its meta slots (past the size included) are known, and invalid. -/
structure openStart (m : OsMeta) (F : List w8) : Prop where
  len : F.length = m.size
  maps : m.maps = ∅
  lo : m.lo = m.size
  hi : m.hi = m.size
  slots : noValid F → ∀ j < 2, ∃ X : List w8, X.length = 64 ∧ ¬ metaValid (decode X : Meta) ∧
    ∀ k < 64, (⟨m, F.map durB, 0, 0, .idle⟩ : CSt).kc (4096 * j + 16 + k) = some [(X.getD k 0, 0)]
  good : goodImg F

/-- What the client knows of a file as on disk: each byte's one candidate, its value. -/
theorem kc_start (img : Nat → w8) (sz b : Nat) :
    (⟨initMeta (OsFile.ofDisk img sz), (OsFile.ofDisk img sz).contents.map durB, 0, 0, .idle⟩ :
      CSt).kc b = some [((OsFile.ofDisk img sz).cache b, 0)] := by
  show CSt.baseC ⟨initMeta (OsFile.ofDisk img sz), _, 0, 0, .idle⟩ b = _
  have hs : (initMeta (OsFile.ofDisk img sz)).size = sz := rfl
  have hf : (OsFile.ofDisk img sz).size = sz := rfl
  unfold CSt.baseC; dsimp only; rw [hs]
  by_cases hb : b < sz
  · rw [if_pos hb, List.getElem?_map, contents_getElem?, hf, if_pos hb]; rfl
  · rw [if_neg hb]
    unfold OsMeta.pc
    rw [show (initMeta (OsFile.ofDisk img sz)).tc = tailMap (OsFile.ofDisk img sz) from rfl,
      tailMap_lookup, hf]
    by_cases h2 : sz ≤ b ∧ b < pageEnd sz
    · rw [if_pos h2]; rfl
    · rw [if_neg h2]
      show (if pageEnd sz ≤ b then some [((0 : w8), 0)] else none) = _
      have h3 : pageEnd sz ≤ b := by omega
      rw [if_pos h3, show (OsFile.ofDisk img sz).cache b = 0 from diskByte_past h3]

theorem openStart_disk (img : Nat → w8) (sz : Nat) (hg : Good (some (OsFile.ofDisk img sz))) :
    openStart (initMeta (OsFile.ofDisk img sz)) (OsFile.ofDisk img sz).contents := by
  have hsz : (OsFile.ofDisk img sz).size = sz := rfl
  refine ⟨by rw [contents_length]; rfl, rfl, rfl, rfl, fun hn j hj => ?_, hg.1⟩
  refine ⟨rawSlot (OsFile.ofDisk img sz) j, by simp [rawSlot], ?_, fun k hk => ?_⟩
  · by_cases hin : 4096 * j < sz
    · by_cases h16 : sz < 4 * 4096
      · exact hg.2.1 h16 j hj hin
      · have h80 : 4096 * j + 80 ≤ (OsFile.ofDisk img sz).size := by rw [hsz]; omega
        have := hn j hj (by rw [contents_length]; exact h80)
        rw [fileMeta_contents h80] at this
        exact this
    · have e : rawSlot (OsFile.ofDisk img sz) j = List.replicate 64 0 := by
        apply List.ext_getElem?; intro k
        simp only [rawSlot, List.getElem?_map, List.getElem?_range', List.getElem?_replicate]
        by_cases hk : k < 64
        · rw [List.getElem?_range hk, if_pos hk]
          show some (diskByte img sz _) = _
          rw [diskByte_past (by unfold pageEnd; omega)]
        · rw [List.getElem?_eq_none (by simp; omega), if_neg hk]; rfl
      rw [e]; exact zeroSlot_invalid
  · rw [kc_start]
    simp [rawSlot, List.getD_eq_getElem?_getD, List.getElem?_range hk]

theorem openStart_new : openStart newMeta [] :=
  openStart_disk (fun b => ([] : List w8).getD b 0) 0
    ⟨⟨by rw [contents_length]; exact Nat.zero_le _, .inl ⟨by rw [contents_length]; show 0 < 16384; decide,
      fun i _ h => by rw [contents_length] at h; have : 4096 * i + 80 ≤ 0 := h; omega⟩⟩,
      fun _ j _ hj => absurd hj (Nat.not_lt_zero _), _, _, rfl⟩

theorem startSt_open {j : Ino} {b : GoString} {V : Hist} {i : Ino} {s : CState}
    (hs : StartSt s) (hi : s = none ∨ sIno s = some i) :
    ∃ m0, (csOpenSt j b V i s).1 = some (i, ⟨m0, (startImg s).map durB, 0, 0, .idle⟩) ∧
      openStart m0 (startImg s) := by
  rcases hs with rfl | ⟨i', vs, sz, rfl, hg⟩
  · exact ⟨newMeta, rfl, openStart_new⟩
  · rcases hi with h | h
    · cases h
    · simp only [csStart, sIno, Option.some.injEq] at h; subst h
      refine ⟨initMeta (OsFile.ofDisk vs sz), ?_, ?_⟩
      · simp only [csOpenSt, csStart, startImg, fst_clean']
      · simp only [startImg, csStart, fst_clean']
        exact openStart_disk vs sz hg

theorem start_initIdle {m : OsMeta} {F : List w8} (hs : openStart m F) (hn : noValid F) :
    initIdle m (F.map durB) := by
  have hg := hs.good.1
  exact ⟨by rw [List.length_map, hs.len], by rw [hs.hi, ← hs.len]; exact hg, hs.slots hn⟩

theorem start_commitClean {m : OsMeta} {F : List w8} (hs : openStart m F) (hc : committedImg F) :
    commitClean m (F.map durB) := by
  obtain ⟨h4, hmp, hpg, hboot, hslot, htx⟩ := hc
  have hg := hs.good.1
  have hr1 := hmp.2.2.1
  have hr2 := hmp.2.2.2.1
  simp only [imgMetas] at hmp hpg hboot hslot hr1 hr2 htx
  have e := fst_clean' F
  refine ⟨by rw [hs.hi, ← hs.len]; exact hg, by rw [hs.lo, ← hs.len]; exact h4, by rw [e]; exact hmp,
    by rw [e]; exact hslot, by rw [e, hs.lo, ← hs.len]; exact hpg, by rw [e]; exact hboot,
    fun k hk => clean_get F k (by omega), fun k hk => ?_, by rw [e]; exact htx, fun k _ hk => ?_⟩
  · rw [e]
    have : 4096 * (curRoot (F.take 8192) + 1) ≤ 4096 * curPgid (F.take 8192) :=
      Nat.mul_le_mul_left _ hr2
    exact clean_get F _ (by omega)
  · rw [e] at hk
    exact clean_get F k (by omega)

/-- The starting state is `dbOk`: `init`'s idle state, or a commit's. -/
theorem start_okS {i : Ino} {m : OsMeta} {F : List w8} (hs : openStart m F) :
    dbOk (some (i, ⟨m, F.map durB, 0, 0, .idle⟩)) := by
  have hl : (F.map durB).length = m.size := by rw [List.length_map, hs.len]
  have hwf : (⟨m, F.map durB, 0, 0, .idle⟩ : CSt).Wf := ⟨hl, Nat.le_refl _, Nat.zero_le _, trivial⟩
  have hsz : m.size ≤ 2 ^ 30 := by rw [← hs.len]; exact hs.good.1
  rcases goodImg_cases hs.good with hn | hc
  · have h0 := start_initIdle hs hn
    have hz : ∀ k < 8192, (List.replicate 16384 (0 : w8)).getD k 0 = 0 := fun k _ => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
    exact noValid_okS _ hwf trivial (by show m.hi ≤ 2 ^ 30; rw [hs.hi]; exact hsz)
      fun j hj => let ⟨X, hXl, hXv, hX⟩ := h0.slots j hj; ⟨X, X, ⟨hXl, hXl, .inl hX⟩, hXv, hXv⟩
  · exact commitClean_okS ⟨m, F.map durB, 0, 0, .idle⟩ hwf trivial (start_commitClean hs hc)
      (Nat.le_refl _) (by show m.hi ≤ 2 ^ 30; rw [hs.hi]; exact hsz) (fun _ _ => trivial)

theorem freshTx_noValid {F : List w8} (hn : noValid F) : freshTx (F.map durB) = (1, none, 4) := by
  unfold freshTx
  simp only [fst_clean', List.length_map]
  rw [if_neg]
  rintro ⟨h4, h0 | h1⟩
  · exact hn 0 (by omega) (by omega) (by rw [fileMeta_take _ _ _ (by omega)] at h0; exact h0)
  · exact hn 1 (by omega) (by omega) (by rw [fileMeta_take _ _ _ (by omega)] at h1; exact h1)

theorem freshTx_committed {F : List w8} (hc : committedImg F) :
    freshTx (F.map durB) = ((curMeta (F.take 8192)).txid'.toNat,
      pageVal ((F.drop (4096 * curRoot (F.take 8192))).take 4096), curPgid (F.take 8192)) := by
  unfold freshTx
  simp only [fst_clean', List.length_map]
  rw [if_pos ⟨hc.1, hc.2.1.2.1⟩]

theorem take_fst_clean (F : List w8) (k : Nat) :
    ((F.map durB).take k).map Prod.fst = F.take k := by
  rw [List.map_take, fst_clean']

/-- `readPageSize` found no valid meta. -/
theorem noValid_of_rps {F : List w8} (hg : goodImg F)
    (h : ∀ i < 2, ¬ metaValid (fileMeta (F.take 8192) i)) : noValid F := by
  rcases goodImg_cases hg with hn | hc
  · exact hn
  · exfalso
    rcases hc.2.1.2.1 with h0 | h1
    · exact h 0 (by omega) h0
    · exact h 1 (by omega) h1

/-- `readPageSize` found a valid meta. -/
theorem committed_of_rps {F : List w8} (hg : goodImg F) (h16 : 4 * 4096 ≤ F.length)
    (h : ∃ i < 2, metaValid (fileMeta (F.take 8192) i)) : committedImg F := by
  rcases goodImg_cases hg with hn | hc
  · exfalso
    obtain ⟨i, hi, hv⟩ := h
    exact hn i hi (by omega) (by rw [fileMeta_take _ _ _ (by omega)] at hv; exact hv)
  · exact hc

/-- A file shorter than four pages has no valid meta. -/
theorem noValid_of_short {F : List w8} (hg : goodImg F) (h : F.length < 4 * 4096) : noValid F := by
  rcases goodImg_cases hg with hn | hc
  · exact hn
  · exact absurd hc.1 (by omega)

/-- The file after `Open`'s `init` step: one a commit may start from, all clean, at transaction
`t` holding `vo`, high water mark `n`. -/
structure openReady (m : OsMeta) (bs : List ByteG) (t : Nat) (vo : Option w64) (n : Nat) :
    Prop where
  cc : commitClean m bs
  len : bs.length = m.size
  clean : ∀ x ∈ bs, x = durB x.1
  ok : True
  maps : m.maps = ∅
  lo : m.lo = m.size
  h16 : 4 * 4096 ≤ m.size
  h30 : m.size ≤ 2 ^ 30
  tx : (curMeta ((bs.map Prod.fst).take 8192)).txid'.toNat = t
  vo : pageVal (pageOf (bs.map Prod.fst) (curRoot ((bs.map Prod.fst).take 8192))) = vo
  pg : curPgid ((bs.map Prod.fst).take 8192) = n

theorem ready_committed {m : OsMeta} {F : List w8} {t : Nat} {vo : Option w64} {n : Nat}
    (hs : openStart m F) (hc : committedImg F) (hf : freshTx (F.map durB) = (t, vo, n)) :
    openReady m (F.map durB) t vo n := by
  rw [freshTx_committed hc] at hf
  simp only [Prod.mk.injEq] at hf
  obtain ⟨ht, hv, hn⟩ := hf
  refine ⟨start_commitClean hs hc, by rw [List.length_map, hs.len], ?_, trivial, hs.maps, hs.lo,
    by rw [← hs.len]; exact hc.1, by rw [← hs.len]; exact hs.good.1, ?_, ?_, ?_⟩
  · intro x hx; simp only [List.mem_map] at hx; obtain ⟨_, _, rfl⟩ := hx; rfl
  all_goals rw [fst_clean']
  · exact ht
  · exact hv
  · exact hn

theorem ready_init {m : OsMeta} {F : List w8} {t : Nat} {vo : Option w64} {n : Nat}
    (hs : openStart m F) (hn : noValid F)
    (hf : freshTx (F.map durB) = (t, vo, n)) :
    openReady (initDoneMeta m) (initFile (F.map durB)) t vo n := by
  rw [freshTx_noValid hn] at hf
  simp only [Prod.mk.injEq] at hf
  obtain ⟨rfl, rfl, rfl⟩ := hf
  have hsz : m.size ≤ 2 ^ 30 := by rw [← hs.len]; exact hs.good.1
  have hl : (F.map durB).length = m.size := by rw [List.length_map, hs.len]
  generalize F.map durB = xs at hl
  have hc := curMeta_init _ (by rw [List.take_take, Nat.min_self])
  refine ⟨init_commitClean hsz, ?_, ?_, trivial, hs.maps, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [initFile_length, hl]; rfl
  · intro x hx; rw [initFile_clean xs] at hx; simp only [List.mem_map] at hx
    obtain ⟨_, _, rfl⟩ := hx; rfl
  · show 4 * 4096 ≤ max m.size 16384; omega
  · show max m.size 16384 ≤ 2 ^ 30; omega
  · rw [initFile_take, hc, initMeta_txid]; rfl
  · rw [show curRoot (((initFile xs).map Prod.fst).take 8192) = 3 by
      unfold curRoot; rw [initFile_take, hc, initMeta_root]; rfl, initFile_root]
  · unfold curPgid; rw [initFile_take, hc, initMeta_pgid]; rfl

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Assumptions]

/-- An idle state with nothing frozen: the client's halves of its `OsMeta` and bytes. -/
theorem csOwn_idle00 (p : Ino) (γ : GName) (m : OsMeta) (bs : List ByteG) :
    csOwnF (GF := GF) γ (some (p, ⟨m, bs, 0, 0, .idle⟩)) ⊣⊢
      ghostVar γ (1 : Qp).half (some (p, ⟨m, bs, 0, 0, .idle⟩) : CState) ∗
      osMeta (GF := GF) p (DFrac.own (1 : Qp).half) m ∗
      osBytes (GF := GF) p 0 (DFrac.own (1 : Qp).half) bs ∗ ⌜bs.length = m.size⌝ := by
  have h := idle_thrBytes (GF := GF) p m [] [] bs 0 0 rfl rfl
  rw [List.nil_append, List.nil_append] at h
  constructor
  · iintro H
    icases (csOwnF_idle _ _ _ rfl).1 $$ H with ⟨Hv, ⟨Hm, Hb⟩, %Hwf⟩
    icases h.1 $$ Hb with ⟨-, Hb⟩
    iframe
    ipureintro; exact Hwf.1
  · iintro ⟨Hv, Hm, Hb, %Hl⟩
    iapply (csOwnF_idle _ _ _ rfl).2
    iframe Hv Hm
    isplitl
    · iapply h.2
      iframe
      iapply (osBytes_nil' _ _ _).2
      iempintro
    · ipureintro; exact ⟨Hl, Nat.le_refl _, Nat.zero_le _, trivial⟩

/-- The committed pages of a clean file, frozen (`cs_freeze`), as pages. -/
theorem ready_pages (p : Ino) (bs : List ByteG) (n : Nat)
    (hcl : ∀ x ∈ bs, x = durB x.1) (h : 4096 * n ≤ bs.length) (h2 : 2 ≤ n) :
    osBytes (GF := GF) p 8192 DFrac.discard ((bs.drop 8192).take (4096 * n - 8192)) ⊢
      |==> [∗list] r ∈ List.range' 2 (n - 2), pageIs (GF := GF) p r (pageOf (bs.map Prod.fst) r) := by
  obtain ⟨G, rfl⟩ : ∃ G : List w8, bs = G.map durB := ⟨_, clean_of' bs hcl⟩
  rw [fst_clean', ← List.map_drop, ← List.map_take, show 8192 = 4096 * 2 by rfl,
    show 4096 * n - 4096 * 2 = 4096 * (n - 2) by omega]
  rw [List.length_map] at h
  exact pages_of_bytes p DFrac.discard G (n - 2) 2 (by omega)

/-- `open_ghost` with `metalock`'s resource over the crash invariant (`metaRC`): no meta bytes. -/
theorem open_ghostC (db : Loc) (p : GoString) (i : Ino) (mp : List w8) (B : List w8)
    (t : Nat) (vo : Option w64) (vp : Nat → Option w64 → Prop) (hvp : vp t vo)
    (hmp : metaPagesOk mp) (ht : (curMeta mp).txid'.toNat = t) (hvo : pageVal B = vo) :
    db.[DB, go!"failed"] ↦ false ∗ pageIs (GF := GF) i (curRoot mp) B ⊢
      |==> ∃ γ : DBNames, ⌜γ.vp = vp ∧ γ.ino = i⌝ ∗ metaRC (GF := GF) γ db p ∗
        ghostVar γ.cur (1 : Qp).half.half (mp, false, curPgid mp) ∗
        ghostVar γ.cur (1 : Qp).half.half (mp, false, curPgid mp) ∗
        ghostVar γ.map (1 : Qp).half (none : MapSt) ∗ ghostVar γ.map (1 : Qp).half (none : MapSt) ∗
        ghostVar γ.out (1 : Qp).half.half false ∗ ghostVar γ.out (1 : Qp).half false ∗
        ghostVar γ.cls (1 : Qp).half false ∗ dbOwner (GF := GF) γ t (curPgid mp) ∗
        dbLast (GF := GF) γ t ∗ dbTx (GF := GF) γ t vo := by
  iintro ⟨Hfl, #HB⟩
  imod ghostVar_alloc (GF := GF) (mp, false, curPgid mp) with ⟨%γcur, Hcur⟩
  imod ghostVar_alloc (GF := GF) (none : MapSt) with ⟨%γmap, Hmap⟩
  imod ghostVar_alloc (GF := GF) false with ⟨%γout, Hout⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Option w64) with ⟨%γtxs, Htxs⟩
  imod ghost_map_insert (V := Option w64) t vo (by rfl) $$ Htxs with ⟨Htxs, Htx⟩
  imod ghostMapElem_persist t γtxs _ vo $$ Htx with #Htx
  imod mono_nat_own_alloc (GF := GF) t with ⟨%γlast, Hlast, #Hlb⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γfail, Hfail, -⟩
  imod ghostVar_alloc (GF := GF) (t, curPgid mp) with ⟨%γown, Hown⟩
  imod ghostVar_alloc (GF := GF) false with ⟨%γcls, Hcls⟩
  imodintro
  iexists ⟨i, γcur, γmap, γout, γtxs, γlast, γfail, γown, γcls, vp⟩
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  icases (ghostVar_split_half γcur 1 _).1 $$ Hcur with ⟨Hcur, Hc2⟩
  icases (ghostVar_split_half γcur (1 : Qp).half _).1 $$ Hc2 with ⟨Hc3, Hc4⟩
  icases (ghostVar_split_half γmap 1 _).1 $$ Hmap with ⟨Hmap1, Hmap2⟩
  icases (ghostVar_split_half γout 1 _).1 $$ Hout with ⟨Hout1, Ho2⟩
  icases (ghostVar_split_half γout (1 : Qp).half _).1 $$ Ho2 with ⟨Hout2, Hout3⟩
  icases (ghostVar_split_half γown 1 _).1 $$ Hown with ⟨Hown1, Hown2⟩
  icases (ghostVar_split_half γcls 1 _).1 $$ Hcls with ⟨Hcls1, Hcls2⟩
  dsimp only
  unfold dbOwner dbLast dbTx
  dsimp only
  iframe Hc3 Hc4 Hmap1 Hmap2 Hout1 Hout2 Hcls1 Hown1 Hlb Htx
  isplitl
  rotate_left
  · ipureintro; exact hvp
  unfold metaRC
  iexists false, mp, curPgid mp, false, (∅ : GMap Nat (Option w64)).insert t vo
  dsimp only
  rw [← ht, ← hvo]
  iframe Hfl Hcur Hcls2 Hout3 Htxs Hfail Hlast Hown2
  isplitr
  · ipureintro
    refine ⟨hmp, rfl, fun k hk => ?_⟩
    rw [GMap.lookup_insert_ne _ _ (by omega)]; rfl
  iexists B
  unfold dbTx
  dsimp only
  iframe HB Htx
  ipureintro
  exact ⟨by rw [ht, hvo]; exact hvp, GMap.lookup_insert _ _ _⟩

set_option maxRecDepth 20000 in
theorem Open.wp_proof_crash (wp_OpenFile : os.OpenFile.specCrashS (GF := GF) (hG := hG))
    (wp_Name : os.File.Name.spec (GF := GF) (hG := hG))
    (wp_flock : flock.spec (GF := GF) (hG := hG))
    (wp_Stat : os.File.Stat.spec (GF := GF) (hG := hG))
    (wp_Size : os.fileStat.Size.spec (GF := GF) (hG := hG))
    (wp_FClose : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_close : DB.close.spec (GF := GF) (hG := hG))
    (wp_readPageSize : DB.readPageSize.spec (GF := GF) (hG := hG))
    (wp_init : DB.init.specCrash (GF := GF) (hG := hG))
    (wp_mmap : DB.mmap.specCrash (GF := GF) (hG := hG)) :
    Open.specCrash (GF := GF) (hG := hG) := by
  intro _ d b R V j γc s0 t vo n vp hb hd hs0 hfresh hvp hvpb
  wp_start as ⟨#Hpkg, #Hos, #Hci, Hown⟩
  ihave ⟨%e2, #He2, %He2⟩ := pkgFacts_errPageSize $$ Hpkg
  (try wp_auto)
  irename «$r0» => Hdb
  generalize «$r0_ptr» = db at *
  iStructNamed Hdb
  rw [show (W64 2 ||| W64 64 : w64) = W64 0x42 from rfl]
  have hshape : s0 = none ∨ ∃ i m bs fa fb, s0 = some (i, ⟨m, bs, fa, fb, .idle⟩) := by
    rcases hs0 with rfl | ⟨i, vs, sz, rfl, -⟩
    · exact .inl rfl
    · exact .inr ⟨_, _, _, _, _, rfl⟩
  wp_apply wp_OpenFile d b (W32 438) dbCrashN R V j γc Good dbOk s0 hb hd hshape dbCrashN_disj
      (fun _ i => start_okS (i := i) openStart_new) $$ [Hown]
    as %f %err (⟨%fd, %i, %Hfd, Hf, Hfdo, Hown⟩ | ⟨%Herr, Hown⟩)
  · iframe; iframe #
  rotate_left
  · obtain ⟨Herr, rfl⟩ := Herr
    cases err with
    | nil => exact absurd rfl Herr
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact ⟨by simp, rfl⟩
    · icases Hown with (Hown | ⟨%i, Hown⟩)
      · iunfold csOwn at Hown
        icases Hown with ⟨Hown, -, -⟩
        iexists _; iexact Hown
      · iunfold csOwn at Hown
        icases Hown with ⟨Hown, -, -⟩
        iexists _; iexact Hown
  obtain ⟨rfl, Hfd, hi⟩ := Hfd
  obtain ⟨m0, heq, hs⟩ := startSt_open (j := j) (b := b) (V := V) hs0 hi
  iunfold csOwn at Hown
  icases Hown with ⟨Hown, -, -⟩
  rw [heq]
  generalize startImg s0 = F at hs hfresh ⊢
  generalize hpath : child d b = path at *
  have hsz30 : m0.size ≤ 2 ^ 30 := by rw [← hs.len]; exact hs.good.1
  (try wp_auto)
  wp_apply wp_Name f fd path (DFrac.own 1) $$ [Hf] as Hf
  · iexact Hf
  (try wp_auto)
  wp_apply wp_flock f fd path (DFrac.own 1) (DFrac.own 1) _ true $$ [Hf Hfdo] as %err1 ⟨Hf, Hfdo⟩
  · iframe; iframe #
  cases err1 with
  | ok ie =>
    (try wp_auto)
    wp_apply wp_FClose f fd path _ $$ [Hf Hfdo] as %e ⟨Hf, -⟩
    · iframe; iframe #
    (try wp_auto)
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact ⟨by simp, rfl⟩
    · iexists _; iexact Hown
  | nil =>
  (try wp_auto)
  icases (csOwn_idle00 i γc m0 (F.map durB)).1 $$ Hown with ⟨Hv, Hm, Hb, %Hl⟩
  wp_apply wp_Stat f fd path (DFrac.own 1) (DFrac.own 1) (DFrac.own (1 : Qp).half) _ m0
      $$ [Hf Hfdo Hm] as %fi %err2 ⟨Hf, Hfdo, Hm, Hfi, #_, -⟩
  · iframe; iframe #; iexact Hm
  ihave Hown := (csOwn_idle00 i γc m0 (F.map durB)).2 $$ [Hv Hm Hb]
  · iframe; ipureintro; exact Hl
  icases Hfi with (⟨%fs, %Hfi, Hfs⟩ | %Hfi)
  rotate_left
  · obtain ⟨Herr2, rfl⟩ := Hfi
    cases err2 with
    | nil => exact absurd rfl Herr2
    | ok ie =>
    (try wp_auto)
    wp_apply wp_close db (DFrac.own 1) slice.nil (W64 0) null null f (DFrac.own 1) fd path _ i m0
        (fun h => absurd rfl h) $$ [dataref datasz meta0 meta1 file Hf Hfdo]
      as %_errc ⟨-, -, -, -, -, file, Hf⟩
    · iframe; iframe #; unfold mappingRes; ileft; ipureintro; rfl
    (try wp_auto)
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact ⟨by simp, rfl⟩
    · iexists _; iexact Hown
  obtain ⟨rfl, rfl⟩ := Hfi
  (try wp_auto)
  wp_apply wp_Size fs (W64 m0.size) $$ [Hfs] as -
  · iexact Hfs
  imod (update_into_persistently (P := typedPointsto (GF := GF) db.[DB, go!"file"] f (DFrac.own 1)))
    $$ file with #file
  imod (update_into_persistently (P := typedPointsto (GF := GF) db.[DB, go!"path"] path (DFrac.own 1)))
    $$ path with #Hpath
  have hsZ : sint.Z (W64 (m0.size : Int)) = m0.size := by
    show BitVec.toInt _ = _
    rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_ofInt]; split <;> omega
  (try wp_auto)
  rw [hsZ, show sint.Z (W64 16384) = 16384 from rfl]
  -- a committed file has a valid meta; any other file is for `init`
  wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∗ ∃ b : Bool, valid_ptr ↦ b ∗
      ⌜(b = true → committedImg F) ∧ (b = false → noValid F)⌝ ∗ db_ptr ↦ db ∗
      os.ownFile (GF := GF) f fd path (DFrac.own 1) ∗
      osFd (GF := GF) fd (DFrac.own 1) ⟨i, true, true⟩ ∗
      csOwnF (GF := GF) γc (some (i, ⟨m0, F.map durB, 0, 0, .idle⟩)) ∗
      db.[DB, go!"dataref"] ↦ (zero_val DB).dataref' ∗ db.[DB, go!"datasz"] ↦ (zero_val DB).datasz' ∗
      db.[DB, go!"meta0"] ↦ (zero_val DB).meta0' ∗ db.[DB, go!"meta1"] ↦ (zero_val DB).meta1' ∗
      «$res0_ptr» ↦ zero_val Loc ∗ «$res1_ptr» ↦ GoInterface.nil) ∨
    (∃ e : GoInterface, ⌜v = returnVal #() ∧ e ≠ interface.nil⌝ ∗ db_ptr ↦ db ∗
      «$res0_ptr» ↦ null ∗ «$res1_ptr» ↦ e ∗ ∃ s' : CState, csOwnF (GF := GF) γc s')))
    with [valid db Hf Hfdo Hown dataref datasz meta0 meta1 «$res0» «$res1»]
  · icases (csOwn_idle00 i γc m0 (F.map durB)).1 $$ Hown with ⟨Hv, Hm, Hb, %Hl⟩
    icases (osBytes_take_drop i _ (F.map durB) 8192 (by omega)).1 $$ Hb with ⟨HX, HXr⟩
    wp_apply wp_readPageSize db f DFrac.discard fd path (DFrac.own 1) (DFrac.own 1)
        (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half) ⟨i, true, true⟩ m0
        ((F.map durB).take 8192) rfl (by rw [List.length_take]; omega) (by omega)
        $$ [Hf Hfdo Hm HX]
      as %ps %ok %err3 ⟨-, Hf, Hfdo, Hm, HX, %Hrd⟩
    · iframe; iframe #
    ihave Hown := (csOwn_idle00 i γc m0 (F.map durB)).2 $$ [Hv Hm HX HXr]
    · iframe Hv Hm
      isplitl
      · iapply (osBytes_take_drop i _ (F.map durB) 8192 (by omega)).2; iframe
      · ipureintro; exact Hl
    rw [take_fst_clean] at Hrd
    have hF16 : 4 * 4096 ≤ F.length := by rw [hs.len]; omega
    cases err3 with
    | ok ie =>
      (try wp_auto)
      wp_apply wp_close db (DFrac.own 1) slice.nil (W64 0) null null f DFrac.discard fd path _ i m0
          (fun h => absurd rfl h) $$ [dataref datasz meta0 meta1 Hf Hfdo]
        as %_errc ⟨-, -, -, -, -, -, Hf⟩
      · iframe; iframe #; unfold mappingRes; ileft; ipureintro; rfl
      (try wp_auto)
      iright
      iexists GoInterface.ok ie
      isplitr
      · ipureintro; simp
      iframe
    | nil =>
    have Hrd := Hrd rfl
    (try wp_auto)
    cases ok with
    | false =>
      (try wp_auto)
      ileft
      isplitr
      · ipureintro; trivial
      iexists false
      iframe
      ipureintro
      exact ⟨(fun h => by cases h), fun _ => noValid_of_rps hs.good (Hrd.2 rfl)⟩
    | true =>
      by_cases hps : ps = W64 4096
      · subst hps
        (try wp_auto)
        ileft
        isplitr
        · ipureintro; trivial
        iexists true
        iframe
        ipureintro
        obtain ⟨i, hi, hv, -⟩ := Hrd.1 rfl
        exact ⟨fun _ => committed_of_rps hs.good hF16 ⟨i, hi, hv⟩, (fun h => by cases h)⟩
      · (try wp_auto)
        simp only [decide_eq_false hps, Bool.not_false]
        (try wp_auto)
        wp_apply wp_close db (DFrac.own 1) slice.nil (W64 0) null null f DFrac.discard fd path _ i m0
            (fun h => absurd rfl h) $$ [dataref datasz meta0 meta1 Hf Hfdo]
          as %_errc ⟨-, -, -, -, -, -, Hf⟩
        · iframe; iframe #; unfold mappingRes; ileft; ipureintro; rfl
        (try wp_auto)
        iright
        iexists e2
        isplitr
        · ipureintro; exact ⟨rfl, He2⟩
        iframe
  · ileft
    isplitr
    · ipureintro; trivial
    iexists false
    iframe
    ipureintro
    exact ⟨(fun h => by cases h), fun _ => noValid_of_short hs.good (by rw [hs.len]; omega)⟩
  iintro (⟨%Hv, %b, valid, %Hb, db, Hf, Hfdo, Hown, dataref, datasz, meta0, meta1, «$res0», «$res1»⟩ |
    ⟨%e, %Hv, db, «$res0», «$res1», %s', Hown⟩)
  rotate_left
  · obtain ⟨rfl, He⟩ := Hv
    (try wp_auto)
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact ⟨He, rfl⟩
    · iexists s'; iexact Hown
  subst Hv
  (try wp_auto)
  -- `init` when no meta is valid
  wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∗ ∃ (m' : OsMeta) (bs : List ByteG),
      db.[DB, go!"filesz"] ↦ W64 (m'.size : Int) ∗
      csOwnF (GF := GF) γc (some (i, ⟨m', bs, 0, 0, .idle⟩)) ∗ ⌜openReady m' bs t vo n⌝ ∗
      db_ptr ↦ db ∗ os.ownFile (GF := GF) f fd path (DFrac.own 1) ∗
      osFd (GF := GF) fd (DFrac.own 1) ⟨i, true, true⟩ ∗
      db.[DB, go!"dataref"] ↦ (zero_val DB).dataref' ∗ db.[DB, go!"datasz"] ↦ (zero_val DB).datasz' ∗
      db.[DB, go!"meta0"] ↦ (zero_val DB).meta0' ∗ db.[DB, go!"meta1"] ↦ (zero_val DB).meta1' ∗
      «$res0_ptr» ↦ zero_val Loc ∗ «$res1_ptr» ↦ GoInterface.nil) ∨
    (∃ e : GoInterface, ⌜v = returnVal #() ∧ e ≠ interface.nil⌝ ∗ db_ptr ↦ db ∗
      «$res0_ptr» ↦ null ∗ «$res1_ptr» ↦ e ∗ ∃ s' : CState, csOwnF (GF := GF) γc s')))
    at next with [filesz db Hf Hfdo Hown dataref datasz meta0 meta1 «$res0» «$res1»]
  · cases b with
    | true =>
      (try wp_auto)
      ileft
      isplitr
      · ipureintro; trivial
      iexists m0, F.map durB
      iframe
      ipureintro; exact ready_committed hs (Hb.1 rfl) hfresh
    | false =>
      have hn := Hb.2 rfl
      (try wp_auto)
      wp_apply wp_init db f fd path (DFrac.own 1) (DFrac.own 1) dbCrashN path R γc i m0 (F.map durB)
          hs.maps hsz30 (start_initIdle hs hn) dbCrashN_disj
          $$ [filesz Hf Hfdo Hown] as %err4 ⟨Hf, Hfdo, Hres⟩
      · iframe; iframe #
      icases Hres with (⟨%He, Hfsz, Hown⟩ | ⟨%He, %sz, %s', Hfsz, Hown⟩)
      · subst He
        (try wp_auto)
        ileft
        isplitr
        · ipureintro; trivial
        iexists initDoneMeta m0, initFile (F.map durB)
        rw [show (max (m0.size : Int) 16384) = ((max m0.size 16384 : Nat) : Int) by omega]
        iframe
        ipureintro; exact ready_init hs hn hfresh
      · cases err4 with
        | nil => exact absurd rfl He
        | ok ie =>
        (try wp_auto)
        wp_apply wp_close db (DFrac.own 1) slice.nil (W64 0) null null f DFrac.discard fd path _ i m0
            (fun h => absurd rfl h) $$ [dataref datasz meta0 meta1 Hf Hfdo]
          as %_errc ⟨-, -, -, -, -, -, Hf⟩
        · iframe; iframe #; unfold mappingRes; ileft; ipureintro; rfl
        (try wp_auto)
        iright
        iexists GoInterface.ok ie
        isplitr
        · ipureintro; simp
        iframe
  iintro (⟨%Hv, %m', %bs, filesz, Hown, %Hr, db, Hf, Hfdo, dataref, datasz, meta0, meta1, «$res0», «$res1»⟩ |
    ⟨%e, %Hv, db, «$res0», «$res1», %s', Hown⟩)
  rotate_left
  · obtain ⟨rfl, He⟩ := Hv
    (try wp_auto)
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact ⟨He, rfl⟩
    · iexists s'; iexact Hown
  subst Hv
  -- the committed pages, frozen
  have hmpok := Hr.cc.ok
  have hpg := Hr.cc.pg
  have hr1 := hmpok.2.2.1
  have hr2 := hmpok.2.2.2.1
  have hlo := Hr.lo
  have ht := Hr.tx
  have hvo := Hr.vo
  have hn := Hr.pg
  subst ht hvo hn
  generalize hmp : (bs.map Prod.fst).take 8192 = mp at *
  have hn2 : 2 ≤ curPgid mp := by omega
  have hnsz : 4096 * curPgid mp ≤ m'.size := by rw [← hlo]; exact hpg
  imod cs_freeze dbCrashN path R i γc Good dbOk m' bs 0 0 8192 (4096 * curPgid mp) ⊤
      (fun _ _ => CoPset.mem_full) (by omega) hnsz (fun h => absurd h (Nat.lt_irrefl 0))
      (commitClean_okS ⟨m', bs, 8192, 4096 * curPgid mp, .idle⟩ ⟨Hr.len, (Nat.mul_le_mul_left 4096 hn2 : 4096 * 2 ≤ _), hnsz, trivial⟩ trivial
        Hr.cc (Nat.le_refl _) Hr.cc.hi (fun _ _ => trivial)) $$ Hci Hown
    with ⟨Hown, Hfr⟩
  imod ready_pages i bs (curPgid mp) Hr.clean (by rw [Hr.len]; exact hnsz) hn2 $$ Hfr with #Hps
  ihave Hr0 := pages_acc (fun r => pageIs (GF := GF) i r (pageOf (bs.map Prod.fst) r)) (curRoot mp)
    (curPgid mp) hr1 hr2 $$ Hps
  icases Hr0 with ⟨#HB, -⟩
  imod open_ghostC db path i mp (pageOf (bs.map Prod.fst) (curRoot mp)) _ _ vp hvp hmpok rfl rfl
      $$ [failed HB]
    with ⟨%γ, %Hγ, HM, Hcur1, Hcur2, Hmap1, Hmap2, Hout1, Hout2, Hcls, Hownr, #Hlast, #Htx⟩
  · iframe; iframe #
  obtain ⟨Hγvp, hγi⟩ := Hγ
  subst hγi
  imod sync.init_Mutex (metaRC (GF := GF) γ db path) ⊤ db.[DB, go!"metalock"] $$ metalock [HM] with #Hmeta
  · inext; iexact HM
  icases (mapFields_join db none).2 $$ [dataref meta0 meta1] with ⟨Hflds1, Hflds2⟩
  · iframe
  imod sync.init_RWMutex (mapR (GF := GF) γ db f fd path) db.[DB, go!"mmaplock"] $$ [Hmap2 Hflds2] mmaplock
    with Hrs
  · inext; unfold mapR mapBody; iexists none; iframe; unfold mapRest; iempintro
  icases sync.ownRWMutex_slots_guard _ _ $$ Hrs with ⟨Hrs, #Hguard⟩
  icases (ownFile_halves f fd path).1 $$ Hf with ⟨Hf1, Hf2⟩
  icases (osFd_halves fd _).1 $$ Hfdo with ⟨Hfd1, Hfd2⟩
  (try wp_auto)
  wp_apply wp_mmap γ γc db f fd path R (W64 0) mp false (curPgid mp) none m' bs rfl (by decide) (by decide)
      $$ [Hcur1 Hmap1 Hout1 Hflds1 filesz datasz Hf1 Hfd1 Hown Hcur2 Hf2 Hfd2 Hout2]
    as %err5 ⟨%st', %m'', Hcur1, Hmap1, Hout1, Hflds1, Hw, %Hm'', Hres⟩
  · iframe #
    unfold writerFileC mmapPre writerExtra
    iframe
    isplitr
    · ipureintro
      exact ⟨hn2, hnsz, fun M => writer_okS 8192 _ Hr.len (Nat.mul_le_mul_left 4096 hn2 : 4096 * 2 ≤ _) hnsz Hr.cc M, fun _ => ⟨hmp, Hr.cc, rfl, Hfd, Hr.h16, Hr.h30,
        by simp only [mapLen]; omega⟩⟩
    dsimp only
    iframe
    isplitr
    · ipureintro; exact Hr.maps
    iapply pages_ex γ.ino _ (curPgid mp - 2) 2 $$ Hps
  icases Hres with (⟨%He5, %base, %len, %γm, %Hst', Htok, #Hinv, Hwc⟩ | ⟨%He5, Hx⟩)
  · subst He5
    obtain ⟨rfl, Hmaps'', Hlen, -, Hbase, Hl41⟩ := Hst'
    imod sync.init_Mutex (rwRC (GF := GF) γ γc db f fd path) ⊤ db.[DB, go!"rwlock"] $$ rwlock
        [Hcur1 Hmap1 Hout1 Hflds1 Hw Hcls Htok Hwc] with #Hrw
    · inext
      unfold rwRC
      ileft
      iexists mp, false, curPgid mp, some (base, len, γm), m'', bs
      iframe
      isplitr
      · ipureintro; intro _; trivial
      dsimp only
      iframe; iframe #
      ipureintro; exact ⟨Hmaps'', by omega, Hbase, Hl41⟩
    ihave Hrds := (BigSepL.bigSepL_impl (Ψ := fun _ _ => dbReader (GF := GF) γ db)) $$ Hrs []
    · imodintro
      iintro %_ %_ %_ Hr
      unfold dbReader; iexists f, fd, path; iframe; iframe #
    imod threadPool.init dbPoolN (dbReader (GF := GF) γ db) ⊤ _
        (sync.threadBound_le_actualMaxReaders (ThreadBoundLe.le (GF := GF) (2 ^ 30))) $$ Hrds with ⟨%γp, #Hpool⟩
    (try wp_auto)
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists γ
    isplitr
    · ipureintro; exact Hγvp
    iframe Hownr Hlast Htx
    isplitr
    · unfold isDBC
      isplitr
      · iexists f, fd, path; iframe #
      isplitr
      · ipureintro; rw [Hγvp]; exact hvpb
      · iexists γp; iframe #
    iframe Hpath
  · obtain ⟨Herr5, rfl⟩ := He5
    unfold writerExtra
    icases Hx with ⟨-, Hf2, Hfd2⟩
    iunfold writerFileC at Hw
    icases Hw with ⟨%fszw, Hfsz, Hdsz, Hf1, Hfd1, Hown, -⟩
    ihave Hf := (ownFile_halves f fd path).2 $$ [Hf1 Hf2]
    · iframe
    ihave Hfd := (osFd_halves fd _).2 $$ [Hfd1 Hfd2]
    · iframe
    unfold mapFields
    icases Hflds1 with ⟨Hd, H0, H1⟩
    icases (pointsto_halves _ _).1 $$ Hdsz with ⟨Hdsz, -⟩
    cases err5 with
    | nil => exact absurd rfl Herr5
    | ok ie =>
    (try wp_auto)
    wp_apply wp_close db (DFrac.own (1 : Qp).half) slice.nil (W64 0) null null f DFrac.discard fd path _ γ.ino
        m'' (fun h => absurd rfl h) $$ [Hd Hdsz H0 H1 Hf Hfd]
      as %_errc ⟨-, -, -, -, -, -, Hf⟩
    · iframe; iframe #; unfold mappingRes; ileft; ipureintro; rfl
    (try wp_auto)
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact ⟨by simp, rfl⟩
    · iexists _; iexact Hown

end proof

end osfs_bboltfs
end EtcdGrove
end Perennial
