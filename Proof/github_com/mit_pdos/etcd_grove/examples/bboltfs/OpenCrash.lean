/- Lean-first (no Rocq counterpart). The proof of `Open`'s crash-aware spec (`OpenCrash.lean` in
`Spec`): as `Open.lean`'s, over the crash invariant. The file `OpenFile` opens is the generation's
(`openStart`: all bytes clean and durable, a `Good` image); `Stat` and `readPageSize` read it
through the client's halves (`csOwn_idle00`); a file with no valid meta (`noValid`) is laid out by
`DB.init.specCrash`, a committed one (`committedImg`) is used as it is; either way the file is then
one a commit may start from (`openReady`), whose committed pages `cs_freeze` makes discarded
(`ready_pages`), and `DB.mmap.specCrash` maps it. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.OpenCrash
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__mmapCrash
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.flock
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__close
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__readPageSize
public import Spec.os.OpenFile
public import Spec.os.File__Name
public import Spec.os.File__Close
public import Spec.os.File__Stat
public import Spec.os.fileStat__Size
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.OpenLemmas
public import Proof.os.CrashStSpec

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section pure
variable [GooseExts]

/-- The `OsMeta` of the file a generation starts with, once opened (created if absent). -/
def startMeta : Option OsFile → OsMeta
  | none => newMeta
  | some f => initMeta f

theorem csOpen_csStart (fo : Option OsFile) :
    csOpen (csStart fo) = some ⟨startMeta fo, (startImg fo).map (·, true), 0, 0, .idle⟩ := by
  cases fo <;> rfl

/-- The file `Open` opened, of `OsMeta` `m` and bytes `F`, all clean and durable. -/
structure openStart (m : OsMeta) (F : List w8) : Prop where
  len : F.length = m.size
  ok : m.ok = true
  maps : m.maps = ∅
  lo : m.lo = m.size
  hi : m.hi = m.size
  durHi : m.durHi = m.size
  dur : m.dur = F.map some
  good : goodImg F

theorem openStart_start (fo : Option OsFile) (h : Good fo) :
    openStart (startMeta fo) (startImg fo) := by
  cases fo with
  | none =>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      ⟨by simp [startImg], Or.inl ⟨by simp [startImg], fun i _ h => by simp [startImg] at h⟩⟩⟩
  | some f => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h⟩

/-- No meta slot held whole is valid: `Open` lays the file out with `init`. -/
def noValid (F : List w8) : Prop :=
  ∀ i < 2, 4096 * i + 80 ≤ F.length → ¬ metaValid (fileMeta F i)

/-- `goodImg`'s committed case. -/
def committedImg (F : List w8) : Prop :=
  4 * 4096 ≤ F.length ∧ metaPagesOk (imgMetas F) ∧ 4096 * curPgid (imgMetas F) ≤ F.length ∧
    bootOk (curMeta (imgMetas F)).txid'.toNat
      (pageVal ((F.drop (4096 * curRoot (imgMetas F))).take 4096)) ∧
    curInSlot (imgMetas F)

theorem goodImg_cases {F : List w8} (h : goodImg F) : noValid F ∨ committedImg F := by
  obtain ⟨-, h | ⟨h4, h0, h1⟩ | h⟩ := h
  · exact Or.inl h.2
  · refine Or.inl fun i hi hl hv => ?_
    simp only [imgMetas] at h0 h1
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact h0 (by rw [fileMeta_take _ _ _ (by omega)]; exact hv)
    · exact h1 (by rw [fileMeta_take _ _ _ (by omega)]; exact hv)
  · exact Or.inr h

theorem fst_clean' (F : List w8) : (F.map (·, true)).map Prod.fst = F := by
  rw [List.map_map]; exact List.map_id _

theorem clean_of' (xs : List (w8 × Bool)) (h : ∀ x ∈ xs, x.2 = true) :
    xs = (xs.map Prod.fst).map (·, true) := by
  rw [List.map_map]
  conv => lhs; rw [← List.map_id xs]
  refine List.map_congr_left fun x hx => ?_
  obtain ⟨a, b⟩ := x
  simp only [Function.comp_apply, id]
  rw [show b = true from h _ hx]

theorem clean_get (F : List w8) (k : Nat) (hk : k < F.length) :
    ∃ b, (F.map (·, true))[k]? = some (b, true) :=
  ⟨F[k], by rw [List.getElem?_map, List.getElem?_eq_getElem hk]; rfl⟩

theorem slotsClean_clean (F : List w8) : slotsClean (F.map (·, true)) := by
  intro i _ k _ x hx
  rw [List.getElem?_map] at hx
  cases h : F[4096 * i + 16 + k]? with
  | none => rw [h] at hx; cases hx
  | some y => rw [h] at hx; cases hx; rfl

theorem start_initIdle {m : OsMeta} {F : List w8} (hs : openStart m F) (hn : noValid F) :
    initIdle m (F.map (·, true)) := by
  have hg := hs.good.1
  refine ⟨by rw [hs.hi, ← hs.len]; exact hg, fun i hi => ?_, fun i hi hl => ?_⟩
  · refine durOk_of F (fun j b hb _ => ?_) (Nat.le_of_eq (by rw [hs.durHi, hs.len])) (fun hl hv => hn i hi hl hv)
    rw [hs.dur, List.getElem?_map, hb]; rfl
  · rw [List.length_map] at hl
    obtain ⟨b, hb⟩ := clean_get F (4096 * i + 16 + 0) (by omega)
    exact Or.inl ⟨0, by omega, _, hb, rfl⟩

theorem start_commitClean {m : OsMeta} {F : List w8} (hs : openStart m F) (hc : committedImg F) :
    commitClean m (F.map (·, true)) := by
  obtain ⟨h4, hmp, hpg, hboot, hslot⟩ := hc
  have hg := hs.good.1
  have hr1 := hmp.2.2.1
  have hr2 := hmp.2.2.2.1
  simp only [imgMetas] at hmp hpg hboot hslot hr1 hr2
  refine ⟨by rw [hs.hi, ← hs.len]; exact hg, by rw [hs.lo, ← hs.len]; exact h4, ?_, ?_, ?_, ?_,
    fun k hk => clean_get F k (by omega), fun k hk => ?_⟩ <;> rw [fst_clean']
  · exact hmp
  · exact hslot
  · rw [hs.lo, ← hs.len]; exact hpg
  · exact hboot
  · have : 4096 * (curRoot (F.take 8192) + 1) ≤ 4096 * curPgid (F.take 8192) :=
      Nat.mul_le_mul_left _ hr2
    exact clean_get F _ (by omega)

/-- The starting state is `dbOk`: `init`'s idle states, or a commit's. -/
theorem start_okS {p : GoString} {m : OsMeta} {F : List w8} (hs : openStart m F) :
    dbOk p (some ⟨m, F.map (·, true), 0, 0, .idle⟩) := by
  have hl : (F.map (·, true)).length = m.size := by rw [List.length_map, hs.len]
  rcases goodImg_cases hs.good with hn | hc
  · exact initIdle_okS (p := p) ⟨m, F.map (·, true), 0, 0, .idle⟩ hl rfl (start_initIdle hs hn)
  · exact commitClean_okS (p := p) ⟨m, F.map (·, true), 0, 0, .idle⟩ hl rfl (start_commitClean hs hc)

theorem freshTx_noValid {F : List w8} (hn : noValid F) : freshTx (F.map (·, true)) = (1, none, 4) := by
  unfold freshTx
  simp only [fst_clean', List.length_map]
  rw [if_neg]
  rintro ⟨h4, h0 | h1⟩
  · exact hn 0 (by omega) (by omega) (by rw [fileMeta_take _ _ _ (by omega)] at h0; exact h0)
  · exact hn 1 (by omega) (by omega) (by rw [fileMeta_take _ _ _ (by omega)] at h1; exact h1)

theorem freshTx_committed {F : List w8} (hc : committedImg F) :
    freshTx (F.map (·, true)) = ((curMeta (F.take 8192)).txid'.toNat,
      pageVal ((F.drop (4096 * curRoot (F.take 8192))).take 4096), curPgid (F.take 8192)) := by
  unfold freshTx
  simp only [fst_clean', List.length_map]
  rw [if_pos ⟨hc.1, hc.2.1.2.1⟩]

/-- The file after `Open`'s `init` step: one a commit may start from, all clean, at transaction
`t` holding `vo`, high water mark `n`. -/
structure openReady (m : OsMeta) (bs : List (w8 × Bool)) (t : Nat) (vo : Option w64) (n : Nat) :
    Prop where
  cc : commitClean m bs
  len : bs.length = m.size
  clean : ∀ x ∈ bs, x.2 = true
  ok : m.ok = true
  maps : m.maps = ∅
  h16 : 4 * 4096 ≤ m.size
  h30 : m.size ≤ 2 ^ 30
  tx : (curMeta ((bs.map Prod.fst).take 8192)).txid'.toNat = t
  vo : pageVal (pageOf (bs.map Prod.fst) (curRoot ((bs.map Prod.fst).take 8192))) = vo
  pg : curPgid ((bs.map Prod.fst).take 8192) = n

theorem ready_committed {m : OsMeta} {F : List w8} {t : Nat} {vo : Option w64} {n : Nat}
    (hs : openStart m F) (hc : committedImg F) (hf : freshTx (F.map (·, true)) = (t, vo, n)) :
    openReady m (F.map (·, true)) t vo n := by
  rw [freshTx_committed hc] at hf
  simp only [Prod.mk.injEq] at hf
  obtain ⟨ht, hv, hn⟩ := hf
  refine ⟨start_commitClean hs hc, by rw [List.length_map, hs.len], ?_, hs.ok, hs.maps,
    by rw [← hs.len]; exact hc.1, by rw [← hs.len]; exact hs.good.1, ?_, ?_, ?_⟩
  · intro x hx; simp only [List.mem_map] at hx; obtain ⟨_, _, rfl⟩ := hx; rfl
  all_goals rw [fst_clean']
  · exact ht
  · exact hv
  · exact hn

theorem ready_init {m : OsMeta} {F : List w8} {t : Nat} {vo : Option w64} {n : Nat}
    (hs : openStart m F) (hn : noValid F) (hf : freshTx (F.map (·, true)) = (t, vo, n)) :
    openReady (initDoneMeta m (F.map (·, true))) (initFile (F.map (·, true))) t vo n := by
  rw [freshTx_noValid hn] at hf
  simp only [Prod.mk.injEq] at hf
  obtain ⟨rfl, rfl, rfl⟩ := hf
  have hsz : m.size ≤ 2 ^ 30 := by rw [← hs.len]; exact hs.good.1
  have hl : (F.map (·, true)).length = m.size := by rw [List.length_map, hs.len]
  generalize F.map (·, true) = xs at hl
  have hc := curMeta_init _ (by rw [List.take_take, Nat.min_self])
  refine ⟨init_commitClean hsz, ?_, ?_, hs.ok, hs.maps, ?_, ?_, ?_, ?_, ?_⟩
  · rw [initFile_length, hl]; rfl
  · intro x hx; rw [initFile_clean xs] at hx; simp only [List.mem_map] at hx
    obtain ⟨_, _, rfl⟩ := hx; rfl
  · simp only [initDoneMeta]; omega
  · simp only [initDoneMeta]; omega
  · rw [initFile_take, hc, initMeta_txid]; rfl
  · rw [show curRoot (((initFile xs).map Prod.fst).take 8192) = 3 by
      unfold curRoot; rw [initFile_take, hc, initMeta_root]; rfl, initFile_root]
  · unfold curPgid; rw [initFile_take, hc, initMeta_pgid]; rfl

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

/-- An idle state with nothing frozen: the client's halves of its `OsMeta` and bytes. -/
theorem csOwn_idle00 (p : GoString) (γ : GName) (m : OsMeta) (bs : List (w8 × Bool)) :
    csOwn (GF := GF) p γ (some ⟨m, bs, 0, 0, .idle⟩) ⊣⊢
      ghostVar γ (1 : Qp).half (some ⟨m, bs, 0, 0, .idle⟩ : CState) ∗
      osMeta (GF := GF) p (DFrac.own (1 : Qp).half) (some m) ∗
      osBytes (GF := GF) p 0 (DFrac.own (1 : Qp).half) bs ∗ ⌜bs.length = m.size⌝ := by
  have h := idle_thrBytes (GF := GF) p m [] [] bs 0 0 rfl rfl
  rw [List.nil_append, List.nil_append] at h
  constructor
  · iintro H
    icases (csOwn_idle _ _ _ rfl).1 $$ H with ⟨Hv, ⟨Hm, Hb⟩, %Hwf⟩
    icases h.1 $$ Hb with ⟨-, Hb⟩
    iframe
    ipureintro; exact Hwf.1
  · iintro ⟨Hv, Hm, Hb, %Hl⟩
    iapply (csOwn_idle _ _ _ rfl).2
    iframe Hv Hm
    isplitl
    · iapply h.2
      iframe
      iapply (osBytes_nil' _ _ _).2
      iempintro
    · ipureintro; exact ⟨Hl, Nat.le_refl _, Nat.zero_le _, trivial⟩

/-- The committed pages of a clean file, frozen (`cs_freeze`), as pages. -/
theorem ready_pages (p : GoString) (bs : List (w8 × Bool)) (n : Nat)
    (hcl : ∀ x ∈ bs, x.2 = true) (h : 4096 * n ≤ bs.length) (h2 : 2 ≤ n) :
    osBytes (GF := GF) p 8192 DFrac.discard ((bs.drop 8192).take (4096 * n - 8192)) ⊢
      |==> [∗list] r ∈ List.range' 2 (n - 2), pageIs (GF := GF) p r (pageOf (bs.map Prod.fst) r) := by
  obtain ⟨G, rfl⟩ : ∃ G : List w8, bs = G.map (·, true) := ⟨_, clean_of' bs hcl⟩
  rw [fst_clean', ← List.map_drop, ← List.map_take, show 8192 = 4096 * 2 by rfl,
    show 4096 * n - 4096 * 2 = 4096 * (n - 2) by omega]
  rw [List.length_map] at h
  exact pages_of_bytes p DFrac.discard G (n - 2) 2 (by omega)

end proof

end bboltfs
end EtcdGrove
end Perennial
