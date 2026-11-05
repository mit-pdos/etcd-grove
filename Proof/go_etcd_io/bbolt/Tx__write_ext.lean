/-
The proof of `Spec/go_etcd_io/bbolt/Tx__write_ext.lean` (maintainer 12, item 3 of
`notes/bbolt-proof-plan.md`): when every dirty page lies inside the file, `Tx.write.wp_proof` (the
page slots carved out of `wrSlotsSz` as `wrSlots`, `wrSlotsSz_in`; the tail untouched, the file's
size unchanged; the new bytes `wbUpd` of the page slots). The case of a page past the file's end
(`WriteAt` extending the file, the zero gap's cells from the waiting slots) is
`Commit/WriteExtRun.Tx.write_ext_gen` (U10w), under a premise the spec lacks (a slot across the old
end holds its part inside the file); without it, a named `sorry` (`write_ext_straddle`).
-/
module

public import Spec.go_etcd_io.bbolt.Tx__write_ext
public import Proof.go_etcd_io.bbolt.Tx__write
public import Proof.go_etcd_io.bbolt.Commit.WriteExtRun

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

private theorem mem_bufSlots_ext (bufs : GMap w64 (List w8)) (s : Nat) (hs : s ∈ bufSlots bufs) :
    ∃ id pg, bufs !! id = some pg ∧ id.toNat ≤ s ∧ s < id.toNat + (1 + pageOverflow pg) := by
  unfold bufSlots at hs
  simp only [List.mem_flatMap, List.mem_range'] at hs
  obtain ⟨⟨id, pg⟩, he, i, hi, rfl⟩ := hs
  dsimp only at hi ⊢
  exact ⟨id, pg, (GMap.mem_toList bufs id pg).1 he, by omega, by omega⟩

private theorem bufSlots_mem_ext (bufs : GMap w64 (List w8)) (id : w64) (pg : List w8)
    (hb : bufs !! id = some pg) (j : Nat) (hj : j < 1 + pageOverflow pg) :
    id.toNat + j ∈ bufSlots bufs := by
  unfold bufSlots
  simp only [List.mem_flatMap, List.mem_range']
  exact ⟨(id, pg), (GMap.mem_toList bufs id pg).2 hb, j, hj, by dsimp only; omega⟩

/-- `slotsOwn` only reads the bytes on its slots. -/
private theorem slotsOwn_congr_ext (ms : MapSt) (p : GoString) (S : List Nat) (bs bs' : Nat → List w8)
    (h : ∀ s ∈ S, bs s = bs' s) : slotsOwn (GF := GF) ms p S bs ⊢ slotsOwn ms p S bs' := by
  unfold slotsOwn
  apply BigSepL.bigSepL_mono
  intro k x hx
  have he := h _ (List.mem_of_getElem? hx)
  rcases ms with _ | ⟨base, _⟩ <;> simp only [he] <;> exact .rfl

/-- **`tx.write()` with the pages anywhere in the mapping** (see the file header). -/
theorem Tx.write_ext.wp_proof (hLogger : DB.Logger.spec (GF := GF) (hG := hG))
    (hSort : sort.«Sort».anyLessSpec (GF := GF) (hG := hG))
    (hOv : internal.common.Page.Overflow.spec (GF := GF) (hG := hG))
    (hId : internal.common.Page.Id.spec (GF := GF) (hG := hG))
    (hUBS : internal.common.UnsafeByteSlice.spec (GF := GF) (hG := hG))
    (hWriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (hSync : fdatasync.spec (GF := GF) (hG := hG))
    (hInc : TxStats.IncWrite.spec (GF := GF) (hG := hG)) :
    Tx.write_ext.spec (GF := GF) (hG := hG) := by
  intro K tx r sm q dq pml pm bufs T wb f fd om b l dqf dqw hdom hok hsz hl hmaps hnd hT htail hwb
  by_cases hin : ∀ id pg, bufs !! id = some pg →
    4096 * (id.toNat + (1 + pageOverflow pg)) ≤ om.size
  case neg =>
    -- a dirty page past the file's end (`NoGrowSync`): `Commit/WriteExtRun.Tx.write_ext_gen`, under
    -- `hstr` (a target slot across the old end holds at least its part inside the file)
    by_cases hstr : ∀ s ∈ bufSlots bufs ++ T, 4096 * s < om.size →
      om.size ≤ 4096 * s + (wb s).length
    · exact Tx.write_ext_gen hLogger hSort hOv hId hUBS hWriteAt hSync hInc K tx r sm q dq pml pm
        bufs T wb f fd om b l dqf dqw hdom hok hsz hl hmaps hnd hT htail hwb hstr
    · -- OPEN, `write_ext_straddle` (U10w): the spec is false here. A slot `s` of `bufSlots ++ T`
      -- across the old end (`4096 s < om.size < 4096 (s + 1)`) with `(wb s).length < om.size -
      -- 4096 s` owns, by `wBytes`, only `(wb s).length` of its bytes inside the file; the rest of
      -- them is owned by no resource of the pre, but the post (the slot whole inside the grown
      -- file, or the page's own `WriteAt`) needs them. Fix (for the spec's owner): the premise
      -- `∀ s ∈ bufSlots bufs ++ T, 4096 * s < om.size → (wb s).length = 4096` (or this `hstr`).
      sorry
  have hok' : bufsOK bufs (min om.size l / 4096) := by
    intro id pg hb
    obtain ⟨h1, h2, h3, h4⟩ := hok id pg hb
    have h5 := hin id pg hb
    refine ⟨h1, h2, h3, ?_⟩
    have : id.toNat + (1 + pageOverflow pg) ≤ om.size / 4096 := by omega
    rw [Nat.min_def]; split <;> omega
  have hinS : ∀ s ∈ bufSlots bufs, 4096 * (s + 1) ≤ om.size := by
    intro s hs
    obtain ⟨id, pg, hb, h1, h2⟩ := mem_bufSlots_ext bufs s hs
    have := hin id pg hb
    omega
  have hwb' : ∀ s ∈ bufSlots bufs, (wb s).length = 4096 :=
    fun s hs => hwb s (List.mem_append_left _ hs) (hinS s hs)
  have hdisj : ∀ s ∈ T, s ∉ bufSlots bufs := by
    intro s hs hs'
    exact (List.nodup_append.1 hnd).2.2 s hs' s hs rfl
  have wp_write := Tx.write.wp_proof hLogger hSort hOv hId hUBS hWriteAt hSync hInc
  iintro %Φ ⟨#Hcore, #Hreg, Hst, Hdb, Hpg, Hpm, Hbufs, Hf, Hwa, Hfo, Hfd, Hm, Hslots⟩ HΦ
  icases (wrSlotsSz_app (GF := GF) b K.p (bufSlots bufs) T wb om.size).1 $$ Hslots with ⟨Hs, HT⟩
  ihave Hs := (wrSlotsSz_in (GF := GF) b K.p (bufSlots bufs) wb om.size hinS).1 $$ Hs
  wp_apply wp_write K tx r sm q dq pml pm bufs wb f fd om b l dqf dqw hdom hok' hsz hmaps hwb'
    $$ [Hst Hdb Hpg Hpm Hbufs Hf Hwa Hfo Hfd Hm Hs]
    as %err ⟨Hst, Hdb, Hpg, Hf, Hwa, Hfo, Hfd, ⟨%om', Hom, %Hom'⟩, %wb', %Hwb', Hres⟩
  · iframe; iframe #
  iapply HΦ
  iframe Hst Hdb Hpg Hf Hwa Hfo Hfd
  iexists om', wbUpd (bufSlots bufs) wb' wb
  iframe Hom
  have hupdT : ∀ s ∈ T, wb s = wbUpd (bufSlots bufs) wb' wb s := by
    intro s hs; simp only [wbUpd, hdisj s hs, ite_false]
  have hupdB : ∀ s ∈ bufSlots bufs, wb' s = wbUpd (bufSlots bufs) wb' wb s := by
    intro s hs; simp only [wbUpd, hs, ite_true]
  isplitr
  · ipureintro
    refine ⟨Nat.le_of_eq Hom'.1.symm, by rw [Hom'.1]; exact Nat.le_max_left _ _, Hom'.2, ?_, ?_⟩
    · intro s hs hs'
      rcases List.mem_append.1 hs with hs | hs
      · rw [← hupdB s hs]; exact Hwb' s hs
      · rw [← hupdT s hs]; exact hwb s (List.mem_append_right _ hs) (by rw [Hom'.1] at hs'; exact hs')
    · intro s hs _; exact (hupdT s hs).symm
  icases Hres with (⟨%He, %Hch, Ho⟩ | ⟨%He, #Hfe, Hs⟩)
  · ileft
    isplitr
    · ipureintro; exact He
    isplitr
    · ipureintro
      refine ⟨fun s hs => by rw [Hom'.1]; exact hinS s hs, ?_⟩
      intro id pg hb j hj
      rw [← hupdB _ (bufSlots_mem_ext bufs id pg hb j hj)]
      exact Hch id pg hb j hj
    isplitl [Ho]
    · iapply slotsOwn_congr_ext _ _ _ _ _ hupdB $$ Ho
    · rw [Hom'.1]
      iapply wrSlotsSz_congr _ _ _ _ _ _ hupdT $$ HT
  · iright
    iframe Hfe
    isplitr
    · ipureintro; exact He
    rw [Hom'.1]
    iapply (wrSlotsSz_app (GF := GF) b K.p (bufSlots bufs) T _ om.size).2
    isplitl [Hs]
    · iapply wrSlotsSz_congr _ _ _ _ _ _ hupdB
      iapply (wrSlotsSz_in (GF := GF) b K.p (bufSlots bufs) wb' om.size hinS).2
      iexact Hs
    · iapply wrSlotsSz_congr _ _ _ _ _ _ hupdT $$ HT

end proof

end bbolt
end EtcdGrove
end Perennial
