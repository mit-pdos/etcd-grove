/-
`Commit`'s write step (U10k of `notes/bbolt-proof-plan.md`): `tx.write()` (`Tx.write_ext`: the
dirty pages anywhere in the mapping) over the writer's working state `wtxW` and its database side
`wdbLive`. The dirty pages' slots `bufSlots` and the mapping's slots past the file's end
(`cmTail`) are carved out of the writer's `W` slots (`wSlots_carveSz`) and written; on success the
pages' slots come back as `slotsOwn` (what `store_publish` takes) and the tail into `W`; on an
error all of them go back into `W` with whatever bytes the write left (`wSlots_returnSz`,
`wbUpd`).
-/
module

public import Proof.go_etcd_io.bbolt.Commit.TailAcc
public import Spec.go_etcd_io.bbolt.Tx__write_ext

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

theorem mem_bufSlots (bufs : GMap w64 (List w8)) (s : Nat) :
    s ∈ bufSlots bufs ↔ ∃ id pg, bufs !! id = some pg ∧ id.toNat ≤ s ∧
      s < id.toNat + (1 + pageOverflow pg) := by
  unfold bufSlots
  simp only [List.mem_flatMap, List.mem_range']
  constructor
  · rintro ⟨⟨id, pg⟩, he, i, hi, rfl⟩
    dsimp only at hi ⊢
    exact ⟨id, pg, (GMap.mem_toList bufs id pg).1 he, by omega, by omega⟩
  · rintro ⟨id, pg, hb, h1, h2⟩
    refine ⟨(id, pg), (GMap.mem_toList bufs id pg).2 hb, s - id.toNat, ?_, ?_⟩
    · dsimp only; omega
    · dsimp only; omega

/-- The dirty pages' slots lie whole inside the file and the mapping. -/
theorem bufSlots_inside (bufs : GMap w64 (List w8)) (size l : Nat)
    (h : bufsOK bufs (min size l / 4096)) :
    ∀ s ∈ bufSlots bufs, 4096 * (s + 1) ≤ l ∧ 4096 * (s + 1) ≤ size := by
  intro s hs
  obtain ⟨id, pg, hb, h1, h2⟩ := (mem_bufSlots bufs s).1 hs
  have h4 := (h id pg hb).2.2.2
  have h5 : 4096 * (min size l / 4096) ≤ min size l := Nat.mul_div_le _ _
  have h6 : 4096 * (s + 1) ≤ 4096 * (min size l / 4096) := Nat.mul_le_mul_left _ (by omega)
  constructor <;> omega

/-- **The tail slots** of a write at the mapping of `l` bytes: the `W` slots of the mapping not
wholly inside the file, but the dirty pages' `SB`. -/
def cmTail (w : WDb) (SB : List Nat) (l : Nat) : List Nat :=
  (List.range (l / 4096)).filter fun s => decide (s ∈ w.W ∧ w.m.size < 4096 * (s + 1) ∧ s ∉ SB)

theorem mem_cmTail (w : WDb) (SB : List Nat) (l s : Nat) :
    s ∈ cmTail w SB l ↔ s < l / 4096 ∧ s ∈ w.W ∧ w.m.size < 4096 * (s + 1) ∧ s ∉ SB := by
  simp [cmTail]

theorem cmTail_nodup (w : WDb) (SB : List Nat) (l : Nat) (hSB : SB.Nodup) :
    (SB ++ cmTail w SB l).Nodup := by
  refine List.nodup_append.2 ⟨hSB, (List.nodup_range).filter _, fun a ha b hb => ?_⟩
  rintro rfl
  exact ((mem_cmTail w SB l a).1 hb).2.2.2 ha

end pure

section step
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
/-- **`Commit`'s write step** (see the file header), for the writer side `w` mapped once at
`b` (`l` bytes), whose `W` slots hold the dirty pages' slots (no duplicates) and every slot of the
mapping past the file's end, and whose `W` slots past the mapping lie inside the file. -/
theorem cm_write_step (wp_write : Tx.write_ext.spec (GF := GF) (hG := hG))
    (K : BC) (tx : Loc) (r : TxReg) (X : WX) (ws : WSt) (w : WDb) (b : Loc) (l : Nat)
    (hms : w.ms = some (b, l)) (hmaps : w.m.maps = GMap.singleton b l) (hsz : w.m.size < 2 ^ 63)
    (hl : l < 2 ^ 63) (hpm : ∀ id, (X.t.pm !! id).isSome = (X.t.bufs !! id).isSome)
    (hbok : bufsOK X.t.bufs (l / 4096))
    (hnd : (bufSlots X.t.bufs).Nodup) (hsub : ∀ s ∈ bufSlots X.t.bufs, s ∈ w.W)
    (hW : ∀ s, s < l / 4096 → w.m.size < 4096 * (s + 1) → s ∈ w.W)
    (hlen : ∀ s ∈ w.W, 4096 * (s + 1) ≤ w.m.size → (w.wb s).length = 4096)
    (hinW : ∀ s ∈ w.W, l / 4096 ≤ s → 4096 * (s + 1) ≤ w.m.size)
    (hpart : ∀ s, 4096 * s < w.m.size → w.m.size < 4096 * (s + 1) →
      w.m.size - 4096 * s ≤ (w.wb s).length) :
    {{ wtxW (GF := GF) K tx r false X ∗ wdbLive K.B K.db K.p K.sp K.t0 tx ws w }}
      (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"write")) (Val #()))
    {{ (err : GoInterface), RET #err; ∃ (pml : Loc) (m' : OsMeta) (wb' : Nat → List w8),
        ⌜w.m.size ≤ m'.size ∧ m'.size ≤ max w.m.size l ∧ m'.maps = w.m.maps ∧
          (∀ s ∈ bufSlots X.t.bufs ++ cmTail w (bufSlots X.t.bufs) l, 4096 * (s + 1) ≤ m'.size →
            (wb' s).length = 4096) ∧
          m'.size ≤ max w.m.size (4096 * (l / 4096)) ∧
          (∀ s ∈ bufSlots X.t.bufs ++ cmTail w (bufSlots X.t.bufs) l, 4096 * s < m'.size →
            m'.size < 4096 * (s + 1) → m'.size - 4096 * s ≤ (wb' s).length)⌝ ∗
        wtxW K tx r false (X.clearPages pml) ∗
        ((⌜err = interface.nil⌝ ∗ ⌜(∀ s ∈ bufSlots X.t.bufs, 4096 * (s + 1) ≤ m'.size) ∧
            (∀ id pg, X.t.bufs !! id = some pg →
              ∀ j < 1 + pageOverflow pg, wb' (id.toNat + j) = pageChunk pg j) ∧
            (∀ s ∈ bufSlots X.t.bufs ++ cmTail w (bufSlots X.t.bufs) l, 4096 * s < m'.size →
              m'.size < 4096 * (s + 1) → m'.size - 4096 * s ≤ (wb' s).length) ∧
            (m'.size = w.m.size ∨ m'.size % 4096 = 0)⌝ ∗
          wdbLive K.B K.db K.p K.sp K.t0 tx ws
            (w.reslot m' (cmTail w (bufSlots X.t.bufs) l ++
                wMinus w.W (bufSlots X.t.bufs ++ cmTail w (bufSlots X.t.bufs) l))
              (wbUpd (cmTail w (bufSlots X.t.bufs) l) wb' w.wb)) ∗
          slotsOwn (some (b, l) : MapSt) K.p (bufSlots X.t.bufs) wb') ∨
         (⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err ∗
          wdbLive K.B K.db K.p K.sp K.t0 tx ws
            (w.reslot m' ((bufSlots X.t.bufs ++ cmTail w (bufSlots X.t.bufs) l) ++
                wMinus w.W (bufSlots X.t.bufs ++ cmTail w (bufSlots X.t.bufs) l))
              (wbUpd (bufSlots X.t.bufs ++ cmTail w (bufSlots X.t.bufs) l) wb' w.wb)))) }} := by
  wp_start_folded as ⟨Hw, Hd⟩
  have hinS : ∀ s ∈ bufSlots X.t.bufs, 4096 * (s + 1) ≤ l := by
    intro s hs
    obtain ⟨id, pg, hp, h1, h2⟩ := (mem_bufSlots X.t.bufs s).1 hs
    have h4 := (hbok id pg hp).2.2.2
    have h5 : 4096 * (l / 4096) ≤ l := Nat.mul_div_le _ _
    omega
  have hinT : ∀ s ∈ cmTail w (bufSlots X.t.bufs) l, 4096 * (s + 1) ≤ l := by
    intro s hs
    have h1 := ((mem_cmTail _ _ _ s).1 hs).1
    have h5 : 4096 * (l / 4096) ≤ l := Nat.mul_div_le _ _
    omega
  have hin : ∀ s ∈ bufSlots X.t.bufs ++ cmTail w (bufSlots X.t.bufs) l, 4096 * (s + 1) ≤ l := by
    intro s hs
    rcases List.mem_append.1 hs with h | h
    · exact hinS s h
    · exact hinT s h
  have hsub' : ∀ s ∈ bufSlots X.t.bufs ++ cmTail w (bufSlots X.t.bufs) l, s ∈ w.W := by
    intro s hs
    rcases List.mem_append.1 hs with h | h
    · exact hsub s h
    · exact ((mem_cmTail _ _ _ s).1 h).2.1
  have hrest : ∀ s ∈ wMinus w.W (bufSlots X.t.bufs ++ cmTail w (bufSlots X.t.bufs) l),
      4096 * (s + 1) ≤ w.m.size := by
    intro s hs
    obtain ⟨hsW, hsn⟩ := (mem_wMinus _ _ s).1 hs
    by_cases hlt : s < l / 4096
    · apply Nat.le_of_not_lt
      intro hgt
      apply hsn
      by_cases hSB : s ∈ bufSlots X.t.bufs
      · exact List.mem_append_left _ hSB
      · exact List.mem_append_right _ ((mem_cmTail _ _ _ s).2 ⟨hlt, hsW, hgt, hSB⟩)
    · exact hinW s hsW (by omega)
  icases cm_write_acc K tx r false X $$ Hw with ⟨#Hcore, #Hreg, Hst, Hdb, Hpg, Hpm, Hbufs, Hwb⟩
  icases cm_file_acc K.B K.db K.p K.sp K.t0 tx ws w $$ Hd
    with ⟨Hfile, Hwa, Hfo, Hfd, Hom, Hwc, Hwbs, Hdb'⟩
  rw [hms]
  icases wSlots_carveSz b l K.p w.W _ w.wb w.m.size (cmTail_nodup w _ l hnd) hsub' hin
    $$ [Hwc Hwbs] with ⟨Hs, Hwc, Hwbs⟩
  · iframe
  wp_apply wp_write K tx r false 1 (DFrac.own (txDbQ 1)) X.t.t.pages' X.t.pm X.t.bufs
    (cmTail w (bufSlots X.t.bufs) l) w.wb w.f w.fd w.m b l (DFrac.own 1) (DFrac.own (1 : Qp).half)
    hpm hbok hsz hl hmaps (cmTail_nodup w _ l hnd)
    (fun s hs => ((mem_cmTail _ _ _ s).1 hs).1)
    (fun s hs hgt => by
      by_cases hSB : s ∈ bufSlots X.t.bufs
      · exact Or.inl hSB
      · exact Or.inr ((mem_cmTail _ _ _ s).2 ⟨hs, hW s hs hgt, hgt, hSB⟩))
    (fun s hs hz => hlen s (hsub' s hs) hz) (fun s _ h1 h2 => hpart s h1 h2)
    $$ [Hst Hdb Hpg Hpm Hbufs Hfile Hwa Hfo Hfd Hom Hs]
    as %err ⟨Hst, Hdb, ⟨%pml, Hpg, Hpm⟩, Hfile, Hwa, Hfo, Hfd, %om', %wb', Hom, %Hom', Hres⟩
  · iframe; iframe #
  ihave Hw := Hwb $$ %pml Hst Hdb Hpg Hpm
  iapply HΦ
  iexists pml, om', wb'
  isplitr
  · ipureintro
    have h5 : 4096 * (l / 4096) ≤ l := Nat.mul_div_le _ _
    exact ⟨Hom'.1, by have := Hom'.2.1; omega, Hom'.2.2.1, Hom'.2.2.2.1, Hom'.2.1,
      Hom'.2.2.2.2.2⟩
  iframe Hw
  icases Hres with (⟨%He, %Hch, Ho, HT⟩ | ⟨%He, #Hfe, Hs⟩)
  · ileft
    iframe Ho
    isplitr
    · ipureintro; exact He
    isplitr
    · ipureintro; exact Hch
    icases wSlots_returnSz b l K.p _ (cmTail w (bufSlots X.t.bufs) l) w.wb wb' w.m.size om'.size
      (fun s hs hT => ((mem_wMinus _ _ s).1 hs).2 (List.mem_append_right _ hT)) hinT hrest Hom'.1
      $$ [HT Hwc Hwbs] with ⟨Hwc, Hwbs⟩
    · iframe
    iapply Hdb' $$ %om' %_ %_ Hfile Hwa Hfo Hfd Hom [Hwc] [Hwbs]
    · first | iexact Hwc | (rw [hms]; iexact Hwc)
    · iexact Hwbs
  · iright
    iframe Hfe
    isplitr
    · ipureintro; exact He
    icases wSlots_returnSz b l K.p _ _ w.wb wb' w.m.size om'.size
      (fun s hs hT => ((mem_wMinus _ _ s).1 hs).2 hT) hin hrest Hom'.1
      $$ [Hs Hwc Hwbs] with ⟨Hwc, Hwbs⟩
    · iframe
    iapply Hdb' $$ %om' %_ %_ Hfile Hwa Hfo Hfd Hom [Hwc] [Hwbs]
    · first | iexact Hwc | (rw [hms]; iexact Hwc)
    · iexact Hwbs

end step

end bbolt
end EtcdGrove
end Perennial
