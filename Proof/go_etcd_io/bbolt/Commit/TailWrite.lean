/-
`Commit`'s write step (U10k of `notes/bbolt-proof-plan.md`): `tx.write()` over the writer's working
state `wtxW` and its database side `wdbLive`. The dirty pages' slots `bufSlots` are carved out of
the writer's `W` slots (`wSlots_carve`) and written; on success they come back as `slotsOwn` (what
`store_publish` takes), the writer side keeping the other `W` slots; on an error they go back into
the `W` slots with whatever bytes the write left (`wSlots_return`, `wbUpd`).
-/
module

public import Proof.go_etcd_io.bbolt.Commit.TailAcc
public import Proof.go_etcd_io.bbolt.Tx__write

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

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

end pure

section step
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
/-- **`Commit`'s write step** (see the file header), for the writer side `w` mapped once at
`b` (`l` bytes), whose `W` slots hold the dirty pages' slots (no duplicates, whole pages). -/
theorem cm_write_step (wp_write : Tx.write.spec (GF := GF) (hG := hG))
    (K : BC) (tx : Loc) (r : TxReg) (X : WX) (ws : WSt) (w : WDb) (b : Loc) (l : Nat)
    (hms : w.ms = some (b, l)) (hmaps : w.m.maps = GMap.singleton b l) (hsz : w.m.size < 2 ^ 63)
    (hpm : ∀ id, (X.t.pm !! id).isSome = (X.t.bufs !! id).isSome)
    (hbok : bufsOK X.t.bufs (min w.m.size l / 4096))
    (hnd : (bufSlots X.t.bufs).Nodup) (hsub : ∀ s ∈ bufSlots X.t.bufs, s ∈ w.W)
    (hlen : ∀ s ∈ bufSlots X.t.bufs, (w.wb s).length = 4096) :
    {{ wtxW (GF := GF) K tx r false X ∗ wdbLive K.B K.db K.p K.sp K.t0 tx ws w }}
      (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"write")) (Val #()))
    {{ (err : GoInterface), RET #err; ∃ (pml : Loc) (m' : OsMeta) (wb' : Nat → List w8),
        ⌜m'.size = w.m.size ∧ m'.maps = w.m.maps ∧
          ∀ s ∈ bufSlots X.t.bufs, (wb' s).length = 4096⌝ ∗
        wtxW K tx r false (X.clearPages pml) ∗
        ((⌜err = interface.nil⌝ ∗ ⌜∀ id pg, X.t.bufs !! id = some pg →
            ∀ j < 1 + pageOverflow pg, wb' (id.toNat + j) = pageChunk pg j⌝ ∗
          wdbLive K.B K.db K.p K.sp K.t0 tx ws (w.reslot m' (wMinus w.W (bufSlots X.t.bufs)) w.wb) ∗
          slotsOwn (some (b, l) : MapSt) K.p (bufSlots X.t.bufs) wb') ∨
         (⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err ∗
          wdbLive K.B K.db K.p K.sp K.t0 tx ws
            (w.reslot m' (bufSlots X.t.bufs ++ wMinus w.W (bufSlots X.t.bufs))
              (wbUpd (bufSlots X.t.bufs) wb' w.wb)))) }} := by
  wp_start_folded as ⟨Hw, Hd⟩
  have hin := bufSlots_inside X.t.bufs w.m.size l hbok
  icases cm_write_acc K tx r false X $$ Hw with ⟨#Hcore, #Hreg, Hst, Hdb, Hpg, Hpm, Hbufs, Hwb⟩
  icases cm_file_acc K.B K.db K.p K.sp K.t0 tx ws w $$ Hd
    with ⟨Hfile, Hwa, Hfo, Hfd, Hom, Hwc, Hwbs, Hdb'⟩
  rw [hms]
  icases wSlots_carve b l K.p w.W (bufSlots X.t.bufs) w.wb w.m.size hnd hsub
    (fun s hs => hin s hs) $$ [Hwc Hwbs] with ⟨Hs, Hwc, Hwbs⟩
  · iframe
  wp_apply wp_write K tx r false 1 (DFrac.own (txDbQ 1)) X.t.t.pages' X.t.pm X.t.bufs w.wb w.f w.fd
    w.m b l (DFrac.own 1) (DFrac.own (1 : Qp).half) hpm hbok hsz hmaps hlen
    $$ [Hst Hdb Hpg Hpm Hbufs Hfile Hwa Hfo Hfd Hom Hs]
    as %err ⟨Hst, Hdb, ⟨%pml, Hpg, Hpm⟩, Hfile, Hwa, Hfo, Hfd, ⟨%om', Hom, %Hom'⟩, %wb', %Hwb', Hres⟩
  · iframe; iframe #
  ihave Hw := Hwb $$ %pml Hst Hdb Hpg Hpm
  iapply HΦ
  iexists pml, om', wb'
  isplitr
  · ipureintro; exact ⟨Hom'.1, Hom'.2, Hwb'⟩
  iframe Hw
  icases Hres with (⟨%He, %Hch, Ho⟩ | ⟨%He, #Hfe, Hs⟩)
  · ileft
    iframe Ho
    isplitr
    · ipureintro; exact He
    isplitr
    · ipureintro; exact Hch
    iapply Hdb' $$ %om' %(wMinus w.W (bufSlots X.t.bufs)) %w.wb Hfile Hwa Hfo Hfd Hom [Hwc] [Hwbs]
    · first | iexact Hwc | (rw [hms]; iexact Hwc)
    · first | iexact Hwbs | (rw [Hom'.1]; iexact Hwbs)
  · iright
    iframe Hfe
    isplitr
    · ipureintro; exact He
    icases wSlots_return b l K.p (wMinus w.W (bufSlots X.t.bufs)) (bufSlots X.t.bufs) w.wb wb'
      w.m.size (fun s hs => ((mem_wMinus _ _ s).1 hs).2) (fun s hs => hin s hs)
      $$ [Hs Hwc Hwbs] with ⟨Hwc, Hwbs⟩
    · iframe
    iapply Hdb' $$ %om' %_ %_ Hfile Hwa Hfo Hfd Hom [Hwc] [Hwbs]
    · first | iexact Hwc | (rw [hms]; iexact Hwc)
    · first | iexact Hwbs | (rw [Hom'.1]; iexact Hwbs)

end step

end bbolt
end EtcdGrove
end Perennial
