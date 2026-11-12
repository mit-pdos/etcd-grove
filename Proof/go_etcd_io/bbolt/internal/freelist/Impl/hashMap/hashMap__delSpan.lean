/-
`hashMap.delSpan` (U2 internal; ported from the old proof).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.HashOwn
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.HashLemmas
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.HashDelete

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `f.delSpan(start, size)`: the span at `start`, of size `size` (in a consistent `hashMap`),
is removed from the maps (its set of size `size` dropped if it is left empty), and `size` from
the count. -/
abbrev hashMap.delSpan.spec : Prop :=
  ∀ (h : Loc) (cnt : w64) (sp bwm : GMap w64 w64) (sets : GMap w64 (GMap w64 Unit))
    (free : List w64) (start size : w64),
  hashOK cnt sp bwm sets free → sp !! start = some size →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ hmRaw (GF := GF) h cnt sp bwm sets }}
    (App (App (Val (h @!! go.GoType.PointerType hashMap.ty @!! go!"delSpan")) (Val #start)) (Val #size))
  {{ RET #(); hmRaw h (cnt - size) (GMap.delete start sp)
      (GMap.delete (start + (size - W64 1)) bwm) (setsDel sets size start) }}



theorem hashMap.delSpan.wp_proof (hdel : PidSetDeleteUnfold (GF := GF)) :
    hashMap.delSpan.spec (GF := GF) (hG := hG) := by
  intro h cnt sp bwm sets free start size Hok Hst
  wp_start as Hraw
  unfold hmRaw
  iNamed Hraw
  ihave %Hdom := BigSepM2.bigSepM2_lookup_iff $$ Hsets
  obtain ⟨set, hset, -⟩ := (Hok.2.2.1.2.1 size start).2 Hst
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 ((Hdom size).2
    (by simp only [show Std.get? sets size = some set from hset, Option.isSome_some]))
  have hl' : FM !! size = some l := hl
  have Hlt : GMap.size (GMap.delete start set) < 2 ^ 63 :=
    setsDel_size_lt Hok hset (GMap.delete start set) (fun k hk => by
      rw [lookup_delete_isSome] at hk; exact hk.2)
  wp_auto
  wp_apply wp_mapDelete $$ [Hfw] as Hfw
  · iexact Hfw
  try wp_auto
  wp_apply wp_mapDelete $$ [Hbw] as Hbw
  · iexact Hbw
  try wp_auto
  wp_apply wp_map_lookup1 $$ [Hfm] as Hfm
  · iexact Hfm
  rw [hl', Option.getD_some]
  icases BigSepM2.bigSepM2_insert_acc hl hset $$ Hsets with ⟨Hl, Hback⟩
  try wp_auto
  wp_apply (wp_mapDelete_pidSet hdel) $$ [Hl] as Hl
  · iexact Hl
  try wp_auto
  wp_apply wp_map_lookup1 $$ [Hfm] as Hfm
  · iexact Hfm
  rw [hl', Option.getD_some]
  try wp_auto
  wp_apply (wp_map_len (K := w64) (V := Unit)) $$ Hl as Hl
  have Hsd : setsDel sets size start =
      if GMap.size (GMap.delete start set) = 0 then GMap.delete size sets
      else <[size := GMap.delete start set]> sets := by
    unfold setsDel; rw [hset, Option.getD_some]
  try wp_auto
  wp_if_destruct
  · have H0 : GMap.size (GMap.delete start set) = 0 := by
      have := Hif; word
    try wp_auto
    wp_apply wp_mapDelete $$ [Hfm] as Hfm
    · iexact Hfm
    try wp_auto
    ihave Hsets := Hback $$ %l %(GMap.delete start set) Hl
    rw [show (Std.insert FM size l : GMap w64 Loc) = FM from GMap.insert_id FM size l hl']
    have hins : (Std.get? (Std.insert sets size (GMap.delete start set)) size) =
        some (GMap.delete start set) := GMap.lookup_insert _ _ _
    icases (BigSepM2.bigSepM2_delete hl hins).1 $$ Hsets with ⟨-, Hsets⟩
    iapply HΦ
    iexists fm, fw, bw, (GMap.delete size FM)
    rw [Hsd, if_pos H0]
    simp only [named]
    iframe
    iExactEq Hsets
    congr 1
    apply GMap.map_eq; intro k
    show (GMap.delete size (<[size := GMap.delete start set]> sets)) !! k = _
    rw [GMap.lookup_delete_iff, GMap.lookup_delete_iff]
    split
    · rfl
    · rename_i hk; exact GMap.lookup_insert_ne _ _ hk
  · have H0 : GMap.size (GMap.delete start set) ≠ 0 := by
      intro h0; apply Hif; rw [h0]; rfl
    try wp_auto
    ihave Hsets := Hback $$ %l %(GMap.delete start set) Hl
    rw [show (Std.insert FM size l : GMap w64 Loc) = FM from GMap.insert_id FM size l hl']
    iapply HΦ
    iexists fm, fw, bw, FM
    rw [Hsd, if_neg H0]
    simp only [named]
    iframe

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
