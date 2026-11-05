/- Lean-first (no Rocq counterpart). The proof of `writer.genLease`: the range loop collects the
map's keys (`ids` holds the first `i` keys of the iteration order), `sort.Slice` only permutes them,
so the element `intn(len(ids))` picks is a key of the map.

`sort.Slice` is translated names-only (reflection: `reflectlite.Swapper`) and has no spec, in
Perennial or here: the proof takes the triple it needs as a hypothesis (`wp_sortSlice`: `sort.Slice`
permutes the slice, calling `less` only on indices in range, with the slice at some permutation),
to be stated as `sort.Slice.spec` at the trust boundary. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__genLease
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.rng__intn

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem writer.genLease.wp_proof (wp_intn : rng.intn.spec (GF := GF) (hG := hG))
    (wp_sortSlice : ∀ (s : GoSlice) (xs : List w64) (less : GoFunc) (P : IProp GF),
      {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ s ↦* xs ∗ P ∗
          □ (∀ (i j : w64) (ys : List w64) (Φ : val → IProp GF),
            ⌜0 ≤ sint.Z i ∧ sint.Z i < sint.Z s.len ∧ 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len ∧
              ys.Perm xs⌝ -∗
            s ↦* ys -∗ P -∗ (∀ b : Bool, s ↦* ys -∗ P -∗ Φ #b) -∗
            WP (App (App (Val #less) (Val #i)) (Val #j)) {{ Φ }}) }}
        (App (App (Val (@! sort.Slice')) (Val #(interface.mkOk (go.GoType.SliceType go.int64) #s)))
          (Val #less))
      {{ RET #(); ∃ ys : List w64, s ↦* ys ∗ P ∗ ⌜ys.Perm xs⌝ }}) :
    writer.genLease.spec (GF := GF) (hG := hG) := by
  intro w wv Lm g
  wp_start as ⟨#Hw, Hm, Hr⟩
  ihave #Hw2 := Hw
  iunfold writerRO at Hw2
  icases Hw2 with ⟨#kvW, #leW, #hW, #rW, #leasesW, #applyingW, #savedW, #ticksW⟩
  wp_auto
  wp_apply wp_intn wv.r' g (W64 2) (by word) $$ [$Hr] as %x ⟨⟨%g1, Hr⟩, %Hx⟩
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ
    iframe
    ipureintro; left; rfl
  wp_apply wp_map_len $$ Hm as Hm
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ
    iframe
    ipureintro; left; rfl
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (x : w64) (s : GoSlice),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "id" ∷ id_ptr ↦ x ∗
      "ids" ∷ ids_ptr ↦ s ∗
      "Hs" ∷ s ↦* keys.take i.toNat ∗
      "Hcap" ∷ ownSliceCap w64 s (DFrac.own 1))) $$ Hm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [id ids]
  · iexists _, slice.nil
    simp only [named, Int.toNat_zero, List.take_zero]
    iframe
    isplitr
    · ipureintro; exact Int.le_refl _
    isplitl
    · iapply ownSlice_nil
    iapply ownSliceCap_nil
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    wp_auto
    wp_apply wp_slice_literal (V := w64) [key]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl2] as %s' ⟨Hs, Hcap, -⟩
    (try wp_auto)
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists key, s'
    simp only [named]
    iframe
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega]
      rw [List.take_add_one, Hkey]; rfl
    rw [Htake]
    iframe
    ipureintro; omega
  iintro HP Hm
  iNamed HP
  have Htk : keys.take ((GMap.size Lm : Nat) : Int).toNat = keys := by
    rw [Int.toNat_natCast, ← Hklen, List.take_length]
  rw [Htk]
  wp_auto
  wp_apply wp_sortSlice s keys _ iprop(ids_ptr ↦ s) $$ [$Hs $ids] as ⟨%ys, Hs, ids, %Hperm⟩
  · imodintro
    iintro %i %j %ys %Φ' %Hij Hs ids HΦ'
    wp_auto
    ihave %Hl := ownSlice_len $$ Hs
    obtain ⟨hi0, hi1, hj0, hj1, -⟩ := Hij
    have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z s.len := ⟨hi0, hi1⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    have hidx : (sint.Z i).toNat < ys.length := by
      have : sint.nat s.len = (sint.Z s.len).toNat := rfl
      omega
    wp_apply wp_load_slice_index s (sint.Z i) ys (DFrac.own 1) (ys[(sint.Z i).toNat]'hidx) hi0 $$ [Hs]
      as Hs
    · iframe; ipureintro; exact List.getElem?_eq_getElem hidx
    have hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len := ⟨hj0, hj1⟩
    simp only [hb', _root_.and_self, ↓reduceIte]
    have hjdx : (sint.Z j).toNat < ys.length := by
      have : sint.nat s.len = (sint.Z s.len).toNat := rfl
      omega
    wp_apply wp_load_slice_index s (sint.Z j) ys (DFrac.own 1) (ys[(sint.Z j).toNat]'hjdx) hj0 $$ [Hs]
      as Hs
    · iframe; ipureintro; exact List.getElem?_eq_getElem hjdx
    iapply HΦ' $$ Hs ids
  ihave %Hl := ownSlice_len $$ Hs
  have hlen : ys.length = GMap.size Lm := by rw [Hperm.length_eq, Hklen]
  have hpos : 0 < sint.Z s.len := by
    have : sint.nat s.len = (sint.Z s.len).toNat := rfl
    have : GMap.size Lm ≠ 0 := fun h => Hif (by rw [h]; rfl)
    omega
  wp_apply wp_intn wv.r' g1 s.len hpos $$ [$Hr] as %y ⟨⟨%g2, Hr⟩, %Hy⟩
  have hb : 0 ≤ sint.Z y ∧ sint.Z y < sint.Z s.len := Hy
  simp only [hb, _root_.and_self, ↓reduceIte]
  have hydx : (sint.Z y).toNat < ys.length := by
    have : sint.nat s.len = (sint.Z s.len).toNat := rfl
    omega
  wp_apply wp_load_slice_index s (sint.Z y) ys (DFrac.own 1) (ys[(sint.Z y).toNat]'hydx) Hy.1 $$ [Hs]
    as Hs
  · iframe; ipureintro; exact List.getElem?_eq_getElem hydx
  iapply HΦ
  iframe
  ipureintro; right
  exact (Hkset _).1 (Hperm.mem_iff.1 (List.getElem_mem hydx))

end proof

end mvccrand
end EtcdGrove
end Perennial
