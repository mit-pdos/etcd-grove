/- Lean-first (no Rocq counterpart). The proof of `pending.del` (mvccrand's, over `keys`): proved. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.pending__del
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.inRange
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.LogLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull

section model
variable [GooseExts]

/-- `del`'s test of a key. -/
def delPr (P : PendM) (endNil : Bool) (kk e : GoString) (x : GoString) : Bool :=
  (P.st !! x).isSome && inRangeM endNil kk e x

/-- The keys `del` has deleted after the first `j` of the keys. -/
def delPre (ks : List GoString) (P : PendM) (endNil : Bool) (kk e : GoString) (j : Nat) :
    List GoString :=
  (ks.take j).filter (delPr P endNil kk e)

theorem delFilter_take_succ (ks : List GoString) (n : Nat) (x : GoString) (pr : GoString → Bool)
    (hx : ks[n]? = some x) :
    (ks.take (n + 1)).filter pr = (ks.take n).filter pr ++ (if pr x then [x] else []) := by
  rw [List.take_add_one, hx, List.filter_append]
  cases h : pr x <;> simp [List.filter, h]

theorem get_not_mem_take {ks : List GoString} (hnd : ks.Nodup) (j : Nat) (x : GoString)
    (h : ks[j]? = some x) : x ∉ ks.take j := by
  intro hm
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 h
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hm
  simp only [List.getElem_take] at hix
  have hi' : i < j := by simp at hi; omega
  have := (hnd.getElem_inj (hi := by omega) (hj := hj)).1 hix
  omega

end model

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

theorem pending.del.wp_proof
    (wp_inRange : inRange.spec (GF := GF) (hG := hG)) :
    pending.del.spec (GF := GF) (hG := hG) := by
  intro p P keys ks dks key endk kk e dq dq' hsorted
  wp_start as ⟨Hp, Hks, Hk, He⟩
  iunfold ownPending at Hp
  icases Hp with ⟨%pv, Hp, %Hrev, Hm, Hcs, Hcap⟩
  have hnd : ks.Nodup := nodup_of_sorted hsorted
  ihave %Hksn := ownSlice_len $$ Hks
  wp_auto
  ihave HI : (∃ (j : w64) (cs : GoSlice) (kv0 : GoString),
      "i" ∷ i_ptr ↦ j ∗
      "n" ∷ n_ptr ↦ W64 (delPre ks P (decide (endk = slice.nil)) kk e (sint.nat j)).length ∗
      "Hp" ∷ p ↦ { pv with changes' := cs } ∗
      "Hm" ∷ pv.st' ↦$ delAll (delPre ks P (decide (endk = slice.nil)) kk e (sint.nat j)) P.st ∗
      "Hcs" ∷ cs ↦* (P.chs ++
        (delPre ks P (decide (endk = slice.nil)) kk e (sint.nat j)).map delChange) ∗
      "Hcap" ∷ ownSliceCap change cs (DFrac.own 1) ∗ "k" ∷ k_ptr ↦ kv0 ∗
      "Hkey" ∷ key_ptr ↦ key ∗ "Hend" ∷ end_ptr ↦ endk ∗ "p" ∷ p_ptr ↦ p ∗
      "Hk" ∷ key ↦*{dq} kk ∗ "He" ∷ endk ↦*{dq'} e ∗ "Hks" ∷ keys ↦*{dks} ks ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z keys.len⌝ : IProp GF)
      $$ [i n Hp Hm Hcs Hcap k key «end» p Hk He Hks]
  · iexists W64 0, pv.changes', _
    simp only [delPre, show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.filter_nil,
      List.map_nil, List.append_nil, List.length_nil]
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  by_cases Hlt : sint.Z j < sint.Z keys.len
  · -- an iteration
    rw [decide_eq_true Hlt]; simp only [↓reduceIte]
    have hjl : sint.nat j < ks.length := by
      have : sint.nat j = (sint.Z j).toNat := rfl
      have : sint.nat keys.len = (sint.Z keys.len).toNat := rfl
      omega
    obtain ⟨x, Hx_lookup⟩ : ∃ x, ks[sint.nat j]? = some x := ⟨_, List.getElem?_eq_getElem hjl⟩
    have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z keys.len := ⟨Hj.1, Hlt⟩
    (try wp_auto)
    (try simp only [hb, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index keys (sint.Z j) ks dks x Hj.1 $$ [Hks] as Hks
    · iframe; ipureintro; exact Hx_lookup
    (try wp_auto)
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    have hx_nd : x ∉ delPre ks P (decide (endk = slice.nil)) kk e (sint.nat j) := fun h =>
      get_not_mem_take hnd _ x Hx_lookup (List.mem_filter.1 h).1
    have hlk : delAll (delPre ks P (decide (endk = slice.nil)) kk e (sint.nat j)) P.st !! x =
        P.st !! x := by
      rw [delAll_lookup]; simp [hx_nd]
    wp_apply (wp_map_lookup2 go.string kvRec.ty pv.st' _ x (DFrac.own 1)) $$ [$Hm] as Hm
    rw [hlk]
    (try wp_auto)
    have hds : delPre ks P (decide (endk = slice.nil)) kk e (sint.nat (j + W64 1)) =
        delPre ks P (decide (endk = slice.nil)) kk e (sint.nat j) ++
          (if delPr P (decide (endk = slice.nil)) kk e x then [x] else []) := by
      unfold delPre; rw [hj1]; exact delFilter_take_succ ks _ x _ Hx_lookup
    have hj2 : sint.Z (j + W64 1) ≤ sint.Z keys.len := by word
    wp_if_destruct
    · -- present: the range check
      wp_apply wp_inRange key endk kk e x dq dq' $$ [$Hk $He] as ⟨Hk, He⟩
      (try wp_auto)
      cases hin : inRangeM (decide (endk = slice.nil)) kk e x
      rotate_left
      · -- in the range: deleted
        have hpr : delPr P (decide (endk = slice.nil)) kk e x = true := by
          simp only [delPr, Hif, hin, Bool.and_self]
        (try wp_auto)
        wp_apply (wp_mapDelete pv.st' _ x go.string kvRec.ty) $$ [$Hm] as Hm
        (try wp_auto)
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %osl ⟨Hosl, -⟩
        (try wp_auto)
        wp_apply wp_slice_append $$ [$Hcs $Hcap $Hosl] as %cs' ⟨Hcs, Hcap, -⟩
        (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, cs', x
        rw [hds]
        simp only [hpr, ↓reduceIte, List.map_append, List.map_cons, List.map_nil,
          List.append_assoc, List.length_append, List.length_cons, List.length_nil]
        rw [delAll_append]
        have : W64 ((delPre ks P (decide (endk = slice.nil)) kk e (sint.nat j)).length + (0 + 1) :
            Nat) = W64 ((delPre ks P (decide (endk = slice.nil)) kk e (sint.nat j)).length : Nat) +
              W64 1 := by word
        rw [this]
        iframe
        ipureintro; constructor <;> word
      · have hpr : delPr P (decide (endk = slice.nil)) kk e x = false := by
          simp only [delPr, hin, Bool.and_false]
        (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, cs, x
        rw [hds]
        simp only [hpr, Bool.false_eq_true, ↓reduceIte, List.append_nil]
        iframe
        ipureintro; constructor <;> word
    · have hpr : delPr P (decide (endk = slice.nil)) kk e x = false := by
        have hpf : (P.st !! x).isSome = false := by simpa using Hif
        simp only [delPr, hpf, Bool.false_and]
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, cs, x
      rw [hds]
      simp only [hpr, Bool.false_eq_true, ↓reduceIte, List.append_nil]
      iframe
      ipureintro; constructor <;> word
  · -- the loop's end
    rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hjn : sint.nat j = ks.length := by
      have h4 : sint.nat j = (sint.Z j).toNat := rfl
      have : sint.nat keys.len = (sint.Z keys.len).toNat := rfl
      omega
    have htk : delPre ks P (decide (endk = slice.nil)) kk e ks.length =
        P.delKeys ks (decide (endk = slice.nil)) kk e := by
      unfold delPre; rw [List.take_length]; rfl
    rw [hjn, htk]
    (try wp_auto)
    iapply HΦ
    iframe
    iunfold ownPending
    iexists { pv with changes' := cs }
    simp only [PendM.del]
    iframe
    ipureintro; exact Hrev

end proof

end mvccfull
end EtcdGrove
end Perennial
