/- Lean-first (no Rocq counterpart). The proof of `pending.del`: the loop over the tester's keys;
after `j` of them the map has lost, and the changes have gained, the present keys in the range among
the first `j` (`delAll`), which do not include the `j`-th (the keys are distinct). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.pending__del
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.inRange

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand

/-- The `j`-th key is not among the first `j`. -/
theorem keyList_get_not_mem_take (j : Nat) (x : GoString) (h : keyList[j]? = some x) :
    x ∉ keyList.take j := by
  rcases j with _ | _ | _ | _ | _ | _ | j <;> simp [keyList] at h ⊢ <;> subst h <;> decide

theorem filter_take_succ (n : Nat) (x : GoString) (pr : GoString → Bool)
    (hx : keyList[n]? = some x) :
    (keyList.take (n + 1)).filter pr =
      (keyList.take n).filter pr ++ (if pr x then [x] else []) := by
  rw [List.take_add_one, hx, List.filter_append]
  cases h : pr x <;> simp [List.filter, h]

section model
variable [GooseExts]

/-- `del`'s test of a key. -/
def delPr (P : PendM) (endNil : Bool) (kk e : GoString) (x : GoString) : Bool :=
  (P.st !! x).isSome && inRangeM endNil kk e x

/-- The keys `del` has deleted after the first `j` of the tester's keys. -/
def delPre (P : PendM) (endNil : Bool) (kk e : GoString) (j : Nat) : List GoString :=
  (keyList.take j).filter (delPr P endNil kk e)

end model

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

theorem pending.del.wp_proof (wp_inRange : inRange.spec (GF := GF) (hG := hG)) :
    pending.del.spec (GF := GF) (hG := hG) := by
  intro p P key endk kk e dq dq'
  wp_start as ⟨Hp, Hk, He⟩
  iunfold ownPending at Hp
  icases Hp with ⟨%pv, Hp, %Hrev, Hm, Hcs, Hcap⟩
  ihave Hmi : (mvccrandInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iunfold mvccrandInit at Hmi
  icases Hmi with ⟨⟨%ks, #Hks, #Hksl⟩, -⟩
  ihave %Hksn := ownSlice_len $$ Hksl
  have hks6 : sint.Z ks.len = 6 := by
    have h := Hksn.1; simp only [keyList, List.length_cons, List.length_nil] at h
    have h4 : sint.nat ks.len = (sint.Z ks.len).toNat := rfl
    have := Hksn.2; omega
  wp_auto
  -- the loop: after `j` keys, `ds j` deleted
  ihave HI : (∃ (j : w64) (cs : GoSlice) (kv0 : GoString),
      "i" ∷ i_ptr ↦ j ∗
      "n" ∷ n_ptr ↦ W64 (delPre P (decide (endk = slice.nil)) kk e (sint.nat j)).length ∗
      "Hp" ∷ p ↦ { pv with changes' := cs } ∗
      "Hm" ∷ pv.st' ↦$ delAll (delPre P (decide (endk = slice.nil)) kk e (sint.nat j)) P.st ∗
      "Hcs" ∷ cs ↦* (P.chs ++
        (delPre P (decide (endk = slice.nil)) kk e (sint.nat j)).map delChange) ∗
      "Hcap" ∷ ownSliceCap change cs (DFrac.own 1) ∗ "k" ∷ k_ptr ↦ kv0 ∗
      "Hkey" ∷ key_ptr ↦ key ∗ "Hend" ∷ end_ptr ↦ endk ∗ "p" ∷ p_ptr ↦ p ∗
      "Hk" ∷ key ↦*{dq} kk ∗ "He" ∷ endk ↦*{dq'} e ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 6⌝ : IProp GF) $$ [i n Hp Hm Hcs Hcap k key «end» p Hk He]
  · iexists W64 0, pv.changes', _
    simp only [delPre, show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.filter_nil,
      List.map_nil, List.append_nil, List.length_nil]
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  by_cases Hlt : sint.Z j < sint.Z ks.len
  · -- an iteration
    rw [decide_eq_true Hlt]; simp only [↓reduceIte]
    have hj6 : sint.Z j < 6 := by rw [← hks6]; exact Hlt
    list_elem keyList (sint.nat j) as x
    have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z ks.len := ⟨Hj.1, Hlt⟩
    (try wp_auto)
    (try simp only [hb, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index ks (sint.Z j) keyList DFrac.discard x Hj.1 $$ [Hksl] as -
    · iframe #; ipureintro; exact Hx_lookup
    (try wp_auto)
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    have hx_nd : x ∉ delPre P (decide (endk = slice.nil)) kk e (sint.nat j) := fun h =>
      keyList_get_not_mem_take _ x Hx_lookup (List.mem_filter.1 h).1
    have hlk : delAll (delPre P (decide (endk = slice.nil)) kk e (sint.nat j)) P.st !! x =
        P.st !! x := by
      rw [delAll_lookup]; simp [hx_nd]
    wp_apply (wp_map_lookup2 go.string kvRec.ty pv.st' _ x (DFrac.own 1)) $$ [$Hm] as Hm
    rw [hlk]
    (try wp_auto)
    have hds : delPre P (decide (endk = slice.nil)) kk e (sint.nat (j + W64 1)) =
        delPre P (decide (endk = slice.nil)) kk e (sint.nat j) ++
          (if delPr P (decide (endk = slice.nil)) kk e x then [x] else []) := by
      unfold delPre; rw [hj1]; exact filter_take_succ _ x _ Hx_lookup
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
        have : W64 ((delPre P (decide (endk = slice.nil)) kk e (sint.nat j)).length + (0 + 1) :
            Nat) = W64 ((delPre P (decide (endk = slice.nil)) kk e (sint.nat j)).length : Nat) +
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
    have hj6 : sint.nat j = 6 := by
      have : ¬ sint.Z j < 6 := by rw [← hks6]; exact Hlt
      have h0 := Hj.2; have h4 : sint.nat j = (sint.Z j).toNat := rfl; rw [h4]; omega
    have htk : delPre P (decide (endk = slice.nil)) kk e 6 =
        P.delKeys (decide (endk = slice.nil)) kk e := rfl
    rw [hj6, htk]
    (try wp_auto)
    iapply HΦ
    iframe
    iunfold ownPending
    iexists { pv with changes' := cs }
    simp only [PendM.del]
    iframe
    ipureintro; exact Hrev

end proof

end mvccrand
end EtcdGrove
end Perennial
