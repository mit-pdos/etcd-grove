/-
Lean-first (no Rocq counterpart).

The proof of `(*histHashes).canonLocked`: the first loop walks `h`'s history back to a node in `is`
(or nil), keeping the nodes passed in `todo` (`todo[j]` holds the history less its last `j`
stores); the second re-interns them oldest first, `n` holding each time one more store of the
history (`intern`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histHashes__canonLocked
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histHashes__intern

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3

/-- A prefix one longer is the shorter one and the next element. -/
theorem take_succ_snoc {α : Type} (l : List α) (m : Nat) (h : m < l.length) :
    ∃ x, l.take (m + 1) = l.take m ++ [x] :=
  ⟨l[m], by rw [List.take_succ, List.getElem?_eq_getElem h]; rfl⟩

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- `hh.is[n]` (`hh.mu` held): some Boolean, the invariant kept. -/
theorem wp_hh_is (hh nn : Loc) :
    {{ hhInv (GF := GF) hh }}
      (App (App (Val (map.lookup1 (go.GoType.PointerType hnode.ty) go.bool))
        (App (Val (GoInstruction (GoLoad (go.GoType.MapType (go.GoType.PointerType hnode.ty) go.bool))))
          (Val #(structFieldRef histHashes go!"is" hh)))) (Val #nn))
    {{ (b : Bool), RET #b; hhInv hh }} := by
  iintro %Φ Hinv HΦ
  iunfold hhInv at Hinv
  icases Hinv with ⟨%mc, %mi, %mg, %C, %I, %G, Hc, Hi, Hg, Hci, Hgs⟩
  icases Hci with (%Hnil | ⟨HC, HI, HCs⟩)
  · obtain ⟨rfl, rfl⟩ := Hnil
    (try wp_auto)
    iapply HΦ
    iunfold hhInv
    iexists map.nil, map.nil, mg, C, I, G
    iframe
    ileft
    ipureintro; exact ⟨rfl, rfl⟩
  · (try wp_auto)
    wp_apply (wp_map_lookup1 _ _ mi I nn (DFrac.own 1)) $$ [$HI] as HI
    iapply HΦ
    iunfold hhInv
    iexists mc, mi, mg, C, I, G
    iframe
    iright
    iframe

theorem histHashes.canonLocked.wp_proof (wp_intern : histHashes.intern.spec (GF := GF) (hG := hG)) :
    histHashes.canonLocked.spec (GF := GF) (hG := hG) := by
  intro hh h hs
  wp_start as ⟨Hinv, #Hh, %Hlen⟩
  (try wp_auto)
  ihave HI : (∃ (tsl : GoSlice) (ts : List Loc) (nn : Loc),
      "todo" ∷ todo_ptr ↦ tsl ∗ "n" ∷ n_ptr ↦ nn ∗ "Hts" ∷ tsl ↦* ts ∗
      "Hcap" ∷ ownSliceCap Loc tsl (DFrac.own 1) ∗ "Hinv" ∷ hhInv hh ∗
      "#Hn" ∷ histOwn nn (hs.take (hs.length - ts.length)) ∗
      "#Htso" ∷ ([∗list] j ↦ t ∈ ts, histOwn t (hs.take (hs.length - j))) ∗
      "%Hk" ∷ ⌜ts.length ≤ hs.length⌝ : IProp GF) $$ [todo n Hinv]
  · iexists slice.nil, [], h
    iframe
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    isplitr
    · rw [show hs.take (hs.length - ([] : List Loc).length) = hs by simp]; iexact Hh
    isplitr
    · iapply BigSepL.bigSepL_nil.2; itrivial
    ipureintro; simp
  wp_for HI
  wp_join (Q := fun v => iprop(∃ b : Bool, ⌜v = #b⌝ ∗ hhInv hh ∗ hh_ptr ↦ hh ∗ n_ptr ↦ nn ∗
      ⌜b = true → nn ≠ null⌝)) with [Hinv hh n] as ⟨%b, %Hv, Hinv, hh, n, %Hb⟩
  · iexists false
    iframe
    ipureintro; exact ⟨rfl, nofun⟩
  · (try wp_auto)
    wp_apply (wp_hh_is hh nn) $$ [$Hinv] as %b Hinv
    (try wp_auto)
    iexists !b
    iframe
    ipureintro; exact ⟨rfl, fun _ => Hif⟩
  subst Hv
  cases b
  · rw [if_neg (by simp only [decide_eq_true_eq]; exact fun h => absurd (GoGlobalContext.intoVal_inj_bool h) (by decide)),
      if_pos (decide_eq_true rfl)]
    ihave %Hlts := ownSlice_len $$ Hts
    (try wp_auto)
    ihave HJ : (∃ (i : w64) (m : Loc) (k : Nat), "i" ∷ i_ptr ↦ i ∗ "n" ∷ n_ptr ↦ m ∗
        "Hinv" ∷ hhInv hh ∗ "#Hm" ∷ histOwn m (hs.take (hs.length - k)) ∗
        "%Hi" ∷ ⌜sint.Z i + 1 = k ∧ k ≤ ts.length⌝ : IProp GF) $$ [i n Hinv]
    · iexists _, nn, ts.length
      iframe
      isplitr
      · iexact Hn
      ipureintro; constructor <;> word
    wp_for HJ
    wp_if_destruct
    · have Hif' := of_decide_eq_true (GoGlobalContext.intoVal_inj_bool Hif)
      have Hik : k = sint.nat i + 1 := by word
      list_elem ts (sint.nat i) as t
      have Hb' : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z tsl.len := ⟨by word, by word⟩
      ihave #Ht := BigSepL.bigSepL_lookup Ht_lookup $$ Htso
      obtain ⟨x, hx⟩ := take_succ_snoc hs (hs.length - k) (by omega)
      ihave Ht2 : histOwn t (hs.take (hs.length - k) ++ [x]) $$ [Ht]
      · rw [← hx, show hs.length - k + 1 = hs.length - sint.nat i by omega]
        iexact Ht
      icases (histOwn_snoc t _ x).1 $$ Ht2 with ⟨%hn, #Hp, #Hs, %Hnl, -⟩
      iStructNamed Hp
      simp only [Hb', _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index _ (sint.Z i) ts _ t (by word) $$ [Hts] as Hts
      · isplit
        · iexact Hts
        · ipureintro; exact Ht_lookup
      (try simp only [Hb', _root_.and_self, ↓reduceIte])
      wp_apply wp_load_slice_index _ (sint.Z i) ts _ t (by word) $$ [Hts] as Hts
      · isplit
        · iexact Hts
        · ipureintro; exact Ht_lookup
      (try wp_auto)
      have Htl := List.length_take_le (hs.length - k) hs
      wp_apply (wp_intern hh m (hs.take (hs.length - k)) hn.st' x hn.n') $$ [$Hinv $Hm $Hs]
        as %c ⟨Hinv, #Hc⟩
      · ipureintro; rw [Hnl]; word
      (try wp_auto)
      wp_for_post
      iframe
      iexists _, c, sint.nat i
      iframe
      isplitr
      · rw [show hs.length - sint.nat i = hs.length - k + 1 by omega, hx]
        iexact Hc
      ipureintro; constructor <;> word
    · have Hif' : ¬ (sint.Z (W64 0) ≤ sint.Z i) := fun h => Hif (by rw [_root_.decide_eq_true h])
      have Hk0 : k = 0 := by word
      subst Hk0
      (try wp_auto)
      rw [show hs.take (hs.length - 0) = hs by simp]
      iapply HΦ
      iframe
  · rw [if_pos (decide_eq_true rfl)]
    have Hnn := Hb rfl
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %lsl ⟨Hl, -⟩
    simp only [arrayLiteralSize1]
    wp_apply (wp_slice_append _ ts _ _ (DFrac.own 1)) $$ [$Hts $Hcap $Hl] as %tsl' ⟨Hts, Hcap, -⟩
    obtain h0 | Hm := Nat.eq_zero_or_pos (hs.length - ts.length)
    · ihave Hn0 : histOwn nn [] $$ [Hn]
      · rw [show ([] : List GSt) = hs.take (hs.length - ts.length) by rw [h0, List.take_zero]]
        iexact Hn
      icases (histOwn_nil nn).1 $$ Hn0 with %Hnull
      exact absurd Hnull Hnn
    obtain ⟨x, hx⟩ := take_succ_snoc hs (hs.length - (ts.length + 1)) (by omega)
    ihave Hn2 : histOwn nn (hs.take (hs.length - (ts.length + 1)) ++ [x]) $$ [Hn]
    · rw [← hx, show hs.length - (ts.length + 1) + 1 = hs.length - ts.length by omega]
      iexact Hn
    icases (histOwn_snoc nn _ x).1 $$ Hn2 with ⟨%hn, #Hp, #Hs, %Hnl, #Hpr⟩
    iStructNamed Hp
    (try wp_auto)
    wp_for_post
    iframe
    iexists _, ts ++ [nn], hn.prev'
    iframe
    simp only [List.length_append, List.length_singleton]
    isplitr
    · iexact Hpr
    isplitr
    · iapply BigSepL.bigSepL_snoc.2
      iframe #
    ipureintro; omega

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
