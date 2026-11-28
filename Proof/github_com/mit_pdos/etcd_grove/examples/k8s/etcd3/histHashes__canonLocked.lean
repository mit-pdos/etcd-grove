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
  · rw [if_neg (by simp), if_pos (decide_eq_true rfl)]
    fail "exit"
  · rw [if_pos (decide_eq_true rfl)]
    have Hnn := Hb rfl
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %lsl ⟨Hl, -⟩
    simp only [arrayLiteralSize1]
    wp_apply (wp_slice_append _ ts _ _ (DFrac.own 1)) $$ [$Hts $Hcap $Hl] as %tsl' ⟨Hts, Hcap, -⟩
    have Hm : 0 < hs.length - ts.length := by
      rcases Nat.eq_zero_or_pos (hs.length - ts.length) with h0 | h0
      · exfalso
        sorry
      · exact h0
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
