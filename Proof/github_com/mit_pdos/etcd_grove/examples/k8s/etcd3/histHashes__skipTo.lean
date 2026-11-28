/-
Lean-first (no Rocq counterpart).

The proof of `(*histHashes).skipTo`: at or beyond `t`, `c` itself (`skipToL_le`); otherwise, `hh.mu`
held, `base` is `c`'s history's canonical node, `gaps[base]` (taken out of the map, or none) holds the
nodes of `base`'s history with one, two, ... foreign stores appended (`gapsOwn`: the same history as
`c`'s, by `histOwn_agree_len`, so its last store `c`'s store, by `HWf`), grown by `intern` up to
`t - rv` nodes and put back; node `t - rv - 1` holds `skipToL`'s history (`repeat_foreignL_gaps`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histHashes__skipTo
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histHashes__canonLocked
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histHashes__intern
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histLen

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3

section pure
variable [GooseExts]

/-- One more foreign store. -/
theorem gapsL_succ (s : GSt) (len j : Nat) :
    gapsL s len (j + 1) = gapsL s len j ++ [⟨s.items, W64 ((len + j + 1 : Nat) : Int)⟩] := by
  simp [gapsL, List.range_succ]

/-- **`skipToL`'s stores are `gapsL`'s** (a well-formed configuration). -/
theorem repeat_foreignL_gaps (H : HSt) (hw : HWf H) (j : Nat) (hj : H.hist.length + j < 2 ^ 64) :
    Nat.repeat k8s_dist.foreignL j H =
      ⟨⟨H.st.items, W64 ((H.hist.length + j : Nat) : Int)⟩, H.hist ++ gapsL H.st H.hist.length j⟩ := by
  induction j with
  | zero =>
    obtain ⟨⟨items, rv⟩, hist⟩ := H
    simp only [HWf] at hw
    simp only [Nat.repeat, Nat.add_zero, gapsL, List.range_zero, List.map_nil, List.append_nil]
    have : rv = W64 ((hist.length : Nat) : Int) := by rw [hw.1]; word
    rw [← this]
  | succ j ih =>
    simp only [Nat.repeat]
    rw [ih (by omega)]
    simp only [k8s_dist.foreignL, gapsL_succ, List.append_assoc]
    have : W64 ((H.hist.length + j : Nat) : Int) + W64 1 = W64 ((H.hist.length + (j + 1) : Nat) : Int) := by
      word
    rw [this, show H.hist.length + j + 1 = H.hist.length + (j + 1) by omega]

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem histHashes.skipTo.wp_proof
    (wp_canonLocked : histHashes.canonLocked.spec (GF := GF) (hG := hG))
    (wp_intern : histHashes.intern.spec (GF := GF) (hG := hG))
    (wp_histLen : histLen.spec (GF := GF) (hG := hG)) :
    histHashes.skipTo.spec (GF := GF) (hG := hG) := by
  intro hh c g t
  wp_start as ⟨#Hhh, #Hc, %Hpre⟩
  obtain ⟨Hwf, Ht⟩ := Hpre
  unfold cfgOwn
  icases Hc with ⟨#Hcst, #Hch, #Hcp, %Hchl⟩
  iunfold storeOwn at Hcst
  icases Hcst with ⟨#Hitems, %Hrv⟩
  (try wp_auto)
  wp_if_destruct
  · -- t ≤ rv: c itself
    (try wp_auto)
    iapply HΦ
    rw [k8s_dist.skipToL_le _ _ (by rw [← Hrv]; word)]
    unfold cfgOwn storeOwn
    iframe
    iframe #
    ipureintro; exact ⟨Hrv, Hchl⟩
  obtain ⟨hs0, x0, Hsnoc⟩ : ∃ hs0 x0, g.st.hist = hs0 ++ [x0] := by
    rcases nil_or_snoc g.st.hist with h | h
    · have := Hwf.2; rw [h] at this; simp at this
    · exact h
  wp_if_destruct
  · -- a nil history: impossible (`HWf`: a store in it)
    rw [Hsnoc] at *
    icases (histOwn_snoc _ hs0 x0).1 $$ Hch with ⟨%hn, Hp, -⟩
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
    exact absurd Hif Hnn
  done

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
