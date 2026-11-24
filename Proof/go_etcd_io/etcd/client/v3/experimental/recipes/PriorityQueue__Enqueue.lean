/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/PriorityQueue__Enqueue.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.PriorityQueue__Enqueue
public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.newSequentialKV
public import Perennial.Proof.fmt.Link
public import Proof.fmt.SprintfPure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

theorem PriorityQueue.Enqueue.wp_proof (hNSK : newSequentialKV.spec (GF := GF) (hG := hG)) :
    PriorityQueue.Enqueue.spec (GF := GF) (hG := hG) := by
  intro q client key val pr lo
  wp_start as ⟨#Hq, #Hlo, %Hv⟩
  iunfold isPriorityQueue at Hq
  icases Hq with ⟨#Hqc, -, #Hqk, #Hcl, %Hkl⟩
  ihave ⟨%kv, #Hkvf, #Hkv⟩ := isEtcdRecipesClient_kv $$ Hcl
  wp_auto
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %sla ⟨Hargs, -⟩
  (try wp_auto)
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_apply fmt.wp_Sprintf_pure _root_.Perennial.fmt.wp_Sprintf go!"%s%05d"
    [.dir none _root_.Perennial.fmt.verb_s, .dir (some 5) _root_.Perennial.fmt.verb_d] _ _ _ _ (by fmt_encode) ?fits ?pa
    $$ [$Hfmt $Hargs] as %pfx ⟨Hargs, %Hpfx⟩
  case pa =>
    rw [show sint.nat (W64 (0 + 1)) = 1 by rfl]
    simp only [List.set_cons_succ, List.set_cons_zero]
    exact .str _ _ _ (.int _ _ _ _ (.uint16 pr) .nil)
  case fits => fmt_fits
  have Hpfx' : pfx = (key ++ go!"/") ++ _root_.Perennial.fmt.padZeros 5 (_root_.Perennial.fmt.decimal (uint.Z pr)) := by
    rw [Hpfx]
    simp (config := { decide := true }) [_root_.Perennial.fmt.dirOutFn, _root_.Perennial.fmt.render, _root_.Perennial.fmt.decimalPad_of_nonneg 5 (show 0 ≤ uint.Z pr by word)]
  subst Hpfx'
  (try wp_auto)
  wp_apply hNSK kv [] _ val lo $$ [$Hpkg $Hkv $Hlo] as %rk %err Hres
  · ipureintro
    refine ⟨List.nil_prefix, List.nil_prefix, ?_, Hv⟩
    have h0 : 0 ≤ uint.Z pr ∧ uint.Z pr < 2 ^ 16 := by word
    have hp : (uint.Z pr).natAbs < 10 ^ 5 := by omega
    have := _root_.Perennial.fmt.length_decimalNat_le _ 5 (by omega) hp
    unfold _root_.Perennial.fmt.decimal
    rw [if_neg (by omega)]
    generalize _root_.Perennial.fmt.decimalNat (uint.Z pr).natAbs = D at this ⊢
    simp [_root_.Perennial.fmt.length_padZeros]; word
  icases Hres with (⟨%Heq, %k, %g, %r, -, #Hr, #Hc, %Hrr⟩ | %Hne)
  · subst Heq
    (try wp_auto)
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists k, g, r
    iframe Hr Hc
    ipureintro; exact ⟨Hrr.1, Hrr.2.1, Hrr.2.2.1⟩
  · (try wp_auto)
    iapply HΦ
    iright
    ipureintro; exact Hne.1

end proof

end recipes
end EtcdGrove
end Perennial
