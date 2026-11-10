module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.genList
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.splitKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.storeKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.pick
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.workloadNodes
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.workloadApps
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.minRV
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.parseRV

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- What `genList` keeps of its input `x` and has established of the list `y` so far. -/
private def LK (x y : Input) : Prop :=
  y.Key' = x.Key' ∧ y.UID' = x.UID' ∧ y.Node' = x.Node' ∧ y.App' = x.App' ∧ y.Val' = x.Val' ∧
    y.UseCached' = x.UseCached' ∧ y.Kind' = W64 4 ∧ go!"/objs/" <+: y.ListKey' ∧
    (∀ r, (k8s.prepareKeyM go!"/objs" y.ListKey' r).isSome) ∧ y.ListKey'.length ≤ 2 ^ 20 ∧
    (y.Match' = W64 0 ∨ y.Match' = W64 1 ∨ y.Match' = W64 2) ∧ 0 ≤ sint.Z y.Limit'

/-- The input `genList` returns is one `Gen` may return. -/
private theorem lk_genIn (x y : Input) (hy : LK x y) (hk : x.Key' ∈ wkKeysL)
    (hu : x.UID'.length < 256) (hn : x.Node'.length < 256) (ha : x.App'.length < 256)
    (hv : x.Val'.length ≤ 2 ^ 20) (hr : ∃ k, parseRVD y.MinRV' = some k ∧ uint.Z k < 2 ^ 63) :
    GenIn y ∧ y.UseCached' = x.UseCached' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hy
  refine ⟨⟨⟨h1 ▸ hk, h2 ▸ hu, h3 ▸ hn, h4 ▸ ha, hr, fun _ => ⟨h11, h8, h12, h9 _, h10⟩⟩, ?_,
    h5 ▸ hv, ?_⟩, h6⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr h7)))
  · intro _ h; rw [h7] at h; exact absurd h (by decide)

set_option hygiene false in
/-- `return in`: the final record is `Gen`'s. -/
local macro "gl_fin" : tactic => `(tactic| (
  (try wp_auto); iapply HΦ; ipureintro
  refine lk_genIn x _ ?_ hk hu hn ha hv ⟨k, ?_, hk2⟩
  · simp only [LK] at Hy ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := Hy
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ?_, ?_⟩
    · first | exact h11 | simp
    · first | exact h12 | word
  · simp only []; exact hk1))

set_option hygiene false in
/-- `LK x y` of the record after the list key is set (the first join). -/
local macro "lk_key" : tactic => `(tactic| (
  simp only [LK]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hm, hl⟩ <;> (try trivial) <;>
  (simp only [wkKeysL, List.mem_cons, List.not_mem_nil, or_false] at hk
   rcases hk with h | h | h | h <;> (try rw [h]) <;>
     first | decide | (intro r; cases r <;> decide))))

set_option hygiene false in
/-- `LK x y'` of a record that changed none of `LK`'s fields of `y` (`Hy : LK x y`). -/
local macro "lk_keep" : tactic => `(tactic| (
  (try wp_auto); (try wp_join_done); iexists _; iframe; ipureintro
  simp only [LK] at Hy ⊢; exact Hy))

set_option maxHeartbeats 1600000 in
theorem genList.wp_proof (wp_splitKey : splitKey.spec (GF := GF) (hG := hG))
    (wp_storeKey : storeKey.spec (GF := GF) (hG := hG))
    (wp_pick : pick.spec (GF := GF) (hG := hG))
    (wp_workloadNodes : workloadNodes.spec (GF := GF) (hG := hG))
    (wp_workloadApps : workloadApps.spec (GF := GF) (hG := hG))
    (wp_minRV : minRV.spec (GF := GF) (hG := hG))
    (wp_parseRV : parseRV.spec (GF := GF) (hG := hG)) :
    genList.spec (GF := GF) (hG := hG) := by
  intro n x c hasC hk hu hn ha hv hm hl
  wp_start
  wp_auto
  wp_apply wp_splitKey
  (try wp_auto)
  wp_apply wp_pick _ (W64 4) (by decide)
  (try wp_auto)
  wp_apply wp_pick _ (W64 10) (by decide)
  (try wp_auto)
  wp_apply wp_pick _ (W64 100) (by decide)
  (try wp_auto)
  wp_apply wp_pick _ (W64 100) (by decide)
  (try wp_auto)
  wp_apply wp_pick _ (W64 2) (by decide)
  (try wp_auto)
  wp_apply wp_pick _ (W64 2) (by decide)
  (try wp_auto)
  wp_apply wp_pick _ (W64 100) (by decide)
  (try wp_auto)
  wp_apply wp_pick _ (W64 200) (by decide)
  (try wp_auto)
  wp_apply wp_pick _ (W64 4) (by decide)
  (try wp_auto)
  wp_apply wp_pick _ (W64 100) (by decide)
  (try wp_auto)
  irename «in» => Hin
  wp_join iprop(∃ (y : Input), in_ptr ↦ y ∗ ns_ptr ↦ (splitKeyL x.Key').1 ∗
      sc_ptr ↦ (n % W64 4) ∗ ⌜LK x y⌝) with [Hin ns sc] as ⟨%y, Hin, ns, sc, %Hy⟩
  · (try wp_auto)
    iexists _; iframe; ipureintro; lk_key
  · wp_if_destruct
    · wp_apply wp_storeKey
      (try wp_auto)
      (try wp_join_done); iexists _; iframe; ipureintro; lk_key
    · (try wp_auto)
      (try wp_join_done); iexists _; iframe; ipureintro; lk_key
  wp_apply wp_workloadNodes as %nsl ⟨Hns, -⟩
  (try wp_auto)
  ihave %Hnsl := ownSlice_len $$ Hns
  have hnsl : nsl.len = W64 3 := by
    have := Hnsl.1; simp only [List.length_cons, List.length_nil] at this; word
  have hi : 0 ≤ sint.Z (W64 1 + n / W64 4 / W64 10 / W64 100 / W64 100 % W64 2) ∧
      sint.Z (W64 1 + n / W64 4 / W64 10 / W64 100 / W64 100 % W64 2) < sint.Z nsl.len := by
    rw [hnsl]; constructor <;> word
  rw [ite_eq_left_of_eq_true _ _ (eq_true hi)]
  list_elem wndD (sint.Z (W64 1 + n / W64 4 / W64 10 / W64 100 / W64 100 % W64 2)).toNat as nd
  wp_apply wp_load_slice_index _ _ wndD _ nd hi.1 $$ [Hns] as Hns
  · iframe; ipureintro; exact Hnd_lookup
  (try wp_auto)
  wp_join iprop(∃ (y : Input), in_ptr ↦ y ∗ fs_ptr ↦ (n / W64 4 / W64 10 % W64 100) ∗ ⌜LK x y⌝)
    with [Hin fs] as ⟨%y, Hin, fs, %Hy⟩
  · lk_keep
  · repeat' wp_if_destruct
    all_goals lk_keep
  wp_join iprop(∃ (y : Input), in_ptr ↦ y ∗ ⌜LK x y⌝) with [Hin ai] as ⟨%y, Hin, %Hy⟩
  · wp_apply wp_workloadApps as %asl ⟨Has, -⟩
    (try wp_auto)
    ihave %Hasl := ownSlice_len $$ Has
    have hasl : asl.len = W64 3 := by
      have := Hasl.1; simp only [List.length_cons, List.length_nil] at this; word
    have hi : 0 ≤ sint.Z (W64 1 + n / W64 4 / W64 10 / W64 100 / W64 100 / W64 2 % W64 2) ∧
        sint.Z (W64 1 + n / W64 4 / W64 10 / W64 100 / W64 100 / W64 2 % W64 2) < sint.Z asl.len := by
      rw [hasl]; constructor <;> word
    rw [ite_eq_left_of_eq_true _ _ (eq_true hi)]
    list_elem wapD (sint.Z (W64 1 + n / W64 4 / W64 10 / W64 100 / W64 100 / W64 2 % W64 2)).toNat
      as ap
    wp_apply wp_load_slice_index _ _ wapD _ ap hi.1 $$ [Has] as Has
    · iframe; ipureintro; exact Hap_lookup
    lk_keep
  · lk_keep
  wp_apply wp_minRV
  (try wp_auto)
  obtain ⟨k, hk1, hk2⟩ := minRVL_ok (n / W64 4 / W64 10 / W64 100 / W64 100 / W64 2 / W64 2 % W64 100)
    (n / W64 4 / W64 10 / W64 100 / W64 100 / W64 2 / W64 2 / W64 100 % W64 200 + W64 1) c hasC
    (by word)
  wp_if_destruct
  all_goals (try wp_apply wp_parseRV as %r %err -)
  all_goals (repeat' wp_if_destruct)
  all_goals gl_fin

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
