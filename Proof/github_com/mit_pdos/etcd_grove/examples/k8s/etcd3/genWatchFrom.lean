/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/genWatchFrom.lean`
(stage E of 7f-6). Lean-first (no Rocq counterpart).

The fifteen `pick`s, then each statement-level `if` joined (`wp_join`) at what the watch needs of
it: the mode draw below 7, a cached object at `2^62` or above dropped (G1), a relative RV drawn
only with a cached object, the RV parsed below `2^62 + 201` (`genWatchFrom` adds at most 201 to
the cached object's), the namespace and name among the workload's or the missing ones, the key one
`PrepareKey` takes under the prefix (decided on the finitely many keys), and the match and
initial-events options (`WatchInOk`, `kModeOk_of`'s premises).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.genWatchFrom
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.workloadKeys
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.workloadNodes
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.workloadApps
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.splitKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.storeKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.rvBytes
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.rvString
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.parseRV
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.pick

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section pure
variable [GooseExts]

/-- A namespace `genWatchFrom` may pick for the workload key `k`. -/
def nsCand (k v : GoString) : Prop := v = (splitKeyL k).1 ∨ v = go!"ns-nonexistent"

/-- A name `genWatchFrom` may pick for the workload key `k`. -/
def nameCand (k v : GoString) : Prop := v = (splitKeyL k).2 ∨ v = go!"pod-nonexistent"

/-- A watch key the generator builds: under the prefix, one `PrepareKey` takes, short. -/
def WKeyOk (w : GoString) : Prop :=
  go!"/objs/" <+: w ∧ (∀ r, (k8s.prepareKeyM go!"/objs" w r).isSome) ∧ w.length ≤ 2 ^ 20

theorem wkeyOk_cluster : WKeyOk go!"/objs/" :=
  ⟨by decide, fun r => by cases r <;> decide, by decide⟩

theorem wkeyOk_ns (k ns : GoString) (hk : k ∈ wksD) (hns : nsCand k ns) :
    WKeyOk (go!"/objs/" ++ ns) := by
  simp only [wksD, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl <;> rcases hns with rfl | rfl <;>
    exact ⟨by decide, fun r => by cases r <;> decide, by decide⟩

theorem wkeyOk_obj (k ns nm : GoString) (hk : k ∈ wksD) (hns : nsCand k ns) (hnm : nameCand k nm) :
    WKeyOk (storeKeyL (ns ++ go!"/" ++ nm)) := by
  simp only [wksD, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl <;> rcases hns with rfl | rfl <;> rcases hnm with rfl | rfl <;>
    exact ⟨by decide, fun r => by cases r <;> decide, by decide⟩

/-- What `genWatchFrom` has established of its record `y` once the key is set: a watch, no cached
object, not skipped, its key `WKeyOk`, its RV `rv`, the initial-events and match options unset. -/
def WK5 (rv : GoString) (y : Input) : Prop :=
  y.Kind' = W64 5 ∧ y.UseCached' = false ∧ y.Skip' = false ∧ WKeyOk y.WKey' ∧ y.MinRV' = rv

/-- `WK5`, the initial-events and match options still unset. -/
def WK (rv : GoString) (y : Input) : Prop := WK5 rv y ∧ y.SendInit' = W64 0 ∧ y.Match' = W64 0

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

set_option hygiene false in
/-- `L[I]` of the slice `sl ↦* L` (`Hs`), whose length is `hl`, as `v` (with `hm : v ∈ L`). -/
local macro "load_elem " L:term:max sl:ident hl:ident I:term:max Hs:ident " as " v:ident hm:ident :
    tactic => `(tactic| (
  have hb : 0 ≤ sint.Z $I ∧ sint.Z $I < sint.Z ($sl).len := by rw [$hl:ident]; constructor <;> word
  rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
  list_elem $L (sint.Z $I).toNat as $v
  wp_apply wp_load_slice_index _ (sint.Z $I) $L _ $v hb.1 $$ [$Hs:ident] as $Hs:ident
  · iframe; ipureintro; assumption
  have $hm : $v ∈ $L := List.mem_of_getElem? (by assumption)
  clear hb))

/-- A `wp_join` case at its join value: `True ∗ R` to `R`. -/
local macro "jfin" : tactic => `(tactic| ((try wp_auto); (try wp_join_done); (try (isplitl []; itrivial))))

/-- The cases of a `wp_join` (the goals `t` solves; the continuation, a wand, is left). -/
local macro "jcases " t:tacticSeq : tactic => `(tactic| all_goals (first | (($t); done) | skip))

set_option hygiene false in
/-- A record that changed none of `WK`'s fields of `y` (`Hy : WK rv y`). -/
local macro "wk_keep" : tactic => `(tactic| (
  jfin; iexists _; iframe; ipureintro
  simp only [WK, WK5] at Hy ⊢; exact Hy))

set_option maxHeartbeats 3200000 in
theorem genWatchFrom.wp_proof (wp_pick : pick.spec (GF := GF) (hG := hG))
    (wp_rvBytes : rvBytes.spec (GF := GF) (hG := hG))
    (wp_rvString : rvString.spec (GF := GF) (hG := hG))
    (wp_workloadKeys : workloadKeys.spec (GF := GF) (hG := hG))
    (wp_splitKey : splitKey.spec (GF := GF) (hG := hG))
    (wp_workloadNodes : workloadNodes.spec (GF := GF) (hG := hG))
    (wp_storeKey : storeKey.spec (GF := GF) (hG := hG))
    (wp_workloadApps : workloadApps.spec (GF := GF) (hG := hG))
    (wp_parseRV : parseRV.spec (GF := GF) (hG := hG)) :
    genWatchFrom.spec (GF := GF) (hG := hG) := by
  intro n id c hasC
  wp_start
  wp_auto
  wp_apply wp_pick _ (W64 10) (by decide)
  (try wp_auto)
  wp_apply wp_pick _ (W64 7) (by decide)
  (try wp_auto)
  wp_apply wp_pick _ (W64 6) (by decide)
  (try wp_auto)
  wp_apply wp_pick _ (W64 3) (by decide)
  (try wp_auto)
  wp_apply wp_pick _ (W64 200) (by decide)
  (try wp_auto)
  wp_apply wp_pick _ (W64 10) (by decide)
  (try wp_auto)
  wp_apply wp_pick _ (W64 4) (by decide)
  (try wp_auto)
  wp_apply wp_pick _ (W64 10) (by decide)
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
  wp_apply wp_pick _ (W64 2) (by decide)
  (try wp_auto)
  wp_apply wp_pick _ (W64 100) (by decide)
  (try wp_auto)
  -- the read-only locals, persistent (every join's cases read them)
  (try ipersist wl); (try ipersist m2); (try ipersist m3); (try ipersist d); (try ipersist kt)
  (try ipersist ki); (try ipersist sc); (try ipersist rc); (try ipersist fs); (try ipersist ls)
  (try ipersist ni); (try ipersist ai); (try ipersist bm); (try ipersist bh)
  (try ipersist watchList); (try ipersist id)
  -- `if watchList && m == 6 { m = m2 }`
  wp_join iprop(∃ mv : w64, m_ptr ↦ mv ∗ ⌜uint.nat mv < 7⌝) with [m]
  · wp_if_destruct
    · isplitr
      · itrivial
      iexists _; iframe; ipureintro; word
    · isplitl []
      · itrivial
      iexists _; iframe; ipureintro; word
  · iexists _; iframe; ipureintro; word
  iintro ⟨%mv, m, %Hmv⟩
  (try wp_auto)
  -- (G1) `if hasC && c.ResourceVersion >= 1<<62 { hasC = false }`
  wp_join iprop(∃ hc : Bool, hasC_ptr ↦ hc ∗ c_ptr ↦ c ∗
      ⌜hc = true → uint.Z c.ResourceVersion' < 2 ^ 62⌝) with [hasC c]
  jcases
    repeat' (first | wp_if_destruct | wp_auto)
    all_goals (
      jfin; iexists _; iframe; ipureintro
      intro h
      first | word | cases h)
  iintro ⟨%hc, hasC, c, %Hhc⟩
  (try wp_auto)
  -- `if !hasC && m >= 3 { m = m3 }`
  wp_join iprop(∃ mv : w64, m_ptr ↦ mv ∗
      ⌜uint.nat mv < 7 ∧ (3 ≤ uint.nat mv → hc = true)⌝) at next with [m]
  jcases
    cases hc
    all_goals repeat' (first | wp_if_destruct | wp_auto)
    all_goals (
      jfin; iexists _; iframe; ipureintro
      constructor <;> (try intro) <;> first | word | (cases hc <;> simp_all))
  iintro ⟨%mv', m, %Hmv'⟩
  (try wp_auto)
  -- the resource version
  wp_join iprop(∃ rvs : GoString, rv_ptr ↦ rvs ∗ m_ptr ↦ mv' ∗ c_ptr ↦ c ∗
      ⌜∃ r0 : w64, parseRVD rvs = some r0 ∧ uint.Z r0 < 2 ^ 62 + 201⌝) with [rv m c]
  jcases
    repeat' (first | wp_if_destruct | wp_auto | (wp_apply wp_rvBytes; (try wp_auto)) |
      (wp_apply wp_rvString; (try wp_auto)))
    all_goals (
      jfin; iexists _; iframe; ipureintro
      first
        | exact ⟨0, rfl, by decide⟩
        | exact ⟨_, parseRVD_rvBytes _, by word⟩
        | (refine ⟨_, parseRVD_rvStr _, ?_⟩
           simp only [eq_comm (a := true), decide_eq_true_eq] at *
           have hcT : hc = true := Hmv'.2 (by word)
           have := Hhc hcT
           word))
  iintro ⟨%rvs, rv, m, c, %Hrv⟩
  (try wp_auto)
  ipersist rv
  -- the key, its namespace and name
  wp_apply wp_workloadKeys as %ksl ⟨Hk, -⟩
  (try wp_auto)
  ihave %Hkl := ownSlice_len $$ Hk
  have hkl : ksl.len = W64 4 := by
    have := Hkl.1; simp only [List.length_cons, List.length_nil] at this; word
  load_elem wksD ksl hkl (n / W64 10 / W64 7 / W64 6 / W64 3 / W64 200 / W64 10 % W64 4) Hk as k hgk
  (try wp_auto)
  wp_apply wp_splitKey
  (try wp_auto)
  wp_join iprop(∃ nsv nmv : GoString, ns_ptr ↦ nsv ∗ name_ptr ↦ nmv ∗ ⌜nsCand k nsv ∧ nameCand k nmv⌝)
    with [ns name]
  jcases
    repeat' (first | wp_if_destruct | wp_auto)
    all_goals (
      jfin; iexists _, _; iframe; ipureintro
      simp [nsCand, nameCand])
  iintro ⟨%nsv, %nmv, ns, name, %Hnn⟩
  (try wp_auto)
  ipersist ns
  ipersist name
  wp_apply wp_workloadNodes as %nsl ⟨Hns, -⟩
  (try wp_auto)
  ihave %Hnsl := ownSlice_len $$ Hns
  have hnsl : nsl.len = W64 3 := by
    have := Hnsl.1; simp only [List.length_cons, List.length_nil] at this; word
  load_elem wndD nsl hnsl (W64 1 + n / W64 10 / W64 7 / W64 6 / W64 3 / W64 200 / W64 10 / W64 4 /
    W64 10 / W64 10 / W64 100 / W64 100 % W64 2) Hns as nd hnd
  (try wp_auto)
  irename «in» => Hin
  -- the key's scope
  wp_join iprop(∃ (y : Input), in_ptr ↦ y ∗ ⌜WK rvs y⌝) with [Hin]
  jcases
    repeat' (first | wp_if_destruct | wp_auto | (wp_apply wp_storeKey; (try wp_auto)))
    all_goals (
      jfin; iexists _; iframe; ipureintro
      refine ⟨⟨rfl, rfl, rfl, ?_, rfl⟩, rfl, rfl⟩
      first
        | exact wkeyOk_cluster
        | exact wkeyOk_ns k nsv hgk Hnn.1
        | exact wkeyOk_obj k nsv nmv hgk Hnn.1 Hnn.2)
  iintro ⟨%y, Hin, %Hy⟩
  (try wp_auto)
  -- `Recursive`, the field selector
  wp_join iprop(∃ (y : Input), in_ptr ↦ y ∗ ⌜WK rvs y⌝) with [Hin]
  jcases
    repeat' (first | wp_if_destruct | wp_auto)
    all_goals wk_keep
  iintro ⟨%y, Hin, %Hy⟩
  (try wp_auto)
  -- the label selector
  wp_join iprop(∃ (y : Input), in_ptr ↦ y ∗ ⌜WK rvs y⌝) with [Hin]
  jcases
    repeat' (first | wp_if_destruct | wp_auto)
    all_goals (
      first
        | wk_keep
        | (wp_apply wp_workloadApps as %asl ⟨Has, -⟩
           (try wp_auto)
           ihave %Hasl := ownSlice_len $$ Has
           have hasl : asl.len = W64 3 := by
             have := Hasl.1; simp only [List.length_cons, List.length_nil] at this; word
           load_elem wapD asl hasl (W64 1 + n / W64 10 / W64 7 / W64 6 / W64 3 / W64 200 / W64 10 /
             W64 4 / W64 10 / W64 10 / W64 100 / W64 100 / W64 2 % W64 2) Has as ap hap
           wk_keep))
  iintro ⟨%y, Hin, %Hy⟩
  (try wp_auto)
  -- `r, _ := parseRV(rv)`, then the initial-events and match options
  obtain ⟨r0, hr0, hr0b⟩ := Hrv
  wp_apply wp_parseRV as %r %err Hp
  isimp only [hr0] at Hp
  icases Hp with %Hp
  obtain ⟨-, hrr⟩ := Hp
  subst hrr
  (try wp_auto)
  (try ipersist r)
  wp_join iprop(∃ (y : Input), in_ptr ↦ y ∗ ⌜WK5 rvs y ∧
      WatchInOk y (uint.nat r) ∧ (y.SendInit' = W64 2 → y.Bookmarks' = true) ∧
      (y.SendInit' ≠ W64 2 → y.SendInit' = W64 1 ∨ 0 < uint.nat r)⌝) with [Hin]
  jcases
    repeat' (first | wp_if_destruct | wp_auto)
    all_goals (
      jfin; iexists _; iframe; ipureintro
      obtain ⟨h5, hs0, hm0⟩ := Hy
      refine ⟨h5, ?_⟩
      dsimp only [WatchInOk]
      (try simp only [hs0, hm0])
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> intro h <;>
        first
          | exact True.intro
          | rfl
          | (exfalso; exact h rfl)
          | (exfalso; exact absurd h (by decide))
          | (left; exact ⟨by simp, True.intro⟩)
          | (right; exact ⟨by word, True.intro⟩)
          | (left; exact True.intro)
          | (right; word))
  iintro ⟨%y, Hin, %Hy⟩
  (try wp_auto)
  -- the behaviour
  wp_join iprop(∃ (y : Input), in_ptr ↦ y ∗ ⌜WK5 rvs y ∧ WatchInOk y (uint.nat r) ∧
      (y.SendInit' = W64 2 → y.Bookmarks' = true) ∧
      (y.SendInit' ≠ W64 2 → y.SendInit' = W64 1 ∨ 0 < uint.nat r)⌝) with [Hin]
  jcases
    repeat' (first | wp_if_destruct | wp_auto)
    all_goals (
      jfin; iexists _; iframe; ipureintro
      simp only [WK5] at Hy ⊢; exact Hy)
  iintro ⟨%y, Hin, %Hy⟩
  (try wp_auto)
  iapply HΦ
  ipureintro
  obtain ⟨⟨h1, h2, h3, ⟨h4a, h4b, h4c⟩, h5⟩, hw, hb, hs⟩ := Hy
  refine ⟨h1, h2, ?_, fun _ => ⟨h4a, h4b _, h4c, r, by rw [h5]; exact hr0, by word, hw, hb, hs⟩⟩
  intro h; rw [h3] at h; cases h

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
