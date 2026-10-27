/-
Lean-first (no Rocq counterpart). What `StartCluster` and (2026-10-20, W4) `StartClusterWitness`
share: the quiet logger is a raft `Logger`, maps of a list's keys, and list lemmas for their loops
(until 2026-10-20 in `StartCluster.lean`).
-/
module

public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.quietLogger__Debugf
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.quietLogger__Errorf
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.quietLogger__Infof
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.quietLogger__Warningf
public import RaftWitness.Proof.github_com.mit_pdos.etcd_grove.examples.kvwitness.Cluster

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]

/-- `quietLogger{}` is a raft `Logger`. -/
theorem qLogger_isLogger
    (wp_Debugf : quietLogger.Debugf.spec (GF := GF) (hG := hG))
    (wp_Errorf : quietLogger.Errorf.spec (GF := GF) (hG := hG))
    (wp_Infof : quietLogger.Infof.spec (GF := GF) (hG := hG))
    (wp_Warningf : quietLogger.Warningf.spec (GF := GF) (hG := hG)) :
    ⊢ isLogger (GF := GF) qLogger := by
  unfold isLogger
  iintro %meth %Hmeth %format %args
  simp only [logMethods, List.mem_cons, List.not_mem_nil, or_false] at Hmeth
  rcases Hmeth with rfl | rfl | rfl | rfl
  · dsimp only [qLogger, interface.mk]
    imodintro
    iintro %Φ - HΦ
    iapply (wp_Infof format args) $$ [] HΦ
    itrivial
  · dsimp only [qLogger, interface.mk]
    imodintro
    iintro %Φ - HΦ
    iapply (wp_Debugf format args) $$ [] HΦ
    itrivial
  · dsimp only [qLogger, interface.mk]
    imodintro
    iintro %Φ - HΦ
    iapply (wp_Warningf format args) $$ [] HΦ
    itrivial
  · dsimp only [qLogger, interface.mk]
    imodintro
    iintro %Φ - HΦ
    iapply (wp_Errorf format args) $$ [] HΦ
    itrivial

/-- The map of the keys `l`, each to `v` (`GMap.listToSet l` for `v = ()`). -/
def constMap {V : Type} (l : List w64) (v : V) : GMap w64 V :=
  match l with
  | [] => ∅
  | k :: l => GMap.insert k v (constMap l v)

theorem constMap_lookup_none {V : Type} (l : List w64) (v : V) (k : w64) (h : k ∉ l) :
    constMap l v !! k = none := by
  induction l with
  | nil => rfl
  | cons k' l IH =>
    simp only [List.mem_cons, not_or] at h
    show (GMap.insert k' v (constMap l v)) !! k = none
    rw [GMap.lookup_insert_ne _ _ (Ne.symm h.1)]
    exact IH h.2

theorem listToSet_constMap (l : List w64) : GMap.listToSet l = constMap l () := by
  induction l with
  | nil => rfl
  | cons k l IH => show GMap.insert k () (GMap.listToSet l) = _; rw [IH]; rfl

/-- A big separating conjunction over a `constMap` is one over its list. -/
theorem bigSepM_constMap {V : Type} (l : List w64) (v : V) (hnd : l.Nodup)
    (Φ : w64 → V → IProp GF) :
    ([∗map] k ↦ x ∈ constMap l v, Φ k x) ⊢ [∗list] k ∈ l, Φ k v := by
  induction l with
  | nil => iintro -; iapply (BigSepL.bigSepL_nil (Φ := fun _ k => Φ k v)).2; iempintro
  | cons k l IH =>
    have hk : k ∉ l := (List.nodup_cons.mp hnd).1
    rw [show constMap (k :: l) v = GMap.insert k v (constMap l v) from rfl]
    iintro H
    ihave ⟨H1, H2⟩ := (BigSepM.bigSepM_insert (Φ := Φ) (m := constMap l v) (i := k) (x := v)
      (constMap_lookup_none l v k hk)).1 $$ H
    iapply (BigSepL.bigSepL_cons (Φ := fun _ k => Φ k v)).2
    iframe H1
    iapply IH (List.nodup_cons.mp hnd).2 $$ H2

theorem constMap_lookup_isSome {V : Type} (l : List w64) (v : V) (k : w64) :
    (constMap l v !! k).isSome ↔ k ∈ l := by
  induction l with
  | nil =>
    simp only [List.not_mem_nil, iff_false]
    rw [show ((constMap [] v : GMap w64 V) !! k) = none from rfl]
    simp
  | cons k' l IH =>
    show (GMap.insert k' v (constMap l v) !! k).isSome ↔ _
    by_cases h : k' = k
    · subst h; rw [GMap.lookup_insert_eq]; simp
    · rw [GMap.lookup_insert_ne _ _ h, IH]
      simp [List.mem_cons, Ne.symm h]

theorem take_drop_ne (l : List w64) (hnd : l.Nodup) (n : Nat) (x y : w64)
    (hx : x ∈ l.take n) (hy : y ∈ l.drop n) : x ≠ y := by
  rw [← List.take_append_drop n l, List.nodup_append] at hnd
  exact hnd.2.2 x hx y hy

theorem drop_cons_of_getElem? (l : List w64) (n : Nat) (x : w64) (h : l[n]? = some x) :
    l.drop n = x :: l.drop (n + 1) := by
  have hn : n < l.length := (List.getElem?_eq_some_iff.mp h).1
  rw [List.drop_eq_getElem_cons hn]
  rw [List.getElem?_eq_getElem hn] at h
  rw [Option.some.inj h]

theorem take_succ_of_getElem? (l : List w64) (n : Nat) (x : w64) (h : l[n]? = some x) :
    l.take (n + 1) = l.take n ++ [x] := by
  rw [List.take_add_one, h]; rfl


end lemmas

end kvwitness
end EtcdGrove
end Perennial
