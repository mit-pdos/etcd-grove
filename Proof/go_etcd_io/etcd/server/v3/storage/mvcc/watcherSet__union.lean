/-
Proof of `Spec/.../mvcc/watcherSet__union.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherSet__union
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherSet__add

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.watcherSet.union.wp_proof
    (hAdd : mvcc.watcherSet.add.spec (GF := GF) (hG := hG)) :
    mvcc.watcherSet.union.spec (GF := GF) (hG := hG) := by
  intro m S m' S'
  wp_start as ⟨Hm, Hm', %Hdisj⟩
  wp_auto
  wp_func_lits
  iunfold mvcc.ownWatcherSetOpt at Hm'
  icases Hm' with (%Hnil | Hm')
  · obtain ⟨rfl, rfl⟩ := Hnil
    wp_auto
    iapply HΦ
    rw [GMap.map_union_empty]
    iframe Hm
    iunfold mvcc.ownWatcherSetOpt
    ileft; ipureintro; exact ⟨rfl, rfl⟩
  iunfold mvcc.ownWatcherSet at Hm'
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List Loc) (i : Int) => iprop(∃ (x : Loc),
      "wa" ∷ wa_ptr ↦ x ∗
      "w" ∷ w_ptr ↦ m ∗
      "Hm" ∷ mvcc.ownWatcherSet m (S ∪ mvcc.upTo keys i.toNat S') ∗
      "%Hi" ∷ ⌜0 ≤ i⌝)) $$ Hm'
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [wa w Hm]
  · iexists _
    simp only [named]
    iframe wa w
    rw [Int.toNat_zero, mvcc.upTo_zero, GMap.map_union_empty]
    iframe Hm
    ipureintro; omega
  isplitr
  · imodintro
    iintro %i %key %v ⟨%Hkey, %Hv⟩ HP
    iNamed HP
    obtain ⟨Hup, Hnone⟩ := mvcc.upTo_succ keys S' i.toNat key Hkey Hknodup Hv
    wp_auto
    (try wp_auto)
    wp_apply hAdd $$ [$Hm] as Hm
    · ipureintro
      rw [GMap.lookup_union_None]
      refine ⟨?_, Hnone⟩
      cases h : S !! key with
      | none => rfl
      | some _ => exact absurd (Hdisj key (by rw [h]; rfl) (by rw [Hv]; rfl)) id
    unfold forMapPostcondition
    iright; ileft
    isplitl []
    · ipureintro; rfl
    iexists _
    simp only [named]
    iframe wa w
    rw [show (i + 1).toNat = i.toNat + 1 by omega, Hup, ← GMap.insert_union_r]
    · iframe Hm
      ipureintro; omega
    cases h : S !! key with
    | none => rfl
    | some _ => exact absurd (Hdisj key (by rw [h]; rfl) (by rw [Hv]; rfl)) id
  iintro ⟨%x, wa, w, Hm, %Hi⟩ Hm'
  rw [show ((S'.size : Int)).toNat = keys.length by omega, mvcc.upTo_all keys S' Hkset]
  wp_auto
  iapply HΦ
  iframe Hm
  iunfold mvcc.ownWatcherSetOpt
  iright
  iunfold mvcc.ownWatcherSet
  iexact Hm'

end proof

end EtcdGrove
end Perennial
