/-
Proof of `Spec/.../mvcc/watcherGroup__contains.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__contains
public import Spec.go_etcd_io.etcd.pkg.v3.adt.NewStringAffinePoint
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Intersects
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

open Classical in
theorem mvcc.watcherGroup.contains.wp_proof
    (hPoint : adt.NewStringAffinePoint.spec (GF := GF) (hG := hG))
    (hInter : adt.intervalTree.Intersects.spec (GF := GF) (hG := hG)) :
    mvcc.watcherGroup.contains.spec (GF := GF) (hG := hG) := by
  intro wg W key
  wp_start as Hg
  iunfold mvcc.ownWatcherGroup at Hg
  icases Hg with ⟨%km, %ws, %t, %KM, %L, Hg⟩
  iNamed Hg
  iunfold mvcc.ownKeyMap at Hkm
  icases Hkm with ⟨Hkm, %Hdom, Hsets⟩
  wp_auto
  wp_apply wp_map_lookup2 $$ Hkm as Hkm
  ihave Hkm : mvcc.ownKeyMap km KM W $$ [Hkm Hsets]
  · iunfold mvcc.ownKeyMap
    iframe Hkm Hsets
    ipureintro; exact Hdom
  cases hk : KM !! key with
  | some m0 =>
    simp only [Option.isSome_some, _root_.decide_true]
    wp_auto
    obtain ⟨w, r, hw, he, hkey⟩ := (Hdom key).1 (by rw [hk]; rfl)
    rw [_root_.decide_eq_true ⟨w, r, hw, (mvcc.covers_none r key he).2 hkey.symm⟩]
    iapply HΦ
    iapply mvcc.ownWatcherGroup_intro wg W km ws t KM L HL
    iframe Hwg Hws Hfixed Hivt Hranges Hkm
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, _root_.decide_false]
    wp_auto
    wp_apply hPoint key
    wp_apply hInter $$ [$Hivt] as Hivt
    have Hst := mvcc.stab_point_ne_nil_iff W L HL.2 key
    have Hres : (!decide (adt.stab (key, key ++ go!"\x00") L = [])) =
        decide (∃ w r, W !! w = some r ∧ r.covers key = true) := by
      have hiff : adt.stab (key, key ++ go!"\x00") L ≠ [] ↔
          ∃ w r, W !! w = some r ∧ r.covers key = true := by
        rw [Hst]
        constructor
        · rintro ⟨w, r, e, hw, -, hc⟩; exact ⟨w, r, hw, hc⟩
        · rintro ⟨w, r, hw, hc⟩
          cases he : r.end? with
          | none =>
            exfalso
            have := (Hdom key).2 ⟨w, r, hw, he, ((mvcc.covers_none r key he).1 hc).symm⟩
            rw [hk] at this; cases this
          | some e => exact ⟨w, r, e, hw, he, hc⟩
      by_cases h : adt.stab (key, key ++ go!"\x00") L = []
      · rw [_root_.decide_eq_true h, _root_.decide_eq_false (fun h' => hiff.2 h' h)]; rfl
      · rw [_root_.decide_eq_false h, _root_.decide_eq_true (hiff.1 h)]; rfl
    rw [show (key ++ [0#8] : GoString) = key ++ go!"\x00" from rfl, Hres]
    iapply HΦ
    iapply mvcc.ownWatcherGroup_intro wg W km ws t KM L HL
    iframe Hwg Hws Hfixed Hivt Hranges Hkm

end proof

end EtcdGrove
end Perennial
