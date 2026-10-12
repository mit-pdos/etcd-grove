/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.kvSortByMod__Less

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.kvSortByMod.Less.wp_proof : txn.kvSortByMod.Less.spec (GF := GF) (hG := hG) := by
  intro sp ks sl l dq i j a b
  wp_start as ⟨#Hsp, #Hks, Hs, Hkvs, %Hij⟩
  wp_auto
  obtain ⟨hi0, hj0, ha, hb, hoka, hokb⟩ := Hij
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  simp only [List.length_map] at Hl
  have hilt : sint.nat i < l.length := (List.getElem?_eq_some_iff.1 ha).1
  have hjlt : sint.nat j < l.length := (List.getElem?_eq_some_iff.1 hb).1
  have Hbi : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := by have := Hl.1; refine ⟨hi0, ?_⟩; word
  have Hbj : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := by have := Hl.1; refine ⟨hj0, ?_⟩; word
  simp only [Hbi, _root_.and_self, ite_true]
  wp_apply wp_load_slice_index sl (sint.Z i) _ dq a.1 hi0 $$ [Hs] as Hs
  · iframe; ipureintro; rw [List.getElem?_map]; exact congrArg (Option.map Prod.fst) ha
  icases kvsAt_acc l (sint.nat i) a ha $$ Hkvs with ⟨Ha, Hclose⟩
  simp only [kvAt, mvcc.kvPtrIs, ↓reduceIte]
  icases Ha with ⟨%ks1, %st1, %uf1, %sc1, #Hk1, %vs1, #Hv1, Hp1⟩
  wp_auto
  ihave Hkvs := Hclose $$ [Hp1]
  · iexists ks1, st1, uf1, sc1; iframe Hk1; iexists vs1; iframe Hv1; iexact Hp1
  simp only [Hbj, _root_.and_self, ite_true]
  wp_apply wp_load_slice_index sl (sint.Z j) _ dq b.1 hj0 $$ [Hs] as Hs
  · iframe; ipureintro; rw [List.getElem?_map]; exact congrArg (Option.map Prod.fst) hb
  icases kvsAt_acc l (sint.nat j) b hb $$ Hkvs with ⟨Hb, Hclose⟩
  simp only [kvAt, mvcc.kvPtrIs, ↓reduceIte]
  icases Hb with ⟨%ks2, %st2, %uf2, %sc2, #Hk2, %vs2, #Hv2, Hp2⟩
  wp_auto
  ihave Hkvs := Hclose $$ [Hp2]
  · iexists ks2, st2, uf2, sc2; iframe Hk2; iexists vs2; iframe Hv2; iexact Hp2
  rw [sub_neg_iff _ _ (by unfold kvOk at hoka; omega) (by unfold kvOk at hokb; omega), ← kvLtBy_mod]
  iapply HΦ
  iframe

end proof


end EtcdGrove
end Perennial
