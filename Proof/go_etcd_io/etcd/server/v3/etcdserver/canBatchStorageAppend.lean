/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/canBatchStorageAppend.lean`. Lean-first (no
Rocq counterpart; etcd-io/etcd#22223).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.canBatchStorageAppend
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem canBatchStorageAppend.wp_proof
    (hGI : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG)) :
    canBatchStorageAppend.spec (GF := GF) (hG := hG) := by
  have hGI := wp_entryAt_GetIndex hGI
  intro s1 s2 l1 l2 ms ns
  wp_start as ⟨#H1, #He1, #H2, #He2⟩
  ihave %Hl1 := ownSlice_len _ _ _ $$ H1
  ihave %Hl2 := ownSlice_len _ _ _ $$ H2
  iunfold entriesAt at He1 He2
  icases He1 with ⟨%Hn1, #Hf1⟩
  icases He2 with ⟨%Hn2, #Hf2⟩
  ihave #Hrpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_auto
  wp_if_destruct
  · -- `len(entries) == 0`
    (try wp_auto)
    iapply HΦ
    ipureintro
    have h0 : l1.length = 0 := by rw [Hl1.1]; unfold sint.nat; rw [Hif]; rfl
    have : ms = [] := List.length_eq_zero_iff.mp (by rw [← Hn1]; exact h0)
    simp [this]
  · have hl1 : 0 < l1.length := by
      rcases Hl1 with ⟨h1, h2⟩
      rcases Int.lt_or_eq_of_le h2 with h | h
      · rw [h1]; word
      · exfalso; apply Hif; word
    wp_if_destruct
    · -- `len(next) == 0`
      (try wp_auto)
      iapply HΦ
      ipureintro
      have h0 : l2.length = 0 := by rw [Hl2.1]; unfold sint.nat; rw [Hif]; rfl
      have : ns = [] := List.length_eq_zero_iff.mp (by rw [← Hn2]; exact h0)
      simp [this]
    · have hl2 : 0 < l2.length := by
        rcases Hl2 with ⟨h1, h2⟩
        rcases Int.lt_or_eq_of_le h2 with h | h
        · rw [h1]; word
        · exfalso; apply Hif; word
      -- `next[0].GetIndex()`
      list_elem l2 0 as e2
      obtain ⟨z, hz⟩ : ∃ z, ns[0]? = some z :=
        ⟨_, List.getElem?_eq_getElem (by rw [← Hn2]; exact hl2)⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
      wp_apply wp_load_slice_index s2 (sint.Z (W64 0)) l2 DFrac.discard e2 (by word) $$ [] as -
      · iframe H2; ipureintro; exact He2_lookup
      ihave He2 := Hf2 $$ %0 %e2 %z %He2_lookup %hz
      wp_apply hGI e2 z $$ [$Hrpkg $He2]
      -- `entries[len(entries)-1].GetIndex()`
      list_elem l1 (l1.length - 1) as e1
      obtain ⟨a, ha⟩ : ∃ a, ms[l1.length - 1]? = some a :=
        ⟨_, List.getElem?_eq_getElem (by rw [← Hn1]; omega)⟩
      (try wp_auto)
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
      wp_apply wp_load_slice_index s1 (sint.Z (s1.len - W64 1)) l1 DFrac.discard e1 (by word) $$ [] as -
      · iframe H1; ipureintro
        have : (sint.Z (s1.len - W64 1)).toNat = l1.length - 1 := by word
        rw [this]; exact He1_lookup
      ihave He1 := Hf1 $$ %(l1.length - 1) %e1 %a %He1_lookup %ha
      wp_apply hGI e1 a $$ [$Hrpkg $He1]
      (try wp_auto)
      iapply HΦ
      ipureintro
      have hms : ms ≠ [] := List.ne_nil_of_length_pos (by rw [← Hn1]; exact hl1)
      have hns : ns ≠ [] := List.ne_nil_of_length_pos (by rw [← Hn2]; exact hl2)
      have hlast : ms.getLast? = some a := by rw [List.getLast?_eq_getElem?, ← Hn1, ha]
      have hhead : ns.head? = some z := by rw [List.head?_eq_getElem?, hz]
      constructor
      · intro h
        right; right
        exact ⟨a, z, hlast, hhead, by simpa using h⟩
      · rintro (h | h | ⟨a', z', ha', hz', he⟩)
        · exact absurd h hms
        · exact absurd h hns
        · rw [hlast] at ha'; rw [hhead] at hz'
          cases ha'; cases hz'
          simp [he]

end proof

end EtcdGrove
end Perennial
