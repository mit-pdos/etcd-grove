/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/updateCommittedIndex.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.updateCommittedIndex
public import EtcdDeps.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex

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

theorem updateCommittedIndex.wp_proof
    (hGI : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG)) :
    updateCommittedIndex.spec (GF := GF) (hG := hG) := by
  intro ap rh dq apv ceL ce
  wp_start as ⟨Hap, #Hsl, #Hents, %Hsnap, #Hrh⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  iunfold entriesAt at Hents
  icases Hents with ⟨%Hlen2, #Hent⟩
  iunfold isReadyHandler at Hrh
  icases Hrh with ⟨%gl, %ul, %uls, %uci, #Hgl, #Hul, #Huls, #Huci, #Hglt, #Hult, #Hulst, #Hucit⟩
  ihave #Hrpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_auto
  -- `ci`: the last entry's index, or 0
  wp_join iprop(∃ ci : w64, ci_ptr ↦ ci)
    at next with [ci] as ⟨%ci, ci⟩
  · wp_if_destruct
    · have hlenpos : 0 < ceL.length := by
        rcases Hlen with ⟨h1, h2⟩
        rw [h1]
        rcases Int.lt_or_eq_of_le h2 with h | h
        · omega
        · exfalso; apply Hif; word
      list_elem ceL (ceL.length - 1) as e
      have hm : ∃ m, ce[ceL.length - 1]? = some m := by
        rw [List.getElem?_eq_getElem (by omega)]; exact ⟨_, rfl⟩
      obtain ⟨m, hm⟩ := hm
      wp_auto
      wp_apply wp_load_slice_index apv.entries' (sint.Z (apv.entries'.len - W64 1)) ceL
        DFrac.discard e (by word) $$ [] as -
      · iframe Hsl; ipureintro
        have : (sint.Z (apv.entries'.len - W64 1)).toNat = ceL.length - 1 := by word
        rw [this]; exact He_lookup
      ihave He := Hent $$ %(ceL.length - 1) %e %m %He_lookup %hm
      wp_apply hGI e m $$ [$Hrpkg $He]
      wp_auto
      wp_join_done
      iexists _; iframe ci
    · wp_join_done
      iexists _; iframe ci
  -- `ap.snapshot != nil`: never (no snapshot)
  wp_auto
  simp only [Hsnap]
  wp_auto
  wp_if_destruct
  · wp_apply Hucit ci
    wp_auto
    iapply HΦ
    iframe
  · iapply HΦ
    iframe

end proof

end EtcdGrove
end Perennial
