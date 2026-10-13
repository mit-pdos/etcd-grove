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
  intro ap rh es ceL ce R
  wp_start as ⟨#Hes, #Hsl, #Hents, #Hsnap, #Hrh, HR⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  iunfold entriesAt at Hents
  icases Hents with ⟨%Hlen2, #Hent⟩
  ihave #Hrpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_auto
  -- `ci`: the last entry's index, or 0
  wp_join iprop(∃ ci : w64, ci_ptr ↦ ci ∗ ap_ptr ↦ ap)
    at next with [ci ap] as ⟨%ci, ci, ap⟩
  · wp_if_destruct
    · -- no entries: `ci` stays 0
      (try wp_auto)
      isplitr
      · itrivial
      iexists _; iframe ci ap
    · have hlenz : 0 < sint.Z es.len := by
        rcases Hlen with ⟨h1, h2⟩
        rcases Int.lt_or_eq_of_le h2 with h | h
        · exact h
        · exfalso; apply Hif; word
      have hlenpos : 0 < ceL.length := by rw [Hlen.1]; word
      list_elem ceL (ceL.length - 1) as e
      have hm : ∃ m, ce[ceL.length - 1]? = some m := by
        rw [List.getElem?_eq_getElem (by omega)]; exact ⟨_, rfl⟩
      obtain ⟨m, hm⟩ := hm
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
      wp_apply wp_load_slice_index es (sint.Z (es.len - W64 1)) ceL
        DFrac.discard e (by word) $$ [] as -
      · iframe Hsl; ipureintro
        have : (sint.Z (es.len - W64 1)).toNat = ceL.length - 1 := by word
        rw [this]; exact He_lookup
      ihave He := Hent $$ %(ceL.length - 1) %e %m %He_lookup %hm
      wp_apply hGI e m $$ [$Hrpkg $He]
      (try wp_auto)
      isplitr
      · itrivial
      iexists _; iframe ci ap
  -- `ap.snapshot != nil`: never (no snapshot)
  iunfold isReadyHandler at Hrh
  icases Hrh with ⟨%gl, %ul, %uls, %uci, #Hgl, #Hul, #Huls, #Huci, #Hglt, #Hult, #Hulst, #Hucit⟩
  wp_if_destruct
  · iapply HΦ
    iexact HR
  · ispecialize Hucit $$ %ci
    -- (`wp_bind` then `iapply`: a `wp_apply` of the hypothesis triple inside `exceptionDo` can
    -- close the goal with a synthetic `sorry`)
    wp_bind (App (Val #uci) (Val #ci))
    iapply Hucit $$ HR
    inext
    iintro HR
    wp_auto
    iapply HΦ $$ HR

end proof

end EtcdGrove
end Perennial
