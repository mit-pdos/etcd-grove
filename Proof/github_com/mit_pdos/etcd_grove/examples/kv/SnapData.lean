/-
Lean-first (no Rocq counterpart).

# A snapshot's data, at the replica (D22 S-r, 2026-10-21)

What `run` needs to install and to take a snapshot (`KV__run.lean`), outside the spec/proof
discipline (lemmas on `Base.lean`'s `StateEnc` and raft's protobuf model):

* the data a replica's state encodes (`stateEnc_intro`: `encodeState`'s bindings of the two
  maps `runOwn` holds encode the replicated state of its client history), and what a
  decoded snapshot gives back (`maps_of_stateEnc`: `decodeState`'s maps are `runOwn`'s of the
  history the data encodes);
* `Snapshot.GetData` on a snapshot whose pointer fields are all set (`ownSnapS`, what a
  snapshot `Ready` hands out), as raft's `GetData` spec is on `ownSnapM`
  (`wp_Snapshot_GetData_S`; raft's `InvPbSnapSet.lean` has the other two getters,
  `wp_Snapshot_GetMetadata_S` and `wp_SnapshotMetadata_GetIndex_S`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Defs
public import Proof.go_etcd_io.raft.v3.InvPbSnapSet

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The bindings `kvs` and `ops` of a replica's maps `K` and `A` (`encodeState`'s `KVsOf`)
encode the replicated state of the history `H` the maps hold (`runOwn`). -/
theorem stateEnc_intro (H : List (List w8)) (K A : GMap (List w8) (List w8))
    (kvs ops : List (List w8 × List w8))
    (Hval : ∀ k, (K !! k).getD [] = kvFold H k) (HA : AppliedOk A H)
    (HK : KVsOf K kvs) (HO : KVsOf A ops) :
    StateEnc H (encState kvs ops) := by
  refine ⟨kvs, ops, rfl, HK.1, HO.1, fun k => by rw [HK.2 k]; exact Hval k, ?_⟩
  have He : (fun o => ops.lookup o) = (fun o => A !! o) := funext HO.2
  rw [He]; exact HA

/-- What `decodeState` gives back of data that encodes the history `H` (`StateEnc`, at the
bindings `kvs` and `ops`): maps as `runOwn` holds them at `H`. -/
theorem maps_of_stateEnc (H : List (List w8)) (kvs ops : List (List w8 × List w8))
    (K A : GMap (List w8) (List w8))
    (Hk : ∀ k, (kvs.lookup k).getD [] = kvFold H k)
    (Ho : AnsTab (fun o => ops.lookup o) H)
    (HK : ∀ k, K !! k = kvs.lookup k)
    (HAo : ∀ o, A !! o = ops.lookup o) :
    (∀ k, (K !! k).getD [] = kvFold H k) ∧ AppliedOk A H := by
  refine ⟨fun k => by rw [HK k]; exact Hk k, ?_⟩
  have He : (fun o => A !! o) = (fun o => ops.lookup o) := funext HAo
  unfold AppliedOk; rw [He]; exact Ho

section getdata
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `Snapshot.GetData` on a snapshot with every pointer field set (`ownSnapS`): its data, lent. -/
theorem wp_Snapshot_GetData_S (p : Loc) (dq : DFrac) (s : SnapshotM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ ownSnapS p dq s }}
      (App (Val (p @!! go.GoType.PointerType raftpb.Snapshot.ty @!! go!"GetData")) (Val #()))
    {{ (ds : GoSlice), RET #ds;
        ds ↦*{dq} s.Data' ∗ (ds ↦*{dq} s.Data' -∗ ownSnapS p dq s) }} := by
  wp_start as Hs
  iNamed Hs
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hnn
  · iapply HΦ
    iframe Hd
    iintro Hd
    iunfold ownSnapS
    iexists ds, pm, uf
    isplitr
    · ipureintro; exact Hnn
    iframe HD Hd HM Hm Hpb

theorem ownSnapS_not_null (p : Loc) (dq : DFrac) (s : SnapshotM) :
    ownSnapS (GF := GF) p dq s ⊢ ownSnapS p dq s ∗ ⌜p ≠ null⌝ := by
  iintro H
  iNamed H
  isplitl
  · iunfold ownSnapS
    iexists ds, pm, uf
    isplitr
    · ipureintro; exact Hnn
    iframe HD Hd HM Hm Hpb
  ipureintro; exact Hnn

end getdata

section pend
variable [GooseExts]

/-- A batch numbered on from the boundary of a storage that holds no entries (one that has just
installed a snapshot) may be handed out (`memStorage_handout`'s premise). -/
theorem pendOk_of_logIndices (σ : StorState) (es : List EntryM) (hne : es ≠ [])
    (hents : σ.ents = []) (H : LogIndicesOk σ.prev es) : PendOk σ es := by
  refine ⟨hne, fun e0 h0 => ?_⟩
  have h0' : es[0]? = some e0 := by rw [List.head?_eq_getElem?] at h0; exact h0
  have H0 := H 0 e0 h0'
  rw [hents]
  simp only [List.length_nil] at H0 ⊢
  push_cast at H0 ⊢
  refine ⟨by omega, by omega, fun k e hk => ?_⟩
  have := H k e hk
  push_cast at this
  omega

theorem pendAbove_of_logIndices (σ : StorState) (es : List EntryM)
    (hfl : uint.Z σ.fl ≤ uint.Z σ.prev.index') (H : LogIndicesOk σ.prev es) : PendAbove σ es := by
  intro e0 h0
  have h0' : es[0]? = some e0 := by rw [List.head?_eq_getElem?] at h0; exact h0
  have H0 := H 0 e0 h0'
  push_cast at H0
  omega

end pend

end EtcdGrove
end Perennial
