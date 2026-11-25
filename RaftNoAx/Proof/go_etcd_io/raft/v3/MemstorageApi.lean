-- The copy for the part `RaftNoAx/` of `Proof/go_etcd_io/raft/v3/MemstorageApi.lean` (etc/copy-part.py; rerun it, do not edit).
/-
# `MemoryStorage` at the node API (raft-final, 2026-10-29: U8 v2 step 4, the design's track P7)

The generic contract law (`memStorage_isStorageP`, `MemstorageInstance.lean`) at the API's
justifications (`memStorJ γ id`: the stored snapshots valid, `snapshotValid γ`; compaction within what
node `id` applied or a snapshot it handed out, `nodeAppliedLb`/`snapGiven`; a stored snapshot within
what was delivered, `storDL`): the storage's invariant `memStorInv ms γs γ id`, its allocation, and
`isStorage γ id` of a registered `MemoryStorage`. (A client whose `Storage` wraps a `MemoryStorage`,
kvreconf's, builds its own `StorageModel` instance over these: the design's A6, no wrapper law here.)

Stated in raft-final's phase 1, proved in its phase 2 (track P7): the allocation from
`memStorInvP_alloc` (index `0` justified by `nodeAppliedLb_zero`), the contract from
`memStorage_isStorageP` (`storBnd` is `memBnd` at `memStorJ`).
-/
module

public import RaftNoAx.Proof.go_etcd_io.raft.v3.MemstorageInstance
public import RaftNoAx.Proof.go_etcd_io.raft.v3.InvNodeRule

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section api
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [MemStorReg GF]

/-- The API's justifications for the `MemoryStorage` of key `K` (`isStorage`'s pieces; 2026-11-01,
durability stage I-4: keyed by the storage's key, `snapGiven` merged into `nodeAppliedLb`). -/
def memStorJ (γ : Cluster) (K : GName) : MemJust GF where
  SV := snapshotValid γ
  -- (auth-lease S4, 2026-11-16, L-r2) with the no-snapshot mode's cap (`storBnd`)
  B k := iprop(nodeAppliedLb γ K k ∗ ⌜clusterNoSnap γ → k ≤ 1⌝)
  DL := nodeCommitLb γ K
  SV_pers := fun sv => by infer_instance
  B_pers := fun k => by infer_instance
  B_timeless := fun k => by infer_instance
  DL_pers := fun i => by infer_instance

/-- (auth-lease S4, L-r2) Outside the no-snapshot mode, `memStorJ`'s justification is the applied
bound. -/
theorem memStorJ_B_off (γ : Cluster) (K : GName) (k : Nat) (h : ¬ clusterNoSnap γ) :
    nodeAppliedLb (GF := GF) γ K k ⊢ (memStorJ γ K).B k := by
  show _ ⊢ iprop(nodeAppliedLb γ K k ∗ _)
  iintro #H
  isplitr
  · iexact H
  ipureintro; intro h'; exact absurd h' h

/-- (auth-lease S4, L-r2) ... and at a point at most `1`, in either mode. -/
theorem memStorJ_B_le_one (γ : Cluster) (K : GName) (k : Nat) (h : k ≤ 1) :
    nodeAppliedLb (GF := GF) γ K k ⊢ (memStorJ γ K).B k := by
  show _ ⊢ iprop(nodeAppliedLb γ K k ∗ _)
  iintro #H
  isplitr
  · iexact H
  ipureintro; intro _; exact h

/-- (auth-lease S4, L-r2) `memStorJ`'s justification gives the applied bound. -/
theorem memStorJ_B_lb (γ : Cluster) (K : GName) (k : Nat) :
    (memStorJ (GF := GF) γ K).B k ⊢ nodeAppliedLb γ K k := by
  show iprop(nodeAppliedLb γ K k ∗ _) ⊢ _
  iintro ⟨#H, -⟩
  iexact H

/-- **The `MemoryStorage` invariant of key `K`** (persistent): the generic one at the API's
justifications. -/
def memStorInv (ms : Loc) (γs : MemStorNames) (γ : Cluster) (K : GName) : IProp GF :=
  memStorInvP ms γs (memStorJ γ K)

instance memStorInv_persistent (ms : Loc) (γs : MemStorNames) (γ : Cluster) (K : GName) :
    Persistent (memStorInv (GF := GF) ms γs γ K) := by
  unfold memStorInv; infer_instance

/-- **The attach** (2026-11-01, durability stage I-4/I-5; until then from the fresh token at `0`):
from `NewMemoryStorage`'s detached token at the compaction point `c` and the stored snapshot `sv`,
once `InitialState` returned, with raft's bound at `c` (`nodeAppliedLb`, every lower point by
`nodeAppliedLb_mono`) and the stored snapshot's validity (the client's certificate, and raft's
commit bound at its index). It consumes the token: a storage is attached once. -/
theorem memStorInv_alloc (ms : Loc) (γs : MemStorNames) (γ : Cluster) (K : GName) (c : Nat)
    (sv : SnapshotM) (E : CoPset)
    -- (auth-lease S4, 2026-11-16, decided by etcd-grove-02) in the cluster's no-snapshot mode, the
    -- compaction point at most `1` (`memStorJ.B`'s cap, L-r2)
    (Hcap : clusterNoSnap γ → c ≤ 1) :
    ⊢ memStorLock (GF := GF) ms γs -∗ memStorFresh ms γs c sv -∗ nodeAppliedLb γ K c -∗
      (⌜sv.Metadata'.Index' = W64 0⌝ ∨ snapshotValid γ sv ∗
        nodeCommitLb γ K (uint.nat sv.Metadata'.Index')) ={E}=∗
      memStorInv ms γs γ K := by
  -- PORT(durability stage II): restated (I-4: keyed by `K`, the generalized attach)
  sorry

private theorem memStorage_contract (ms : Loc) (γs : MemStorNames) (γ : Cluster) (K : GName)
    (SV : SnapshotM → IProp GF) (hsz : γ.maxData.isSome = true → γs.sz = true)
    (htr : Cluster.trace γ = none) :
    isStorageP γs.sz SV (memBnd (memStorJ γ K)) (nodeCommitLb γ K) (memStorIface ms) ⊢
      isStorageP γ.maxData.isSome SV (storBnd γ K) (nodeCommitLb γ K) (memStorIface ms) := by
  iintro #H
  ihave #H' : isStorageP γ.maxData.isSome SV (memBnd (memStorJ γ K))
    (nodeCommitLb γ K) (memStorIface ms) $$ []
  · by_cases h : γ.maxData.isSome = true
    · have e : γ.maxData.isSome = γs.sz := by rw [h, hsz h]
      rw [e]
      iExactEq H; rfl
    · have e : γ.maxData.isSome = false := by simpa using h
      rw [e]
      ihave #H2 := isStorageP_unsize _ _ _ _ _ $$ H
      iExactEq H2; rfl
  unfold isStorageP
  icases H' with ⟨%i, %Hst, #H1, #H2, #H3, #H4, #H5, #Hbound, #Hlen⟩
  iexists i
  iframe H1 H2 H3 H4 H5 Hlen
  isplitr
  · ipureintro; exact Hst
  iintro !> %c #Hc
  imod Hbound $$ %c Hc with HB
  unfold memBnd memStorJ
  icases HB with ⟨%k, %Hck, #Hk, %Hns⟩
  imodintro
  iapply storBnd_intro_untraced γ K k c htr Hns $$ Hk
  ipureintro; exact Hck

/-- **A registered `MemoryStorage` meets the storage contract of key `K`**, at an untraced cluster
(2026-11-12, trace-check, Q39 (a): `storBnd` is gated on the trace; at a traced one `memStorJ`'s
bound, the applied index, is not the contract's). (out_size C2) A
cluster that bounds proposed data needs a sized storage (`γs.sz`, chosen at `NewMemoryStorage`). -/
theorem memStorage_isStorage
    (wp_LastIndex : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Term : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (wp_Entries : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
    (wp_Snapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
    (ms : Loc) (γs : MemStorNames) (γ : Cluster) (K : GName)
    (hsz : γ.maxData.isSome = true → γs.sz = true) (htr : Cluster.trace γ = none) :
    ⊢ memStorInv (GF := GF) ms γs γ K -∗ memStorReg ms γs -∗ isStorage γ K (memStorIface ms) := by
  unfold isStorage memStorInv
  iintro #Hinv #Hreg
  iapply memStorage_contract ms γs γ K (snapshotValid γ) hsz htr
  ihave #H := memStorage_isStorageP wp_LastIndex wp_FirstIndex wp_Term wp_Entries wp_Snapshot
    ms γs (memStorJ γ K) $$ Hinv Hreg
  iExactEq H; rfl

/-- The stored snapshot also carries the client's persistent source tag. -/
def memStorJT (γ : Cluster) (K : GName) (Tg : SnapshotM → IProp GF) [∀ sv, Persistent (Tg sv)] : MemJust GF :=
  { memStorJ γ K with
    SV := fun sv => iprop(snapshotValid γ sv ∗ Tg sv)
    SV_pers := fun _ => by infer_instance }

/-- The memory storage invariant used by a client tracking snapshot provenance. -/
def memStorInvT (ms : Loc) (γs : MemStorNames) (γ : Cluster) (K : GName)
    (Tg : SnapshotM → IProp GF) [∀ sv, Persistent (Tg sv)] : IProp GF :=
  memStorInvP ms γs (memStorJT γ K Tg)

theorem memStorInvT_alloc (ms : Loc) (γs : MemStorNames) (γ : Cluster) (K : GName)
    (Tg : SnapshotM → IProp GF) [∀ sv, Persistent (Tg sv)] (c : Nat) (sv : SnapshotM) (E : CoPset)
    (Hcap : clusterNoSnap γ → c ≤ 1) :
    ⊢ memStorLock (GF := GF) ms γs -∗ memStorFresh ms γs c sv -∗ nodeAppliedLb γ K c -∗
      (⌜sv.Metadata'.Index' = W64 0⌝ ∨ (snapshotValid γ sv ∗ Tg sv) ∗
        nodeCommitLb γ K (uint.nat sv.Metadata'.Index')) ={E}=∗
      memStorInvT ms γs γ K Tg := by
  iintro #Hl Hf #Ha Hv
  unfold memStorInvT
  iapply memStorInvP_alloc ms γs (memStorJT γ K Tg) E c sv $$ Hl Hf [] [Hv]
  rotate_left
  · iExactEq Hv; rfl
  iintro !> %k %hk
  simp only [memStorJT, memStorJ]
  isplitr
  · iapply nodeAppliedLb_mono γ K c k hk $$ Ha
  ipureintro; exact fun h => Nat.le_trans hk (Hcap h)

theorem memStorage_isStorageT
    (wp_LastIndex : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Term : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (wp_Entries : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
    (wp_Snapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
    (ms : Loc) (γs : MemStorNames) (γ : Cluster) (K : GName)
    (Tg : SnapshotM → IProp GF) [∀ sv, Persistent (Tg sv)]
    (hsz : γ.maxData.isSome = true → γs.sz = true) (htr : Cluster.trace γ = none) :
    ⊢ memStorInvT (GF := GF) ms γs γ K Tg -∗ memStorReg ms γs -∗ isStorageT γ K Tg (memStorIface ms) := by
  unfold memStorInvT isStorageT
  iintro #Hinv #Hreg
  iapply memStorage_contract ms γs γ K (fun sv => iprop(snapshotValid γ sv ∗ Tg sv)) hsz htr
  ihave #H := memStorage_isStorageP wp_LastIndex wp_FirstIndex wp_Term wp_Entries wp_Snapshot
    ms γs (memStorJT γ K Tg) $$ Hinv Hreg
  iExactEq H; rfl

end api

end EtcdGrove
end Perennial
