/- `MemoryStorage.Append` (`storage.go:280`), proved 2026-10-10 (Lean-first). -/
module

public import Spec.go_etcd_io.raft.v3.MemoryStorage__Append
public import Spec.go_etcd_io.raft.v3.MemoryStorage__firstIndex
public import Proof.go_etcd_io.raft.v3.InvRaftlog

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The entries the switch's first arm leaves (`append(ms.ents[:offset:offset],
entries...)`): the dummy, the stored entries below the batch, the batch. -/
private theorem append_cut (dummy : raftpb.Entry) (σ : StorState) (e0 : raftpb.Entry)
    (rest : List raftpb.Entry) (k : Nat)
    (Hk : (k : Int) = uint.Z e0.Index' - uint.Z σ.prev.index') (Hk1 : 1 ≤ k) :
    (dummy :: σ.ents).take k ++ e0 :: rest = dummy :: storApp σ (e0 :: rest) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [storApp, List.take_succ_cons, List.cons_append]
  rw [show (uint.Z e0.Index' - uint.Z σ.prev.index' - 1).toNat = j by omega]

/-- ... and the second (`append(ms.ents, entries...)`, the batch right after the stored
entries). -/
private theorem append_end (dummy : raftpb.Entry) (σ : StorState) (e0 : raftpb.Entry)
    (rest : List raftpb.Entry)
    (Hk : (σ.ents.length : Int) + 1 = uint.Z e0.Index' - uint.Z σ.prev.index') :
    (dummy :: σ.ents) ++ e0 :: rest = dummy :: storApp σ (e0 :: rest) := by
  simp only [storApp, List.cons_append]
  rw [List.take_of_length_le (by omega)]

theorem MemoryStorage.Append.wp_proof
    (wp_MemoryStorage_firstIndex : MemoryStorage.firstIndex.spec (GF := GF) (hG := hG)) :
    MemoryStorage.Append.spec (GF := GF) (hG := hG) := by
  intro ms γs σ p s dq Hbnd
  wp_start as ⟨Htok, Hs⟩
  icases Htok with (%Hnil | Htok)
  · -- an empty batch: `Append` returns at once
    subst Hnil
    ihave %Hslen := ownSlice_len $$ Hs
    simp only [List.length_nil] at Hslen
    wp_apply wp_with_defer as %defer defer
    wp_if_destruct
    · iapply HΦ
      iframe Hs
      ileft; ipureintro; trivial
    · exfalso
      apply Hif
      word
  iunfold memAppendTok at Htok
  icases Htok with ⟨#Hinit, #Hmu, %H, Hdone, #Hhist, Hep, %Htk⟩
  obtain ⟨Hlast, Hpe, Hpne, Hpok⟩ := Htk
  obtain ⟨e0, rest, rfl⟩ : ∃ e0 rest, p = e0 :: rest := by
    cases p with
    | nil => exact absurd rfl Hpne
    | cons a b => exact ⟨a, b, rfl⟩
  obtain ⟨He0lo, He0hi⟩ := Hpok e0 rfl
  have Hb0 := Hbnd e0 rfl
  ihave %Hslen := ownSlice_len $$ Hs
  simp only [List.length_cons] at Hslen Hb0
  wp_apply wp_with_defer as %defer defer
  wp_if_destruct
  · exfalso
    have H0 := Hslen.1
    rw [Hif, show sint.nat (W64 0) = 0 from rfl] at H0
    omega
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold memstorageInv at Hinv
  icases Hinv with ⟨%σp, Hinv⟩
  iNamedSuffix Hinv "_inv"
  iunfold memInvGhost at Hgs_inv
  icases Hgs_inv with ⟨%D, Hd_inv, #Hlb_inv, %HD⟩
  -- the writer's half: the contents are the state the batch was handed out at
  icases monoAuth_agree_keep γs.done _ _ D H $$ [$Hd_inv $Hdone] with ⟨⟨Hd_inv, Hdone⟩, %HDH⟩
  subst HDH
  have Hσp : σp = σ := by rw [Hlast] at HD; injection HD with h; exact h.symm
  subst Hσp
  iNamed Hfields_inv
  ihave Hf : memstorageFields ms σp $$ [HhardState Hsnapshot Hvoters Hents_f Hents Hents_cap HcallStats]
  · unfold memstorageFields
    iexists hs, snap, es, dummy, cs, voters
    iframe
    ipureintro; exact ⟨Hsnap_id, Hdummy⟩
  wp_apply wp_MemoryStorage_firstIndex ms σp Hpb_inv $$ [$Hf] as %fi ⟨%Hfi, Hf⟩
  have Hs0 : (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z s.len) = True :=
    eq_true ⟨by word, by word⟩
  simp only [Hs0, ↓reduceIte]
  -- `entries[0].Index`, read three times: the field, out of the fractional element
  icases ownSlice_elem_acc (sint.Z (W64 0)) e0 s dq (e0 :: rest) (by word) (by simp) $$ Hs
    with ⟨He0, Hsback⟩
  icases (AccessStrict.access_strict
      (A := (sliceIndexRef raftpb.Entry (sint.Z (W64 0)) s).[raftpb.Entry, go!"Index"] ↦{dq}
        e0.Index')
      (A' := (sliceIndexRef raftpb.Entry (sint.Z (W64 0)) s).[raftpb.Entry, go!"Index"] ↦{dq}
        e0.Index')
      (P := sliceIndexRef raftpb.Entry (sint.Z (W64 0)) s ↦{dq} e0)) $$ He0 with ⟨He0, Hclose⟩
  wp_auto
  have Hlenz : uint.Z s.len = (rest.length : Int) + 1 := by
    have := Hslen.1; word
  -- `last < first`: no, the batch starts at or above `first`
  wp_if_destruct
  · exfalso; word
  simp only [Hs0, ↓reduceIte]
  wp_auto
  -- `first > entries[0].Index`: no, the batch starts above the boundary
  wp_if_destruct
  · exfalso; word
  -- `offset := entries[0].Index - ms.ents[0].Index`
  iNamed Hf
  icases Hents with #Hents
  ihave %Hlen := ownSlice_len $$ Hents
  simp only [List.length_cons] at Hlen
  icases ownSlice_elem_acc (sint.Z (W64 0)) dummy es DFrac.discard (dummy :: σp.ents) (by word) rfl
    $$ Hents with ⟨#Hd0, -⟩
  iStructNamed Hd0
  have Hes0 : (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z es.len) = True :=
    eq_true ⟨by word, by word⟩
  simp only [Hs0, ↓reduceIte]
  wp_auto
  simp only [Hes0, ↓reduceIte]
  wp_auto
  ihave He0 := Hclose $$ He0
  ihave Hs := Hsback $$ He0
  rw [show (e0 :: rest).set (sint.Z (W64 0)).toNat e0 = e0 :: rest by simp]
  obtain ⟨Hd0i, Hd0t⟩ := Hdummy
  rw [Hd0i]
  have Hoff : uint.Z (e0.Index' - σp.prev.index') = uint.Z e0.Index' - uint.Z σp.prev.index' := by
    word
  have Heslen : uint.Z es.len = (σp.ents.length : Int) + 1 := by
    have := Hlen.1; word
  ihave %Hwf := ownSlice_wf $$ Hents
  -- the state the batch leaves, its bound, and `done` at it
  have Hpb' : uint.Z σp.prev.index' + ((storApp σp (e0 :: rest)).length : Int) < 2^61 := by
    simp only [storApp, List.length_append, List.length_take, List.length_cons]
    omega
  imod memDone_append γs D (storAbsorb { σp with pend := e0 :: rest }) $$ Hd_inv Hdone
    with ⟨Hd_inv, Hdone⟩
  wp_if_destruct
  · -- the batch overwrites stored entries: `append(ms.ents[:offset:offset], entries...)`
    have Hcut := of_decide_eq_true Hif.symm
    rw [Hoff] at Hcut
    have HoffZ : sint.Z (e0.Index' - σp.prev.index') = uint.Z e0.Index' - uint.Z σp.prev.index' := by
      word
    rw [ite_eq_left ⟨by word, by word, by word, by word⟩]
    icases (ownSlice_slice (W64 0) (e0.Index' - σp.prev.index') es DFrac.discard (dummy :: σp.ents)
      ⟨by word, by word, by word⟩).1 $$ Hents with ⟨-, #Hsub, -⟩
    have Hk : (sint.nat (e0.Index' - σp.prev.index') : Int) =
        uint.Z e0.Index' - uint.Z σp.prev.index' := by word
    have Hsubeq : subslice (sint.nat (W64 0)) (sint.nat (e0.Index' - σp.prev.index'))
        (dummy :: σp.ents) = (dummy :: σp.ents).take (sint.nat (e0.Index' - σp.prev.index')) := by
      simp only [subslice]; rfl
    ihave #Hsub1 : slice.slice es raftpb.Entry (W64 0) (e0.Index' - σp.prev.index') ↦*□
        (dummy :: σp.ents).take (sint.nat (e0.Index' - σp.prev.index')) $$ [Hsub]
    · rw [← Hsubeq]; iexact Hsub
    have Hne : (dummy :: σp.ents).take (sint.nat (e0.Index' - σp.prev.index')) ≠ [] := by
      intro Hc
      have := congrArg List.length Hc
      simp only [List.length_take, List.length_cons, List.length_nil] at this
      omega
    ihave #Hsub2 := ownSlice_same_ptr_len
      (slice.slice es raftpb.Entry (W64 0) (e0.Index' - σp.prev.index'))
      (slice.fullSlice es raftpb.Entry (W64 0) (e0.Index' - σp.prev.index')
        (e0.Index' - σp.prev.index'))
      _ _ Hne rfl rfl (by simp only [slice.fullSlice]; word) $$ Hsub1
    ihave Hcap0 := ownSliceCap_empty (V := raftpb.Entry)
      (slice.fullSlice es raftpb.Entry (W64 0) (e0.Index' - σp.prev.index')
        (e0.Index' - σp.prev.index')) (by simp only [slice.fullSlice])
      (by simp only [slice.fullSlice]; word)
    wp_auto
    wp_apply wp_slice_append_persistent (V := raftpb.Entry) _ _ s (e0 :: rest) dq
      $$ [$Hsub2 $Hcap0 $Hs] as %es' ⟨Hes', Hes'_cap, Hs⟩
    ihave #Hes2 : es' ↦*□ (dummy :: storApp σp (e0 :: rest)) $$ [Hes']
    · rw [← append_cut dummy σp e0 rest _ Hk (by omega)]; iexact Hes'
    -- the deferred `ms.Unlock()`, at the appended state
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock
      $$ [$Hmu $Hlocked Hd_inv HhardState Hsnapshot Hvoters Hents_f Hes'_cap HcallStats]
    · inext
      unfold memstorageInv
      iexists storAbsorb { σp with pend := e0 :: rest }
      isplitl [Hd_inv]
      · unfold memInvGhost
        iexists D ++ [storAbsorb { σp with pend := e0 :: rest }]
        iframe Hd_inv Hhist
        ipureintro; simp
      isplitl
      · unfold memstorageFields
        iexists hs, snap, es', dummy, cs, voters
        simp only [storAbsorb, storApp_pend, named]
        iframe
        isplitr
        · ipureintro; exact Hsnap_id
        isplitr
        · iexact Hes2
        ipureintro
        exact ⟨Hd0i, Hd0t⟩
      ipureintro
      simp only [storAbsorb, storApp_pend]
      exact Hpb'
    iapply HΦ
    iframe Hs
    iright
    unfold memAppendedTok
    iexists D
    iframe Hdone Hep
    ipureintro; exact Hpb'
  wp_if_destruct
  · -- the batch continues the stored entries: `append(ms.ents, entries...)`
    have Hend := of_decide_eq_true Hif.symm
    have Hk : (σp.ents.length : Int) + 1 = uint.Z e0.Index' - uint.Z σp.prev.index' := by
      have H1 : uint.Z es.len = uint.Z (e0.Index' - σp.prev.index') := by rw [Hend]
      omega
    wp_apply wp_slice_append_persistent (V := raftpb.Entry) es (dummy :: σp.ents) s (e0 :: rest) dq
      $$ [$Hents $Hents_cap $Hs] as %es' ⟨Hes', Hes'_cap, Hs⟩
    ihave #Hes2 : es' ↦*□ (dummy :: storApp σp (e0 :: rest)) $$ [Hes']
    · rw [← append_end dummy σp e0 rest Hk]; iexact Hes'
    -- the deferred `ms.Unlock()`, at the appended state
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock
      $$ [$Hmu $Hlocked Hd_inv HhardState Hsnapshot Hvoters Hents_f Hes'_cap HcallStats]
    · inext
      unfold memstorageInv
      iexists storAbsorb { σp with pend := e0 :: rest }
      isplitl [Hd_inv]
      · unfold memInvGhost
        iexists D ++ [storAbsorb { σp with pend := e0 :: rest }]
        iframe Hd_inv Hhist
        ipureintro; simp
      isplitl
      · unfold memstorageFields
        iexists hs, snap, es', dummy, cs, voters
        simp only [storAbsorb, storApp_pend, named]
        iframe
        isplitr
        · ipureintro; exact Hsnap_id
        isplitr
        · iexact Hes2
        ipureintro
        exact ⟨Hd0i, Hd0t⟩
      ipureintro
      simp only [storAbsorb, storApp_pend]
      exact Hpb'
    iapply HΦ
    iframe Hs
    iright
    unfold memAppendedTok
    iexists D
    iframe Hdone Hep
    ipureintro; exact Hpb'
  · -- a gap after the stored entries: excluded by `PendOk`
    exfalso
    rename_i Hlt
    have h1 : ¬ (uint.Z (e0.Index' - σp.prev.index') < uint.Z es.len) :=
      fun h => Hlt (by simp [h])
    have h2 : es.len ≠ e0.Index' - σp.prev.index' := fun h => Hif (by simp [h])
    have h3 : uint.Z es.len ≠ uint.Z (e0.Index' - σp.prev.index') := fun h => h2 (uint_Z_inj.1 h)
    omega

end proof

end EtcdGrove
end Perennial
