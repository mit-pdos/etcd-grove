/- Port of election_proof/proof_MemoryStorage__Entries.v. U8 v2 step 3 (2026-10-29): over the lock's
invariant; past the compaction point, the caller's two ranges are in the lock's map, so `hi` is at
most the end (no panic), the entries are not only the dummy (no `ErrUnavailable`), and the
physical window is the caller's (`MemoryStorage.Entries.window`). -/
module

public import Spec.go_etcd_io.raft.v3.MemoryStorage__Entries
public import Spec.go_etcd_io.raft.v3.MemoryStorage__lastIndex
public import Spec.go_etcd_io.raft.v3.limitSize
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import Proof.go_etcd_io.raft.v3.LemmasEnts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The window `[lo, hi)` of the caller's ranges `ab` (from `k`), all in the lock's map `M`, past
the compaction point `c`: it ends at or before the end, and the physical entries over it are the
caller's. -/
theorem MemoryStorage.Entries.window (M : GMap Nat EntryM) (c : Nat) (ents ab : List EntryM)
    (k lo hi : Nat)
    (Hab : ∀ j e, ab[j]? = some e → M.lookup (k + j) = some e)
    (Hend : ∀ i, c + 1 + ents.length ≤ i → M.lookup i = none)
    (Hmid : ∀ i, c < i → i < c + 1 + ents.length → M.lookup i = ents[i - c - 1]?)
    (Hk : k ≤ lo) (Hlohi : lo < hi) (Hhi : hi ≤ k + ab.length) (Hc : c < lo) :
    hi ≤ c + 1 + ents.length ∧
      (ents.take (hi - c - 1)).drop (lo - c - 1) = (ab.drop (lo - k)).take (hi - lo) := by
  have Hin : ∀ i, k ≤ i → i < hi → ∃ e, ab[i - k]? = some e ∧ M.lookup i = some e := by
    intro i h1 h2
    refine ⟨ab[i - k]'(by omega), List.getElem?_eq_getElem (by omega), ?_⟩
    have := Hab (i - k) _ (List.getElem?_eq_getElem (by omega))
    rwa [show k + (i - k) = i by omega] at this
  have Hhe : hi ≤ c + 1 + ents.length := by
    refine Nat.le_of_not_lt fun h => ?_
    obtain ⟨e, -, He⟩ := Hin (hi - 1) (by omega) (by omega)
    rw [Hend (hi - 1) (by omega)] at He
    cases He
  refine ⟨Hhe, List.ext_getElem? fun n => ?_⟩
  simp only [List.getElem?_drop, List.getElem?_take]
  by_cases hn : n < hi - lo
  · rw [ite_eq_left (by omega), ite_eq_left hn]
    obtain ⟨e, He1, He2⟩ := Hin (lo + n) (by omega) (by omega)
    rw [show lo - k + n = lo + n - k by omega, He1]
    have := Hmid (lo + n) (by omega) (by omega)
    rw [He2, show lo + n - c - 1 = lo - c - 1 + n by omega] at this
    exact this.symm
  · rw [ite_eq_right (by omega), ite_eq_right hn]

/-- `InvRaftlog`'s `ownSlice_same_ptr_len` (whose section takes a `StorageModel`, which this proof
no longer has): two slice values with the same pointer and length own the same non-empty list. -/
theorem MemoryStorage.Entries.ownSlice_same_ptr_len {V : Type} [ZeroVal V]
    [TypedPointsto (GF := GF) V] (s1 s2 : GoSlice) (dq : DFrac) (vs : List V) :
    vs ≠ [] →
    s1.ptr = s2.ptr →
    s1.len = s2.len →
    sint.Z s2.len ≤ sint.Z s2.cap →
    ⊢ (s1 ↦*{dq} vs : IProp GF) -∗ s2 ↦*{dq} vs := by
  intro Hne Hptr Hlen Hcap
  obtain ⟨p1, l1, c1⟩ := s1
  obtain ⟨p2, l2, c2⟩ := s2
  simp only at Hptr Hlen Hcap
  subst Hptr Hlen
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨H, %_⟩)
  · exact absurd H.2 Hne
  · iright
    iframe H
    ipureintro; exact Hcap

theorem MemoryStorage.Entries.wp_proof
    (wp_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (wp_MemoryStorage_lastIndex : MemoryStorage.lastIndex.spec (GF := GF) (hG := hG))
    (wp_limitSize : limitSize.spec (GF := GF) (hG := hG)) :
    MemoryStorage.Entries.spec (GF := GF) (hG := hG) := by
  intro ms γs k dq1 dq2 a b lo hi maxSize ec
  wp_start as ⟨#Hlock, Hla, Hlb, %Hrangev, #Hec⟩
  iunfold memStorLock at Hlock
  icases Hlock with ⟨#Hinit, #Hmu⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold memstorageInv at Hinv
  icases Hinv with ⟨%p, %ents, %M, %sv, Hinv⟩
  iNamedSuffix Hinv "_inv"
  -- the caller's two ranges are in the map
  iunfold memLog at Hla Hlb
  icases Hla with ⟨Hla, %Hlab⟩
  icases Hlb with ⟨Hlb, %Hlbb⟩
  icases memLogL_auth _ _ _ _ _ _ $$ Hlog_inv Hla with %HMa
  icases memLogL_auth _ _ _ _ _ _ $$ Hlog_inv Hlb with %HMb
  have HMab : ∀ j e, (a ++ b)[j]? = some e → M.lookup (k + j) = some e := by
    intro j e h
    rw [List.getElem?_append] at h
    split at h
    · exact HMa j e h
    · have := HMb (j - a.length) e h
      rwa [show k + a.length + (j - a.length) = k + j by omega] at this
  -- the compaction point is compacted
  ihave #Hcomp : memCompacted γs (uint.nat p.index') $$ [Hcp_inv]
  · ihave #Hlb := monoNatLbOwn_get _ _ _ $$ Hcp_inv
    iunfold memCompJust at Hcj_inv
    icases Hcj_inv with ⟨%L, #HL, %HcL⟩
    iunfold memCompacted
    iright
    iframe Hlb
    iexists L
    iframe HL
    ipureintro; exact ⟨_, HcL, Nat.le_refl _⟩
  have Hc1 := Hok_inv.1
  have Hpb' : uint.Z (memPhys p ents).prev.index' + ((memPhys p ents).ents.length : Int) < 2^61 := by
    simp only [memPhys]; word
  have Hwin := fun Hc => MemoryStorage.Entries.window M (uint.nat p.index') ents (a ++ b) k
    (uint.nat lo) (uint.nat hi) HMab Hok_inv.2.1 Hok_inv.2.2.1 Hrangev.1 Hrangev.2.1
    (by simp only [List.length_append]; omega) Hc
  iunfold memstorageFields at Hfields_inv
  icases Hfields_inv with ⟨%hp, %es, %dummy, %nfi, %nli, %nen, %nte, %nsn, Hfields_inv⟩
  generalize Hσ : memPhys p ents = σ at Hpb' ⊢
  have Hσprev : σ.prev = p := by rw [← Hσ]; rfl
  have Hσents : σ.ents = ents := by rw [← Hσ]; rfl
  iNamed Hfields_inv
  icases Hents with #Hents
  ihave %Hcl := entsRO_cons_len $$ Hents
  icases entsRO_lookup es (dummy :: σ.ents) 0 dummy rfl $$ Hents
    with ⟨%ls, %l0, #Hls, #He0, %Hl0⟩
  wp_auto
  rw [ite_eq_left ⟨by word, by word⟩]
  wp_apply wp_load_slice_index es (sint.Z (W64 0)) ls DFrac.discard l0 (by word) $$ [Hls] with -
  · iframe Hls; ipureintro; exact Hl0.1
  wp_apply wp_GetIndex.1 l0 DFrac.discard dummy $$ [He0] with -
  · iframe He0
  obtain ⟨Hd0, Hd1⟩ := Hdummy
  wp_if_destruct
  · -- at or below the compaction point: `ErrCompacted`
    have Hle : uint.Z lo ≤ uint.Z p.index' := by rw [Hd0, Hσprev] at Hif; word
    try wp_auto
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HhardState Hents_f Hents Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot Hlog_inv Hen_inv Hcp_inv Hsx_inv Hlk_inv]
    · unfold memstorageInv
      iexists p, ents, M, sv
      simp only [named]
      iframe # ∗
      isplitl
      · unfold memstorageFields
        rw [Hσ]
        iexists _, _, _, _, _, _, _, _
        iframe # ∗
        ipureintro; exact ⟨Hd0, Hd1⟩
      ipureintro; exact Hok_inv
    iapply HΦ $$ %slice.nil %([] : List EntryM) %ec
    isplitl [Hla]
    · iunfold memLog; iframe Hla; ipureintro; exact Hlab
    isplitl [Hlb]
    · iunfold memLog; iframe Hlb; ipureintro; exact Hlbb
    ileft
    isplitl []
    · ipureintro; rfl
    iapply memCompacted_mono γs _ _ (by word) $$ Hcomp
  have Hlo : uint.Z p.index' + 1 ≤ uint.Z lo := by rw [Hd0, Hσprev] at Hif; word
  obtain ⟨Hhie, HEw⟩ := Hwin (by word)
  have Hrange : uint.Z σ.prev.index' + 1 ≤ uint.Z lo ∧ uint.Z lo < uint.Z hi ∧
      uint.Z hi ≤ uint.Z σ.prev.index' + (σ.ents.length : Int) + 1 := by
    rw [Hσprev, Hσents]
    refine ⟨Hlo, by have := Hrangev.2.1; word, by word⟩
  have HE : (σ.ents.take (uint.Z hi - uint.Z σ.prev.index' - 1).toNat).drop
        (uint.Z lo - uint.Z σ.prev.index' - 1).toNat =
      ((a ++ b).drop (uint.nat lo - k)).take (uint.nat hi - uint.nat lo) := by
    rw [Hσprev, Hσents, ← HEw]
    congr 2 <;> word
  ihave Hf : memstorageFields ms σ $$ [HhardState Hents_f Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
  · unfold memstorageFields
    iexists _, _, _, _, _, _, _, _
    iframe HhardState Hents_f Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot Hents Hents_cap
    ipureintro
    exact ⟨Hd0, Hd1⟩
  wp_apply wp_MemoryStorage_lastIndex ms σ Hpb' $$ [$Hf] as %li ⟨%Hli, Hf⟩
  rw [Hd0]
  unfold memstorageFields
  iNamed Hf
  icases Hents with #Hents
  clear Hcl Hl0
  ihave %Hcl := entsRO_cons_len $$ Hents
  obtain ⟨Hd0', Hd1'⟩ := Hdummy
  wp_if_destruct
  · exfalso; word
  wp_if_destruct
  · exfalso; word
  iunfold entsRO at Hents
  iunfold entsPts at Hents
  icases Hents with ⟨%ls, #Hls, #Hbig⟩
  ihave %Hlen2 := ownSlice_len _ _ _ $$ Hls
  ihave %Hwf2 := ownSlice_wf _ _ _ $$ Hls
  ihave %Hbl := entsBig_length $$ Hbig
  have Hlo' : sint.Z (lo - σ.prev.index') = uint.Z lo - uint.Z σ.prev.index' := by word
  have Hhi' : sint.Z (hi - σ.prev.index') = uint.Z hi - uint.Z σ.prev.index' := by word
  rw [ite_eq_left ⟨by word, by word, by word⟩]
  wp_auto
  -- the sub-slice `σ.ents[lo-offset:hi-offset]` is `E0`
  have Hlon : sint.nat (lo - σ.prev.index') = (uint.Z lo - uint.Z σ.prev.index' - 1).toNat + 1 := by
    word
  have Hhin : sint.nat (hi - σ.prev.index') = (uint.Z hi - uint.Z σ.prev.index' - 1).toNat + 1 := by
    word
  have HE0 : subslice (sint.nat (lo - σ.prev.index')) (sint.nat (hi - σ.prev.index')) (dummy :: σ.ents) =
      (σ.ents.take (uint.Z hi - uint.Z σ.prev.index' - 1).toNat).drop
        (uint.Z lo - uint.Z σ.prev.index' - 1).toNat := by
    rw [Hlon, Hhin]; simp [subslice]
  have HE0len : ((σ.ents.take (uint.Z hi - uint.Z σ.prev.index' - 1).toNat).drop
      (uint.Z lo - uint.Z σ.prev.index' - 1).toNat).length =
      (uint.Z hi - uint.Z lo).toNat := by
    simp only [List.length_drop, List.length_take]; omega
  icases (ownSlice_slice (lo - σ.prev.index') (hi - σ.prev.index') es DFrac.discard ls
      ⟨by word, by word, by word⟩).1 $$ Hls with ⟨-, #Hsub, -⟩
  ihave #Hbsub := entsBig_subslice (sint.nat (lo - σ.prev.index')) (sint.nat (hi - σ.prev.index'))
    ls (dummy :: σ.ents) $$ Hbig
  ihave #HsubE : entsRO (slice.slice es Loc (lo - σ.prev.index') (hi - σ.prev.index'))
      ((σ.ents.take (uint.Z hi - uint.Z σ.prev.index' - 1).toNat).drop
        (uint.Z lo - uint.Z σ.prev.index' - 1).toNat) $$ []
  · rw [← HE0]
    iunfold entsRO; iunfold entsPts
    iexists _
    iframe Hsub Hbsub
  wp_apply wp_limitSize $$ [$HsubE] as %s1 %nlim ⟨%Hn, Hs1, -⟩
  iunfold entsPts at Hs1
  icases Hs1 with ⟨%ls1, #Hs1, #Hb1⟩
  ihave %Hs1len := ownSlice_len _ _ _ $$ Hs1
  ihave %Hs1wf := ownSlice_wf _ _ _ $$ Hs1
  ihave %Hb1len := entsBig_length $$ Hb1
  have HE0ne : (σ.ents.take (uint.Z hi - uint.Z σ.prev.index' - 1).toNat).drop
      (uint.Z lo - uint.Z σ.prev.index' - 1).toNat ≠ [] := by
    intro Hc; rw [Hc, List.length_nil] at HE0len; omega
  have Hn1 := Hn.2 HE0ne
  have Hnetake : ((σ.ents.take (uint.Z hi - uint.Z σ.prev.index' - 1).toNat).drop
      (uint.Z lo - uint.Z σ.prev.index' - 1).toNat).take nlim ≠ [] := by
    intro Hc
    have := congrArg List.length Hc
    rw [List.length_take, List.length_nil] at this
    omega
  have Hls1ne : ls1 ≠ [] := by
    intro Hc; rw [Hc, List.length_nil] at Hb1len
    exact Hnetake (List.length_eq_zero_iff.1 Hb1len.symm)
  rw [ite_eq_left ⟨by decide, by word, by word, by word⟩]
  ihave #Hs2 := MemoryStorage.Entries.ownSlice_same_ptr_len s1 (slice.fullSlice s1 Loc (W64 0) s1.len s1.len)
    DFrac.discard _ Hls1ne
    (by simp only [slice.fullSlice, sliceIndexRef]; rw [show sint.Z (W64 0) = 0 from rfl,
          go.arrayIndexRef_0])
    (by simp only [slice.fullSlice]; word)
    (by simp only [slice.fullSlice]; word) $$ Hs1
  ihave Hf : memstorageFields ms σ $$ [HhardState Hents_f Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
  · unfold memstorageFields
    iexists _, _, _, _, _, _, _, _
    iframe HhardState Hents_f Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot Hents_cap
    isplitr
    · iunfold entsRO; iunfold entsPts; iexists ls; iframe Hls Hbig
    ipureintro
    exact ⟨Hd0', Hd1'⟩
  wp_auto
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hf Hlog_inv Hen_inv Hcp_inv Hsx_inv Hlk_inv]
  · unfold memstorageInv
    iexists p, ents, M, sv
    rw [Hσ]
    simp only [named]
    iframe # ∗
    ipureintro; exact Hok_inv
  iapply HΦ
  isplitl [Hla]
  · iunfold memLog; iframe Hla; ipureintro; exact Hlab
  isplitl [Hlb]
  · iunfold memLog; iframe Hlb; ipureintro; exact Hlbb
  iright
  isplitl []
  · ipureintro; rfl
  isplitl []
  · iunfold entsRO; iunfold entsPts; iexists ls1; iframe Hs2 Hb1
  ipureintro
  rw [← HE]
  refine ⟨Hnetake, ?_, List.take_prefix _ _⟩
  simp only [slice.fullSlice]

end proof

end EtcdGrove
end Perennial
