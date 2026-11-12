/- `MemoryStorage.Append` (`storage.go:280`), proved 2026-10-10 (Lean-first). -/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.MemoryStorage__Append
public import RaftWitness.Spec.go_etcd_io.raft.v3.MemoryStorage__firstIndex
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import RaftWitness.Proof.go_etcd_io.raft.v3.LemmasMemstorage
public import RaftWitness.Proof.go_etcd_io.raft.v3.InvRaftlog

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The entries the switch's first arm leaves (`append(ms.ents[:offset:offset],
entries...)`): the dummy, the stored entries below the batch, the batch. -/
private theorem append_cut (dummy : EntryM) (σ : StorState) (e0 : EntryM)
    (rest : List EntryM) (k : Nat)
    (Hk : (k : Int) = uint.Z e0.Index' - uint.Z σ.prev.index') (Hk1 : 1 ≤ k) :
    (dummy :: σ.ents).take k ++ e0 :: rest = dummy :: storApp σ (e0 :: rest) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [storApp, List.take_succ_cons, List.cons_append]
  rw [show (uint.Z e0.Index' - uint.Z σ.prev.index' - 1).toNat = j by omega]

/-- ... and the second (`append(ms.ents, entries...)`, the batch right after the stored
entries). -/
private theorem append_end (dummy : EntryM) (σ : StorState) (e0 : EntryM)
    (rest : List EntryM)
    (Hk : (σ.ents.length : Int) + 1 = uint.Z e0.Index' - uint.Z σ.prev.index') :
    (dummy :: σ.ents) ++ e0 :: rest = dummy :: storApp σ (e0 :: rest) := by
  simp only [storApp, List.cons_append]
  rw [List.take_of_length_le (by omega)]

/-- (D19i part 1) The lock's invariant after the append: `done` at the appended state, the fields
the old ones (the contents cut at `c`) with the batch, which starts above the cut and above the
application's snapshot (both within the floor, which the batch is above). -/
private theorem append_close (ms : Loc) (γs : MemStorNames) (σ σL S0 : StorState) (c : entryID)
    (H : List StorState) (p : List EntryM) (e0 : EntryM) (hp : p.head? = some e0)
    (Hde : DataEq σ σL) (Hcok : CutOk σL c ∧ uint.Z c.index' ≤ uint.Z S0.ss.index')
    (Hccap : uint.Z c.index' ≤ γs.cap)
    (Hcb : uint.Z c.index' < uint.Z e0.Index')
    (Hhi : uint.Z e0.Index' ≤ uint.Z σ.prev.index' + (σ.ents.length : Int) + 1)
    (Hsb : (S0.ss = σL.ss ∧ S0.scs = σL.scs ∧ S0.sal = σL.sal) ∨
      uint.Z S0.ss.index' < uint.Z e0.Index')
    (Hok : HistOk (H ++ [storAbsorb { σ with pend := p }]))
    (Hpb : uint.Z σ.prev.index' + ((storApp σ p).length : Int) < 2^61) :
    ⊢ monoListAuthOwn (GF := GF) γs.done (1 : Qp).half (H ++ [storAbsorb { σ with pend := p }]) -∗
      monoListLbOwn γs.hist (H ++ [storAbsorb { σ with pend := p }]) -∗ memKey γs.lk -∗
      memstorageFields ms { memCut σL c with ents := storApp (memCut σL c) p, pend := [] } -∗
      ghostVar γs.cb (1 : Qp).half c -∗ monoNatAuthOwn γs.bd 1 (uint.Z c.index').toNat -∗
      (⌜c = σL.prev⌝ ∨ memFlLb γs c.index') -∗ ghostVar γs.sn memQ (snapPart S0) -∗
      (⌜S0.ss = σL.ss ∧ S0.scs = σL.scs ∧ S0.sal = σL.sal⌝ ∨
        (⌜uint.Z σL.ss.index' < uint.Z S0.ss.index' ∧ uint.Z σL.prev.index' ≤ uint.Z S0.ss.index' ∧
            termAt σL.prev σL.ents S0.ss.index' = some S0.ss.term'⌝ ∗ memFlLb γs S0.ss.index')) -∗
      memstorageInv ms γs := by
  iintro Hd #Hlb Hlk Hf Hcbv Hbd #Hcfl Hsq #Hsrel
  obtain ⟨Hp1, Hp2, Hp3, Hp4, Hp5, -⟩ := Hde
  have HcokS : CutOk σ c := by
    obtain ⟨h1, h2, h3⟩ := Hcok.1
    refine ⟨by rw [Hp1]; exact h1, ?_, by rw [Hp1, Hp2]; exact h3⟩
    unfold EtcdGrove.stLast at h2 ⊢; rw [Hp1, Hp2]; exact h2
  have Hc1 := HcokS.1
  unfold memstorageInv
  iexists storAbsorb { σ with pend := p }, c
  isplitl [Hd Hlk]
  · unfold memInvGhost
    iexists H ++ [storAbsorb { σ with pend := p }]
    iframe Hd Hlb Hlk
    ipureintro; exact ⟨by simp, Hok⟩
  isplitl [Hf]
  · iapply memstorageFields_congr $$ Hf
    · rfl
    · simp only [memCut, storAbsorb, storApp_pend]
      rw [← memCut]
      rw [storApp_memCut Hcok.1 p (fun e he => by rw [hp] at he; cases he; exact Hcb)]
      simp only [storApp]
      rw [Hp1, Hp2]
  isplitr
  · ipureintro
    simp only [storAbsorb, storApp_pend]
    exact Hpb
  iunfold memCutInv
  iexists S0
  iframe Hcbv Hbd Hsq
  isplitr
  · icases Hcfl with (%Hc | #Hc)
    · ileft; ipureintro; rw [Hc]; simp only [storAbsorb]; exact Hp1.symm
    · iright; iexact Hc
  have Hhi' : ∀ e, p.head? = some e →
      uint.Z e.Index' ≤ uint.Z σ.prev.index' + (σ.ents.length : Int) + 1 := by
    intro e he; rw [hp] at he; cases he; exact Hhi
  isplitr
  · ipureintro
    refine ⟨?_, Hcok.2⟩
    have := HcokS.app p (fun e he => by rw [hp] at he; cases he; exact Hcb) Hhi'
    simpa only [storAbsorb, storApp_pend] using this
  isplitr
  · ipureintro; exact Hccap
  icases Hsrel with (%Hs | ⟨%Hs, #Hc⟩)
  · ileft; ipureintro
    simp only [storAbsorb]
    rw [Hp3, Hp4, Hp5]; exact Hs
  · iright
    iframe Hc
    ipureintro
    obtain ⟨h1, h2, h3⟩ := Hs
    simp only [storAbsorb, storApp_pend]
    have Hlt : uint.Z S0.ss.index' < uint.Z e0.Index' := by
      rcases Hsb with ⟨Hs1, -, -⟩ | Hs
      · rw [Hs1] at h1; omega
      · exact Hs
    refine ⟨by rw [Hp3]; exact h1, by rw [Hp1]; exact h2, ?_⟩
    rw [termAt_storApp_below σ p _ (fun e he => by
        rw [hp] at he; cases he; exact ⟨Hlt, Hhi⟩) (by rw [Hp1]; exact h2), Hp1, Hp2]
    exact h3

theorem MemoryStorage.Append.wp_proof
    (wp_MemoryStorage_firstIndex : MemoryStorage.firstIndex.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG)) :
    MemoryStorage.Append.spec (GF := GF) (hG := hG) := by
  intro ms γs σ p s dq Hbnd
  wp_start as ⟨Htok, Hs⟩
  iunfold entsPts at Hs
  icases Hs with ⟨%lsb, Hsb, #Hbigb⟩
  ihave %Hblen := entsBig_length $$ Hbigb
  icases Htok with (%Hnil | Htok)
  · -- an empty batch: `Append` returns at once
    subst Hnil
    ihave %Hslen := ownSlice_len $$ Hsb
    simp only [List.length_nil] at Hblen
    rw [List.length_eq_zero_iff.1 Hblen] at Hslen
    simp only [List.length_nil] at Hslen
    wp_auto
    wp_apply wp_with_defer as %defer defer
    wp_if_destruct
    · iapply HΦ
      isplitr
      · ileft; ipureintro; trivial
      iunfold entsPts
      iexists lsb
      iframe Hsb Hbigb
    · exfalso
      apply Hif
      word
  iunfold memAppendTok at Htok
  icases Htok with ⟨#Hinit, #Hmu, %H, %D, Hdone, Hhist, Hep, %Htk⟩
  obtain ⟨Hlast, Hpe, ⟨Hpne, Hpok⟩, Hpab, HDH, HDne, HR, Hok⟩ := Htk
  obtain ⟨e0, rest, rfl⟩ : ∃ e0 rest, p = e0 :: rest := by
    cases p with
    | nil => exact absurd rfl Hpne
    | cons a b => exact ⟨a, b, rfl⟩
  obtain ⟨He0lo0, He0hi0, -⟩ := Hpok e0 rfl
  have Hab0 := Hpab e0 rfl
  have Hb0 := Hbnd e0 rfl
  ihave %Hslen := ownSlice_len $$ Hsb
  simp only [List.length_cons] at Hslen Hb0 Hblen
  icases entsBig_lookup lsb (e0 :: rest) 0 e0 rfl $$ Hbigb with ⟨%lb0, %Hlb0, #Heb0⟩
  wp_auto
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
  icases Hinv with ⟨%σL, %c, Hinv⟩
  iNamedSuffix Hinv "_inv"
  iunfold memInvGhost at Hgs_inv
  icases Hgs_inv with ⟨%Dl, Hd_inv, #Hlb_inv, %HD, Hlk_inv⟩
  -- the writer's half: the contents have the data of the state the batch was handed out at
  -- (D19i part 1: `done` may lag by floor raises)
  icases monoAuth_agree_keep γs.done _ _ Dl D $$ [$Hd_inv $Hdone] with ⟨⟨Hd_inv, Hdone⟩, %HDD⟩
  subst HDD
  have Hde : DataEq σ σL := RaiseOnly.last HDH HR HD.1 Hlast
  iunfold memCutInv at Hcut_inv
  iNamed Hcut_inv
  -- (D19i part 1) the cut, and the application's snapshot, are below the batch: within the floor,
  -- which the batch is above (the token's half of `hist` bounds every floor witness)
  have Hflw : ∀ (Lc : List StorState) (w : StorState), Lc <+: H ++ [storAbsorb { σ with pend := e0 :: rest }] →
      Lc.getLast? = some w → uint.Z w.fl < uint.Z e0.Index' := by
    intro Lc w Hpre hw
    have := Hok.last_mono Hpre hw
      (show (H ++ [storAbsorb { σ with pend := e0 :: rest }]).getLast? =
        some (storAbsorb { σ with pend := e0 :: rest }) by simp)
    simp only [storAbsorb] at this
    omega
  ihave %Hcb : ⌜uint.Z c.index' < uint.Z e0.Index'⌝ $$ [Hhist]
  · icases Hcfl with (%Hc | #Hc)
    · ipureintro; rw [Hc, ← Hde.1]; exact He0lo0
    · iunfold memFlLb at Hc
      icases Hc with ⟨%Lc, #HLc, %HLcok⟩
      icases mono_list_auth_lb_valid γs.hist _ _ Lc $$ Hhist HLc with %Hpre
      obtain ⟨-, w, hw, hx⟩ := HLcok
      ipureintro
      have := Hflw Lc w Hpre.2 hw
      omega
  ihave %Hsb : ⌜(S.ss = σL.ss ∧ S.scs = σL.scs ∧ S.sal = σL.sal) ∨
      uint.Z S.ss.index' < uint.Z e0.Index'⌝ $$ [Hhist]
  · icases Hsrel with (%Hs | ⟨%Hs, #Hc⟩)
    · ipureintro; left; exact Hs
    · iunfold memFlLb at Hc
      icases Hc with ⟨%Lc, #HLc, %HLcok⟩
      icases mono_list_auth_lb_valid γs.hist _ _ Lc $$ Hhist HLc with %Hpre
      obtain ⟨-, w, hw, hx⟩ := HLcok
      ipureintro
      right
      have := Hflw Lc w Hpre.2 hw
      omega
  ihave #Hlbn := monoListLbOwn_get γs.hist _ _ $$ Hhist
  -- the fields are the contents cut at `c`: the batch continues them, as the view
  have Hlast' := memCut_stLast Hcok.1
  have He0lo : uint.Z (memCut σL c).prev.index' < uint.Z e0.Index' := Hcb
  have He0hi : uint.Z e0.Index' ≤ uint.Z (memCut σL c).prev.index' +
      ((memCut σL c).ents.length : Int) + 1 := by
    unfold EtcdGrove.stLast at Hlast'
    rw [Hde.1, Hde.2.1] at He0hi0
    simp only [memCut] at Hlast' ⊢
    omega
  have Hpb_inv' : uint.Z (memCut σL c).prev.index' + ((memCut σL c).ents.length : Int) < 2^61 := by
    unfold EtcdGrove.stLast at Hlast'; simp only [memCut] at Hlast' ⊢; omega
  have Hpbσ : uint.Z σ.prev.index' + ((storApp σ (e0 :: rest)).length : Int) < 2^61 := by
    simp only [storApp, List.length_append, List.length_take, List.length_cons]
    omega
  generalize Hσf : memCut σL c = σp at He0lo He0hi Hpb_inv' ⊢
  iNamed Hfields_inv
  ihave Hf : memstorageFields ms σp $$ [HhardState Hents_f Hents Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
  · unfold memstorageFields
    iexists hp, es, dummy, nfi, nli, nen, nte, nsn
    iframe
    ipureintro; exact Hdummy
  wp_apply wp_MemoryStorage_firstIndex ms σp Hpb_inv' $$ [$Hf] as %fi ⟨%Hfi, Hf⟩
  have Hlenz : uint.Z s.len = (rest.length : Int) + 1 := by
    have := Hslen.1; rw [Hblen] at this; word
  -- `entries[0].GetIndex()`, read four times
  rw [ite_eq_left ⟨by word, by word⟩]
  wp_apply wp_load_slice_index s (sint.Z (W64 0)) lsb dq lb0 (by word) $$ [Hsb] as Hsb
  · iframe Hsb; ipureintro; exact Hlb0
  wp_apply wp_GetIndex.1 lb0 DFrac.discard e0 $$ [Heb0] with -
  · iframe Heb0
  -- `last < first`: no, the batch starts at or above `first`
  wp_if_destruct
  · exfalso; word
  rw [ite_eq_left ⟨by word, by word⟩]
  wp_apply wp_load_slice_index s (sint.Z (W64 0)) lsb dq lb0 (by word) $$ [Hsb] as Hsb
  · iframe Hsb; ipureintro; exact Hlb0
  wp_apply wp_GetIndex.1 lb0 DFrac.discard e0 $$ [Heb0] with -
  · iframe Heb0
  -- `first > entries[0].Index`: no, the batch starts above the boundary
  wp_if_destruct
  · exfalso; word
  -- `offset := entries[0].GetIndex() - ms.ents[0].GetIndex()`
  iNamed Hf
  icases Hents with #Hents
  ihave %Hcl := entsRO_cons_len $$ Hents
  iunfold entsRO at Hents
  iunfold entsPts at Hents
  icases Hents with ⟨%ls, #Hls, #Hbig⟩
  ihave %Hbl := entsBig_length $$ Hbig
  icases entsBig_lookup ls (dummy :: σp.ents) 0 dummy rfl $$ Hbig with ⟨%l0, %Hl0, #He0⟩
  rw [ite_eq_left ⟨by word, by word⟩]
  wp_apply wp_load_slice_index s (sint.Z (W64 0)) lsb dq lb0 (by word) $$ [Hsb] as Hsb
  · iframe Hsb; ipureintro; exact Hlb0
  wp_apply wp_GetIndex.1 lb0 DFrac.discard e0 $$ [Heb0] with -
  · iframe Heb0
  rw [ite_eq_left ⟨by word, by word⟩]
  wp_apply wp_load_slice_index es (sint.Z (W64 0)) ls DFrac.discard l0 (by word) $$ [Hls] with -
  · iframe Hls; ipureintro; exact Hl0
  wp_apply wp_GetIndex.1 l0 DFrac.discard dummy $$ [He0] with -
  · iframe He0
  obtain ⟨Hd0i, Hd0t⟩ := Hdummy
  rw [Hd0i]
  have Hoff : uint.Z (e0.Index' - σp.prev.index') = uint.Z e0.Index' - uint.Z σp.prev.index' := by
    word
  have Heslen : uint.Z es.len = (σp.ents.length : Int) + 1 := by
    have := Hcl.2; word
  ihave %Hwf := ownSlice_wf $$ Hls
  -- the state the batch leaves, its bound, and `done` at it
  have Hpb' : uint.Z σp.prev.index' + ((storApp σp (e0 :: rest)).length : Int) < 2^61 := by
    simp only [storApp, List.length_append, List.length_take, List.length_cons]
    omega
  imod monoHalves_update γs.done Dl (H ++ [storAbsorb { σ with pend := e0 :: rest }])
    (HDH.trans (List.prefix_append _ _)) $$ Hd_inv Hdone with ⟨Hd_inv, Hdone⟩
  wp_if_destruct
  · -- the batch overwrites stored entries: `append(ms.ents[:offset:offset], entries...)`
    have Hcut := of_decide_eq_true Hif.symm
    rw [Hoff] at Hcut
    rw [ite_eq_left ⟨by word, by word, by word, by word⟩]
    icases (ownSlice_slice (W64 0) (e0.Index' - σp.prev.index') es DFrac.discard ls
      ⟨by word, by word, by word⟩).1 $$ Hls with ⟨-, #Hsub, -⟩
    have Hk : (sint.nat (e0.Index' - σp.prev.index') : Int) =
        uint.Z e0.Index' - uint.Z σp.prev.index' := by word
    have Hsubeq : subslice (sint.nat (W64 0)) (sint.nat (e0.Index' - σp.prev.index')) ls =
        ls.take (sint.nat (e0.Index' - σp.prev.index')) := by
      simp only [subslice]; rfl
    ihave #Hsub1 : slice.slice es Loc (W64 0) (e0.Index' - σp.prev.index') ↦*□
        ls.take (sint.nat (e0.Index' - σp.prev.index')) $$ [Hsub]
    · rw [← Hsubeq]; iexact Hsub
    have Hne : ls.take (sint.nat (e0.Index' - σp.prev.index')) ≠ [] := by
      intro Hc
      have := congrArg List.length Hc
      simp only [List.length_take, Hbl, List.length_cons, List.length_nil] at this
      omega
    ihave #Hsub2 := ownSlice_same_ptr_len
      (slice.slice es Loc (W64 0) (e0.Index' - σp.prev.index'))
      (slice.fullSlice es Loc (W64 0) (e0.Index' - σp.prev.index')
        (e0.Index' - σp.prev.index'))
      _ _ Hne rfl rfl (by simp only [slice.fullSlice]; word) $$ Hsub1
    ihave Hcap0 := ownSliceCap_empty (V := Loc)
      (slice.fullSlice es Loc (W64 0) (e0.Index' - σp.prev.index')
        (e0.Index' - σp.prev.index')) (by simp only [slice.fullSlice])
      (by simp only [slice.fullSlice]; word)
    wp_auto
    wp_apply wp_slice_append_persistent (V := Loc) _ _ s lsb dq
      $$ [$Hsub2 $Hcap0 $Hsb] as %es' ⟨#Hes', Hes'_cap, Hsb⟩
    ihave #Hbt := entsBig_take (sint.nat (e0.Index' - σp.prev.index')) ls (dummy :: σp.ents) $$ Hbig
    ihave #Hba := entsBig_app _ lsb _ (e0 :: rest) $$ [Hbt Hbigb]
    · iframe Hbt Hbigb
    ihave #Hes2 : entsRO es' (dummy :: storApp σp (e0 :: rest)) $$ []
    · rw [← append_cut dummy σp e0 rest _ Hk (by omega)]
      iunfold entsRO; iunfold entsPts
      iexists _
      iframe Hes' Hba
    -- the deferred `ms.Unlock()`, at the appended state
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock
      $$ [$Hmu $Hlocked Hd_inv Hlk_inv HhardState Hents_f Hes'_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot Hcb Hbd Hsq]
    · inext
      ihave Hf' : memstorageFields ms { σp with ents := storApp σp (e0 :: rest), pend := [] } $$ [HhardState Hents_f Hes'_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
      · unfold memstorageFields
        iexists hp, es', dummy, nfi, nli, nen, nte, nsn
        simp only [named]
        iframe
        isplitr
        · iexact Hes2
        ipureintro
        exact ⟨Hd0i, Hd0t⟩
      rw [← Hσf]
      iapply append_close ms γs σ σL S c H (e0 :: rest) e0 rfl Hde Hcok Hccap Hcb He0hi0 Hsb Hok Hpbσ
        $$ Hd_inv Hlbn Hlk_inv Hf' Hcb Hbd Hcfl Hsq Hsrel
    iapply HΦ
    isplitr [Hsb]
    · iright
      unfold memAppendedTok
      iexists H, Dl
      iframe Hdone Hhist Hep
      ipureintro; exact Hpbσ
    iunfold entsPts
    iexists lsb
    iframe Hsb Hbigb
  wp_if_destruct
  · -- the batch continues the stored entries: `append(ms.ents, entries...)`
    have Hend := of_decide_eq_true Hif.symm
    have Hk : (σp.ents.length : Int) + 1 = uint.Z e0.Index' - uint.Z σp.prev.index' := by
      have H1 : uint.Z es.len = uint.Z (e0.Index' - σp.prev.index') := by rw [Hend]
      omega
    wp_apply wp_slice_append_persistent (V := Loc) es ls s lsb dq
      $$ [$Hls $Hents_cap $Hsb] as %es' ⟨#Hes', Hes'_cap, Hsb⟩
    ihave #Hba := entsBig_app ls lsb (dummy :: σp.ents) (e0 :: rest) $$ [Hbig Hbigb]
    · iframe Hbig Hbigb
    ihave #Hes2 : entsRO es' (dummy :: storApp σp (e0 :: rest)) $$ []
    · rw [← append_end dummy σp e0 rest Hk]
      iunfold entsRO; iunfold entsPts
      iexists _
      iframe Hes' Hba
    -- the deferred `ms.Unlock()`, at the appended state
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock
      $$ [$Hmu $Hlocked Hd_inv Hlk_inv HhardState Hents_f Hes'_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot Hcb Hbd Hsq]
    · inext
      ihave Hf' : memstorageFields ms { σp with ents := storApp σp (e0 :: rest), pend := [] } $$ [HhardState Hents_f Hes'_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
      · unfold memstorageFields
        iexists hp, es', dummy, nfi, nli, nen, nte, nsn
        simp only [named]
        iframe
        isplitr
        · iexact Hes2
        ipureintro
        exact ⟨Hd0i, Hd0t⟩
      rw [← Hσf]
      iapply append_close ms γs σ σL S c H (e0 :: rest) e0 rfl Hde Hcok Hccap Hcb He0hi0 Hsb Hok Hpbσ
        $$ Hd_inv Hlbn Hlk_inv Hf' Hcb Hbd Hcfl Hsq Hsrel
    iapply HΦ
    isplitr [Hsb]
    · iright
      unfold memAppendedTok
      iexists H, Dl
      iframe Hdone Hhist Hep
      ipureintro; exact Hpbσ
    iunfold entsPts
    iexists lsb
    iframe Hsb Hbigb
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
