/-
Lean-first (no Rocq counterpart).

# The store over raft's cluster with snapshots and reconfiguration (2026-10-28, stage U4a)

What `run`, `New` and `StartCluster` use of the store's cluster (`kvCluster`, `Defs.lean`):

* **The configuration stays the voters'.** A committed conf entry is a `RemoveMember`'s
  (`kv_committed_conf`, `Lemmas.lean`) of a non-voter (`rmShrink_notVoter`), so the store's rule's
  decision on it (`kvRule_decide`) keeps `kvMembership` (`kvMembership_rm`). The positions with no
  conf entry (`NoConfChangeIn`) grow along a log (`noConf_snoc`) and survive extending it
  (`noConf_prefix`).
* **The snapshots' registry** (`kvSnapInv`): allocated empty (`kvSnapInv_alloc`); a snapshot the
  store certifies at a committed prefix of the voters' membership with no conf entry, its data the
  encoded state, is recorded (`kv_snap_make`); a certificate's snapshot is one of those
  (`kv_snap_read`). Each opening of the invariant spends a later credit (raft's `ownSnapsMade` is
  not timeless).
* **`CreateSnapshot` with the token in hand, at a known term** (`CreateSnapshot.unifiedSpec_tok_of`):
  `MemoryStorage.CreateSnapshot.unifiedSpec` as `MemoryStorage.CreateSnapshot.spec_tok` is of
  `.spec` (`MemstorageAU.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Lemmas
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.Storage__InitialState
public import Proof.go_etcd_io.raft.v3.CCApply
public import Proof.go_etcd_io.raft.v3.MemstorageAU

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-! ## Positions without a conf entry -/

theorem noConf_empty (l : List LogEntry) (a : Nat) : NoConfChangeIn l a a := by
  intro k e h1 h2; omega

theorem noConf_prefix (l l' : List LogEntry) (a b : Nat) (h : NoConfChangeIn l a b)
    (hp : l <+: l') (hb : b ≤ l.length) : NoConfChangeIn l' a b := by
  intro k e h1 h2 h3
  apply h k e h1 h2
  obtain ⟨t, rfl⟩ := hp
  rwa [List.getElem?_append_left (by omega)] at h3

theorem noConf_snoc (l : List LogEntry) (a b : Nat) (e : LogEntry) (h : NoConfChangeIn l a b)
    (he : l[b]? = some e) (hc : ¬ e.isConfChange) : NoConfChangeIn l a (b + 1) := by
  intro k e' h1 h2 h3
  by_cases hk : k = b
  · subst hk; rw [he] at h3; cases h3; exact hc
  · exact h k e' h1 (by omega) h3

/-- The last term of a nonempty log, as its terms' list has it. -/
theorem kv_terms_last (l : List LogEntry) (hne : l ≠ []) :
    ∃ t, Option.map LogEntry.term l.getLast? = some t ∧
      (l.map LogEntry.term)[l.length - 1]? = some t := by
  refine ⟨(l.getLast hne).term, ?_, ?_⟩
  · rw [List.getLast?_eq_getLast hne]; rfl
  · have hl : l.length - 1 < l.length := by
      have := List.length_pos_iff.mpr hne; omega
    rw [List.getElem?_map, List.getElem?_eq_getElem hl, List.getLast_eq_getElem]
    rfl

/-! ## The voters' membership -/

/-- A list without repeats is a permutation of the elements of its set. -/
theorem kv_perm_elements_listToSet (l : List w64) (h : l.Nodup) :
    l ≡ₚ GMap.elements (GMap.listToSet l) := by
  refine (List.perm_ext_iff_of_nodup h (GMap.NoDup_elements _)).2 ?_
  intro k; rw [GMap.elem_of_elements, GMap.elem_of_list_to_set]

theorem kv_perm_elements_empty : ([] : List w64) ≡ₚ GMap.elements (∅ : GSet w64) := by
  refine (List.perm_ext_iff_of_nodup List.nodup_nil (GMap.NoDup_elements _)).2 ?_
  intro k
  rw [GMap.elem_of_elements]
  simp only [List.not_mem_nil, false_iff]
  exact GMap.not_elem_of_empty _

/-- The `ConfState` of the store's snapshots (the voters) reports the voters' membership. -/
theorem kvConfState_is : confStateIs (kv.kvConfState kvVoters) kvMembership :=
  ⟨kv_perm_elements_listToSet _ (by decide), kv_perm_elements_empty, kv_perm_elements_empty,
    kv_perm_elements_empty, rfl⟩

/-- **`RemoveMember(id)` that keeps the voters removes a non-voter.** -/
theorem rmShrink_notVoter (id : w64) (H : RmShrink id) : id ∉ GMap.listToSet kvVoters := by
  intro hV
  have h0 : id ≠ W64 0 := by
    intro h; subst h; rw [GMap.elem_of_list_to_set] at hV; revert hV; decide
  obtain ⟨lrn', -, Hm⟩ := H ∅ (fun k hk => absurd hk (GMap.not_elem_of_empty _))
  let c : ConfChangeSingleM := { Type' := W32 1, NodeId' := id }
  have hne : (GMap.delete id (GMap.listToSet kvVoters) : GSet w64) ≠ ∅ := by
    intro he
    -- two of the three voters are not `id`; one of them survives the deletion
    have hmem : ∀ x, x ∈ kvVoters → x ≠ id → x ∈ (GMap.delete id (GMap.listToSet kvVoters) : GSet w64) := by
      intro x hx hxi
      rw [GMap.elem_of_gset] at ⊢
      rw [GMap.lookup_delete_ne _ (Ne.symm hxi)]
      have : x ∈ GMap.listToSet kvVoters := (GMap.elem_of_list_to_set _ _).2 hx
      rw [GMap.elem_of_gset] at this; exact this
    by_cases h1 : (W64 1) = id
    · have := hmem (W64 2) (by decide) (by intro h; rw [← h1] at h; revert h; decide)
      rw [he] at this; exact GMap.not_elem_of_empty _ this
    · have := hmem (W64 1) (by decide) h1
      rw [he] at this; exact GMap.not_elem_of_empty _ this
  have Hs := simpleM_cfgState_removeVoter (GMap.listToSet kvVoters) ∅ c rfl h0 hV hne
    (fun k hk => absurd hk (GMap.not_elem_of_empty _))
  have Hc : ccApplyM (W32 0) [c] (cfgState (GMap.listToSet kvVoters) ∅) =
      some (cfgState (GMap.delete id (GMap.listToSet kvVoters)) ∅) := by
    unfold ccApplyM
    rw [ite_eq_right (by simp)]
    have He : enterJointOf (W32 0) [c].length = some (false, false) := by
      simp [enterJointOf]
    rw [He]
    exact Hs
  have Hm' : ccApplyM (W32 0) [c] (cfgState (GMap.listToSet kvVoters) ∅) =
      some (cfgState (GMap.listToSet kvVoters) lrn') := Hm
  rw [Hc] at Hm'
  have Hinc := congrArg (fun o => o.map (fun s : CCState => s.cfg.incoming)) Hm'
  simp only [Option.map_some, Option.some.injEq, cfgState, cfgM] at Hinc
  have : id ∈ (GMap.delete id (GMap.listToSet kvVoters) : GSet w64) := by rw [Hinc]; exact hV
  rw [GMap.elem_of_gset, GMap.lookup_delete] at this
  cases this

end pure

section reg
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

/-- **`RemoveMember(id)` of a non-voter keeps the voters' membership.** -/
theorem kvMembership_rm (id : w64) (H : RmShrink id) (Hv : kvMembership.Valid) :
    Membership.applyChange (.v1 (rmCC id)) kvMembership = some kvMembership := by
  by_cases h0 : id = W64 0
  · subst h0; exact Membership.applyChange_nodeZero _ _ rfl Hv
  · exact Membership.applyChange_removeAbsent _ _ rfl h0 (rmShrink_notVoter id H) Hv

/-- The store's rule on a `RemoveMember(id)` entry: apply the change. -/
theorem kvRule_decide (pre : List LogEntry) (m : Membership) (e : LogEntry) (id : w64)
    (hty : e.type = W32 1) (hd : ccDecodeV1 e.data = some (rmCC id)) :
    ConfDecision.ofRule (kvRule pre m e) = .apply (.v1 (rmCC id)) := by
  unfold kvRule ccDecode
  rw [if_pos hty, hd]
  rfl

theorem kvSnapN_raftN : (↑kvRaftN : CoPset) ⊆ ⊤ \ ↑kvSnapN :=
  mask_ndot_ne' nroot "kv_raft" "kv_snaps" (by decide)

/-- **The registry's invariant**, from the allocation's empty registry. -/
theorem kvSnapInv_alloc (γr : RKVNames) (E : CoPset) :
    ⊢ ownSnapsMade (GF := GF) γr.cluster [] ={E}=∗ kvSnapInv γr := by
  iintro Hown
  unfold kvSnapInv
  iapply inv_alloc
  inext
  iexists []
  iframe Hown
  iapply (BigSepL.bigSepL_nil).2; iempintro

/-- **A certificate's snapshot is one the store made**: of a committed prefix of the snapshot's
index with no conf entry, at the voters' membership (its lists report it, no auto-leave), its data
the encoded state of the prefix. -/
theorem kv_snap_read (γr : RKVNames) (k : SnapTrip) (E : CoPset) (HE : ↑kvSnapN ⊆ E) :
    ⊢ £ 1 -∗ kvCluster (GF := GF) γr -∗ snapshotCert γr.cluster kvRaftN k ={E}=∗
      ∃ L : List LogEntry, isCommittedLogLb γr.cluster L ∗ confAt γr.cluster L.length kvMembership ∗
        ⌜L.length = uint.nat k.sid.index' ∧ kvSnapOk L k.dat ∧ NoConfChangeIn L 0 L.length ∧
          k.cl.Is kvMembership ∧ k.al = false⌝ := by
  iintro Hlc #Hcl #Hcert
  ihave #Hcl' := Hcl
  unfold kvCluster
  icases Hcl' with ⟨#Hc, -, -, #Hinv⟩
  icases snapshotCert_made γr.cluster kvRaftN k $$ [Hc Hcert] with ⟨%l, %m, #Hl, #Ha, #Hmade, %Hp⟩
  · iframe Hc Hcert
  unfold kvSnapInv
  iinv Hinv with Hb Hclose
  imod lc_fupd_elim_later $$ Hlc Hb with Hb
  icases Hb with ⟨%S, Hown, #HS⟩
  ihave %Hel := snapMade_elem γr.cluster S _ $$ [Hown Hmade]
  · iframe Hown Hmade
  obtain ⟨j, Hj⟩ := List.getElem?_of_mem Hel
  ihave #Hrec := (BigSepL.bigSepL_lookup (Φ := fun _ s => kvSnapRecOk (GF := GF) γr s) Hj) $$ HS
  unfold kvSnapRecOk
  icases Hrec with ⟨%L, #HL, %HLp⟩
  obtain ⟨Hlen, Hconf, Hok, Hnc⟩ := HLp
  simp only at Hlen Hconf Hok
  subst Hconf
  imod Hclose $$ [Hown] with -
  · inext
    iexists S
    iframe Hown HS
  imodintro
  iexists L
  iframe HL
  rw [Hlen]
  iframe Ha
  ipureintro
  rw [Hlen] at Hnc
  exact ⟨Hp.1, Hok, Hnc, Hp.2.2.1, Hp.2.2.2⟩

/-- **Certifying a snapshot the store takes** of the committed prefix `l` (its length `i`, last
term `t`) with no conf entry, at the voters' membership, its `ConfState` the voters, its data `d`
the encoded state of `l`: recorded in the store's registry. -/
theorem kv_snap_make (γr : RKVNames) (l : List LogEntry) (i t : w64) (d : List w8)
    (Hlen : l.length = uint.nat i) (Hlast : Option.map LogEntry.term l.getLast? = some t)
    (Hok : SnapListsOk ⟨⟨t, i⟩, (kv.kvConfState kvVoters).lists, false, d⟩)
    (Hd : kvSnapOk l d) (Hnc : NoConfChangeIn l 0 l.length) :
    ⊢ £ 1 -∗ kvCluster (GF := GF) γr -∗ isCommittedLogLb γr.cluster l -∗
      confAt γr.cluster l.length kvMembership ={⊤}=∗
      snapshotCert γr.cluster kvRaftN ⟨⟨t, i⟩, (kv.kvConfState kvVoters).lists, false, d⟩ := by
  iintro Hlc #Hcl #Hl #Ha
  unfold kvCluster
  icases Hcl with ⟨#Hc, -, -, #Hinv⟩
  unfold kvSnapInv
  iinv Hinv with Hb Hclose
  imod lc_fupd_elim_later $$ Hlc Hb with Hb
  icases Hb with ⟨%S, Hown, #HS⟩
  imod snapshotCert_make γr.cluster kvRaftN (⊤ \ ↑kvSnapN) l i t d kvMembership
      (kv.kvConfState kvVoters) S kvSnapN_raftN Hlen Hlast Hok kvConfState_is
    $$ Hc Hl Ha Hown with ⟨Hown, #Hcert⟩
  imod Hclose $$ [Hown] with -
  · inext
    iexists S ++ [⟨l.length, kvMembership, d⟩]
    iframe Hown
    iapply (BigSepL.bigSepL_snoc (Φ := fun _ s => kvSnapRecOk (GF := GF) γr s)).2
    iframe HS
    unfold kvSnapRecOk
    iexists l
    iframe Hl
    ipureintro
    exact ⟨rfl, rfl, Hd, Hnc⟩
  imodintro
  rw [show (false = kvMembership.autoLeave) from rfl]
  iexact Hcert

end reg

section stok
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `ms.CreateSnapshot(i, cs, data)` at a term the caller knows, with the token in hand:
`MemoryStorage.CreateSnapshot.unifiedSpec` as `MemoryStorage.CreateSnapshot.spec_tok` is of
`.spec`. -/
abbrev CreateSnapshot.unifiedSpec_tok : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (σt : StorState) (x i : w64) (cs : Loc) (dq : DFrac)
    (oc : Option ConfStateM) (data : GoSlice) (bs : List w8) (eood : GoInterface)
    (ts : List w64) (t : w64),
  ts[uint.nat i - 1]? = some t →
  (uint.Z σt.ss.index' < uint.Z i →
    uint.Z σt.prev.index' ≤ uint.Z i ∧ uint.Z i ≤ uint.Z x) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Htok" ∷ memSnapTok ms γs σt ∗
      "#Hfw" ∷ memFloorTok ms γs x ∗
      "#Hts" ∷ memTermsAt γs ts ∗
      "Hcs" ∷ (match oc with
               | none => iprop(⌜cs = null⌝)
               | some c => ownCSM cs dq c) ∗
      "Hdata" ∷ data ↦* bs ∗
      "#Hcert" ∷ memStorCert γs
        (snapTrip (memSnapCreated σt i t oc bs) (memSnapCreated σt i t oc bs).Metadata'.ConfState'.lists) ∗
      "#Herr" ∷ globalAddr ErrSnapOutOfDate ↦□ eood }}
    (App (App (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"CreateSnapshot"))
      (Val #i)) (Val #cs)) (Val #data))
  {{ (snap' : Loc) (err : GoInterface), RET (PairV #snap' #err);
      (match oc with
       | none => iprop(⌜cs = null⌝)
       | some c => ownCSM cs dq c) ∗
      ((⌜uint.Z i ≤ uint.Z σt.ss.index' ∧ snap' = null ∧ err = eood⌝ ∗
        memSnapTok ms γs σt ∗ data ↦* bs) ∨
      (⌜uint.Z σt.ss.index' < uint.Z i ∧ err = interface.nil⌝ ∗
        ownSnapM snap' (DFrac.own 1) (memSnapCreated σt i t oc bs) ∗
        memSnapTok ms γs { σt with ss := entryID.mk t i,
                                   scs := (memSnapCreated σt i t oc bs).Metadata'.ConfState'.lists,
                                   sal := (memSnapCreated σt i t oc bs).Metadata'.ConfState'.AutoLeave',
                                   sdat := bs })) }}

omit [StorageModel GF] in
private theorem mask_empty_sub' : (∅ : CoPset) ⊆ ⊤ \ ↑memSnapN := Std.LawfulSet.empty_subset

omit [StorageModel GF] in
/-- `MemstorageAU.lean`'s `wp_later_frame` (private there). -/
private theorem wp_later_frame' {e : Expr} {Φ : val → IProp GF} {R : IProp GF}
    (h : toVal e = none) :
    ⊢ ▷ R -∗ WP e {{ v, R -∗ Φ v }} -∗ WP e {{ Φ }} := by
  iintro HR Hwp
  iapply (wp_wand (Φ := fun v => iprop(R ∗ (R -∗ Φ v)))) $$ [HR Hwp]
  · iapply (wp_frame_step_l' h (fun _ hp => hp))
    iframe
  · iintro %v ⟨HR, H⟩
    iapply H $$ HR

omit [StorageModel GF] in
theorem CreateSnapshot.unifiedSpec_tok_of
    (wp_CreateSnapshot : MemoryStorage.CreateSnapshot.unifiedSpec (GF := GF) (hG := hG)) :
    CreateSnapshot.unifiedSpec_tok (GF := GF) (hG := hG) := by
  intro ms γs σt x i cs dq oc data bs eood ts t Hts Hpre
  wp_start_folded as ⟨Htok, #Hfw, #Hts, Hcs, Hdata, #Hcert, #Herr⟩
  icases (memSnapTok_split ms γs σt).1 $$ Htok with ⟨#Hro, Hak, Htg⟩
  ihave Hcs : memCsArg cs dq oc $$ [Hcs]
  · cases oc <;> simp only [memCsArg] <;> iexact Hcs
  iapply (wp_later_frame' rfl) $$ HΦ
  iapply wp_CreateSnapshot ms γs x i cs dq oc data bs eood ts t Hts $$ [Hak Hcs Hdata] [Htg]
  · iframe Hpkg Hro Hak Hfw Hts Hcs Hdata Herr
  iapply fupd_mask_intro mask_empty_sub'
  iintro Hclose
  iexists σt
  iframe Htg Hcert
  isplitr
  · ipureintro; exact Hpre
  isplit
  · iintro %Hle Htg
    imod Hclose with -
    imodintro
    iintro Hak Hcs Hdata
    iintro HΦ
    iapply HΦ
    isplitl [Hcs]
    · cases oc <;> simp only [memCsArg] <;> iexact Hcs
    ileft
    isplitr
    · ipureintro; exact ⟨Hle, rfl, rfl⟩
    iframe Hdata
    iapply (memSnapTok_split ms γs σt).2
    iframe Hro Hak Htg
  · iintro %Hlt Htg
    imod Hclose with -
    imodintro
    iintro %snap' Hsnap Hak Hcs
    iintro HΦ
    iapply HΦ
    isplitl [Hcs]
    · cases oc <;> simp only [memCsArg] <;> iexact Hcs
    iright
    isplitr
    · ipureintro; exact ⟨Hlt, rfl⟩
    iframe Hsnap
    iapply (memSnapTok_split ms γs _).2
    unfold memStorCreated
    iframe Hro Hak Htg

end stok

end EtcdGrove
end Perennial
