/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/tracecheck/Cluster__handleReady.lean`.
Lean-first (no Rocq counterpart).

No snapshot (`IsEmptySnap` of `nil`); `Append` takes the `Ready`'s `appendRight` (as the
`MemoryStorage`'s range, `memStorLog_to`) and gives the receipt (nothing frozen); the hard state, if
any, is set. The apply loop keeps the view `ViewOk` at the log applied so far. A conf entry at position
`k`: a `ConfChange` is a bootstrap one (`tcOps_v1_boot`, then the bootstrap log's `AddNode` of a voter:
`BootLogFacts`), so it decodes and leaves the voters' membership (`Membership.applyChange_addVoter`),
decided by `confPolicy_decide` and applied by `node.ApplyConfChange`; a `ConfChangeV2` is refuted
(`tcOps_emptyV2`, `committed_emptyV2_joint` against the simple membership).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Cluster__handleReady
public import Spec.go_etcd_io.raft.v3.IsEmptySnap
public import Spec.go_etcd_io.raft.v3.IsEmptyHardState
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Append
public import Spec.go_etcd_io.raft.v3.MemoryStorage__SetHardState
public import Spec.go_etcd_io.raft.v3.node__ApplyConfChange
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetData
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import Spec.google_golang_org.protobuf.proto.UnmarshalConfChange

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 ProbeA

section pure
variable [GooseExts]

theorem tc_run_lt (k len : w64) (n m : Nat) (h : sint.Z k < sint.Z len) (h1 : m = sint.nat len)
    (h2 : m = n) (h0 : 0 ≤ sint.Z k) : sint.nat k < n := by
  subst h1 h2; word

theorem tc_run_eq (k len : w64) (n m : Nat) (h : ¬ sint.Z k < sint.Z len) (h1 : m = sint.nat len)
    (h2 : m = n) (hk : sint.Z k ≤ (n : Int)) : sint.nat k = n := by
  subst h1 h2; word

theorem tc_run_succ (k len : w64) (h : sint.Z k < sint.Z len) (h0 : 0 ≤ sint.Z k) :
    0 ≤ sint.Z (k + W64 1) ∧ sint.Z (k + W64 1) = sint.Z k + 1 ∧
      sint.nat (k + W64 1) = sint.nat k + 1 := by
  refine ⟨by word, by word, by word⟩

theorem tc_toNat_sint (k : w64) (_h : 0 ≤ sint.Z k) : (sint.Z k).toNat = sint.nat k := by word

/-- The Go entry at position `k` of a log's entries. -/
theorem tc_toEntries_get (l : List LogEntry) (base k : Nat) (e : LogEntry) (h : l[k]? = some e) :
    (LogEntry.toEntries l base)[k]? = some (e.toEntryM (W64 (base + k + 1))) := by
  unfold LogEntry.toEntries; rw [List.getElem?_mapIdx, h]; rfl

theorem tc_toEntries_length (l : List LogEntry) (base : Nat) :
    (LogEntry.toEntries l base).length = l.length := by
  unfold LogEntry.toEntries; exact List.length_mapIdx

/-- **The `app`'s view, as the apply loop keeps it**: the voters' membership, applied up to a point
at most `p`, past which no conf entry of `l` before `p`. -/
def ViewAt (l : List LogEntry) (p : Nat) (v : ConfigView) : Prop :=
  v.membership = tcMem ∧ v.applied ≤ p ∧ NoConfChangeIn l v.applied p

theorem viewAt_start (D ce : List LogEntry) (v : ConfigView) (h : ViewOk D v) :
    ViewAt (D ++ ce) D.length v := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun k e hlo hhi hk => h3 k e hlo hhi ?_⟩
  rw [List.getElem?_append_left hhi] at hk; exact hk

theorem viewAt_end (l : List LogEntry) (v : ConfigView) (h : ViewAt l l.length v) :
    ViewOk l v := h

theorem viewAt_noConf (l : List LogEntry) (p : Nat) (e : LogEntry) (v : ConfigView)
    (h : ViewAt l p v) (hk : l[p]? = some e) (hc : ¬ e.isConfChange) : ViewAt l (p + 1) v := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, by omega, fun k e' hlo hhi hk' => ?_⟩
  by_cases hkp : k = p
  · subst hkp; rw [hk] at hk'; cases hk'; exact hc
  · exact h3 k e' hlo (by omega) hk'

theorem viewAt_applied (l : List LogEntry) (p : Nat) :
    ViewAt l (p + 1) ⟨p + 1, tcMem⟩ :=
  ⟨rfl, Nat.le_refl _, fun _ _ h1 h2 _ => absurd h2 (by simp only at h1; omega)⟩

theorem tcMem_valid_mem (id : w64) (h : id ∈ tcVoters) : id ∈ tcMem.voters := by
  show id ∈ GMap.listToSet tcVoters
  exact (GMap.elem_of_list_to_set id tcVoters).2 h

end pure

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A committed `ConfChange` is a voter's bootstrap `AddNode`** (§2.3, A6's `ConfChange` arm): at
its position (a bootstrap one, `tcOps_v1_boot`) the voters' membership; it decodes, applies leaving
the membership, and the policy records it applied. -/
theorem tc_conf1 (γ : Cluster) (boot l : List LogEntry) (p : Nat) (e : LogEntry)
    (HB : BootLogFacts boot) (hk : l[p]? = some e) (ht : e.type = W32 1) :
    ⊢ isCluster (GF := GF) γ tcRaftN -∗ tcOpsInv γ boot -∗ confPolicy γ tcConfN tcRule -∗
      isCommittedLogLb γ boot -∗ isCommittedLogLb γ l -∗ confAt γ p tcMem ={⊤}=∗
      ∃ cm : ConfChangeM, ⌜ccDecodeV1 e.data = some cm ∧
          Membership.applyChange (.v1 cm) tcMem = some tcMem⌝ ∗
        confDecided γ p (.apply (.v1 cm)) := by
  iintro #Hc #Hops #Hpol #Hb #Hl #Ha
  imod tcOps_v1_boot γ boot l ⊤ HB (fun _ _ => CoPset.mem_full) $$ Hops Hb Hl with %Hv1
  have Hp := Hv1 p e hk ht
  icases isCommittedLogLb_agree γ boot l $$ [Hb Hl] with %Hag
  · iframe Hb Hl
  have Hbk : boot[p]? = some e := by
    rcases Hag with h | h
    · obtain ⟨x, rfl⟩ := h; rw [List.getElem?_append_left Hp] at hk; exact hk
    · obtain ⟨x, rfl⟩ := h
      have hpl : p < l.length := by
        have := (List.getElem?_eq_some_iff.1 hk).1; exact this
      rw [List.getElem?_append_left hpl]; exact hk
  obtain ⟨id, ctx, Hid, -, -, -, Hm⟩ := HB.2.2 p e Hbk
  have Hdec1 : ccDecodeV1 e.data = some ⟨W32 0, id, ctx, W64 0⟩ := Hm
  ihave %Hv := confAt_valid γ p tcMem $$ Ha
  have Hin : id ∈ tcVoters := List.mem_of_getElem? Hid
  have Hap : Membership.applyChange (.v1 ⟨W32 0, id, ctx, W64 0⟩) tcMem = some tcMem :=
    Membership.applyChange_addVoter _ _ rfl (tcMem_valid_mem id Hin) Hv
  have Hdec : ccDecode e = some (.v1 ⟨W32 0, id, ctx, W64 0⟩) := by
    unfold ccDecode; simp only [ht, ↓reduceIte, Hdec1]; rfl
  have hs : (ConfDecision.ofRule (tcRule (l.take p) tcMem e)).step tcMem = some tcMem := by
    simp only [tcRule, Hdec, ConfDecision.ofRule, ConfDecision.step]; exact Hap
  imod confPolicy_decide γ tcRaftN tcConfN ⊤ tcRule l p e tcMem tcMem hk (.inl ht)
    (fun _ _ => CoPset.mem_full) hs $$ [Hc Hpol Hl Ha] with #Hd
  · iframe Hc Hpol Hl Ha
  imodintro
  iexists ⟨W32 0, id, ctx, W64 0⟩
  isplitr
  · ipureintro; exact ⟨Hdec1, Hap⟩
  simp only [tcRule, Hdec, ConfDecision.ofRule]
  iexact Hd

/-- **No committed `ConfChangeV2` at the voters' membership** (§2.3, A6's `ConfChangeV2` arm, refuted):
it is an empty one (`tcOps_emptyV2`), committed only where the configuration is joint
(`committed_emptyV2_joint`), and the voters' simple membership is not. -/
theorem tc_noConf2 (γ : Cluster) (boot l : List LogEntry) (p : Nat) (e : LogEntry)
    (HB : BootLogFacts boot) (hk : l[p]? = some e) (ht : e.type = W32 2) :
    ⊢ isCluster (GF := GF) γ tcRaftN -∗ tcOpsInv γ boot -∗ isCommittedLogLb γ l -∗
      confAt γ p tcMem ={⊤}=∗ False := by
  iintro #Hc #Hops #Hl #Ha
  imod tcOps_emptyV2 γ boot l ⊤ HB (fun _ _ => CoPset.mem_full) $$ Hops Hl with %Hall
  have He2 : e.isEmptyV2 := Hall e (List.mem_of_getElem? hk) ht
  ihave %Hj := committed_emptyV2_joint γ tcRaftN l p e tcMem hk He2 $$ [Hc Hl Ha]
  · iframe Hc Hl Ha
  exact absurd rfl Hj

end lemmas

section receipt
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [MemStorReg GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

attribute [local instance] memStorageModel

/-- **`Advance`'s receipt after `Append`**, nothing frozen. -/
theorem tc_advReceipt (ms : Loc) (γs : MemStorNames) (es : List EntryM) (k n : Nat)
    (Hk : ∀ e0, es.head? = some e0 → k = uint.nat e0.Index') :
    ⊢ memStorReg (GF := GF) ms γs -∗
      (if es = [] then emp else memLog γs k (DFrac.own 1) es ∗ memEnd γs (k + es.length)) -∗
      advReceipt (memStorIface ms) n es none := by
  iintro #Hreg Hb
  unfold advReceipt
  iexists []
  isplitl
  · unfold appendReceipt
    by_cases he : es = []
    · ileft; ipureintro; exact he
    · iright
      simp only [he, ↓reduceIte]
      icases Hb with ⟨Hl, He⟩
      obtain ⟨e0, he0⟩ : ∃ e0, es.head? = some e0 := by
        cases es with
        | nil => exact absurd rfl he
        | cons x xs => exact ⟨x, rfl⟩
      iexists e0, es
      isplitr
      · ipureintro; exact ⟨he0, rfl⟩
      rw [← Hk e0 he0]
      isplitr
      · iapply memStorLog_of ms γs k DFrac.discard [] $$ Hreg
        iapply memLog_nil
      isplitl [Hl]
      · iapply memStorLog_of ms γs (k + ([] : List EntryM).length) (DFrac.own 1) es $$ Hreg
        simp only [List.length_nil, Nat.add_zero]
        iexact Hl
      iapply memStorEnd_of ms γs _ $$ Hreg He
  · ipureintro; intro h; exact absurd rfl h

end receipt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [MemStorReg GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]

attribute [local instance] memStorageModel

theorem Cluster.handleReady.wp_proof
    (wp_IsEmptySnap : IsEmptySnap.spec (GF := GF) (hG := hG))
    (wp_IsEmptyHardState : IsEmptyHardState.spec (GF := GF) (hG := hG))
    (wp_Append : MemoryStorage.Append.spec (GF := GF) (hG := hG))
    (wp_SetHardState : MemoryStorage.SetHardState.spec (GF := GF) (hG := hG))
    (wp_ACC : node.ApplyConfChange.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Entry.GetType.spec (GF := GF) (hG := hG))
    (wp_GetData : raftpb.Entry.GetData.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (wp_Unmarshal1 : proto.UnmarshalConfChange.spec (GF := GF) (hG := hG)) :
    Cluster.handleReady.spec (GF := GF) (hG := hG) := by
  intro c W r n ms γs id rd D ce es h hs0 v Hview Hes
  wp_start as ⟨#Hw, #Hri, Hown, Hmeta, #Hce, #Hcl, #Hdl, #Hes, #Hhs, %Hnull, Happ, Hcfg, Hrun⟩
  ihave #Hw' := Hw
  iunfold tcWorld at Hw'
  icases Hw' with ⟨#HcTick, #HcMax, #HcDrop, #HcSnap, %Hpure, #Hstop, #Hsc, #Hrs, #Hnodes, #Hnj, #Hiso, #HcP, #HcD, #HcX, #HcR,
    #HcC, #Hclu, #Hops, #Hpol, #Hsn, #Hboot⟩
  ihave #Hri' := Hri
  iunfold repInfo at Hri'
  icases Hri' with ⟨#Hid, #Hnf, #Hsf, #Hnode, #Hreg, #Hlock⟩
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  try wp_auto
  wp_apply ctr_wp_Add _ _ $$ [$HcR] as %_ -
  try wp_auto
  wp_apply wp_IsEmptySnap rd.Snapshot' DFrac.discard none $$ [$Hraft] as %b2 ⟨%Hb2, -⟩
  · unfold snapOpt; ipureintro; exact Hnull
  subst Hb2
  simp only [Option.elim]
  try wp_auto
  -- `r.storage.Append(rd.Entries)`
  ihave Hrange : iprop(∃ (k : Nat) (old : List EntryM),
      ⌜(∀ e0, es.head? = some e0 → k = uint.nat e0.Index') ∧ (es = [] → k = 0)⌝ ∗
      (if es = [] then emp else memLog γs k (DFrac.own 1) old ∗ memEnd γs (k + old.length)))
    $$ [Happ]
  · iunfold appendRight at Happ
    icases Happ with (%He | ⟨%e0, %old, %Hh, Hl, He⟩)
    · subst He
      iexists 0, []
      simp only [ite_true]
      isplitr
      · ipureintro; simp
      itrivial
    · iexists uint.nat e0.Index', old
      have hne : es ≠ [] := by intro h; subst h; cases Hh
      simp only [hne, ↓reduceIte]
      isplitr
      · ipureintro; exact ⟨fun e h => by rw [Hh] at h; cases h; rfl, fun h => h.elim⟩
      ihave Hl := memStorLog_to ms γs _ _ _ $$ Hreg Hl
      ihave He := memStorEnd_to ms γs _ $$ Hreg He
      iframe Hl He
  icases Hrange with ⟨%k, %old, ⟨%Hk, %Hk0⟩, Hrange⟩
  have h1 : ∀ (j : Nat) (e : EntryM), es[j]? = some e → uint.nat e.Index' = k + j := by
    intro j e hj
    cases hes : es with
    | nil => rw [hes] at hj; cases hj
    | cons e0 rest =>
      rw [Hk e0 (by rw [hes]; rfl)]
      exact (Hes e0 (by rw [hes]; rfl)).1 j e hj
  have h2 : k + es.length ≤ 2 ^ 61 := by
    cases hes : es with
    | nil => rw [Hk0 hes]; simp
    | cons e0 rest =>
      have := (Hes e0 (by rw [hes]; rfl)).2
      rw [Hk e0 (by rw [hes]; rfl)]
      rw [hes] at this
      exact this
  wp_apply wp_Append ms γs k old es rd.Entries' DFrac.discard h1 h2
    $$ [$Hraft $Hlock $Hrange $Hes] as ⟨-, Hb⟩
  try wp_auto
  -- the hard state
  wp_join iprop(∃ hs1 : HardStateM, memStorMeta ms γs hs1 ∗ r_ptr ↦ r ∗ rd_ptr ↦ rd)
    with [Hmeta r rd] as ⟨%hs1, Hmeta, r, rd⟩
  · try wp_auto
    wp_apply wp_IsEmptyHardState rd.HardState' h $$ [$Hraft $Hhs]
    try wp_auto
    wp_if_destruct
    · try wp_auto
      wp_join_done
    · try wp_auto
      wp_apply wp_SetHardState ms γs hs0 rd.HardState' h $$ [$Hraft $Hmeta $Hhs] as Hmeta
      try wp_auto
      wp_join_done
  · try wp_auto
    -- the apply loop
    iunfold repOwn at Hown
    icases Hown with ⟨%a0, %si0, %cs0, Happl, Hsi, Hcs⟩
    iunfold committedEntriesAt at Hce
    icases entsPts_elim _ _ _ $$ Hce with ⟨%cls, #Hcel, #Hceb⟩
    ihave %Hcelen := ownSlice_len $$ Hcel
    ihave %Hcebl := entsBig_length $$ Hceb
    rw [tc_toEntries_length] at Hcebl
    ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
    · iPkgInit
    ihave #Hproto : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
    · iPkgInit
    have Hv0 := viewAt_start D ce v Hview
    ihave IH : iprop(∃ (j : w64) (ev : Loc) (a : w64) (cs : Loc) (cf : Bool) (v' : ConfigView),
        "i" ∷ i_ptr ↦ j ∗ "e" ∷ e_ptr ↦ ev ∗ "r" ∷ r_ptr ↦ r ∗ "confApplied" ∷ confApplied_ptr ↦ cf ∗
        "Happl" ∷ r.[github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.creplica, go!"applied"]
          ↦ a ∗
        "Hcs" ∷ r.[github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.creplica,
          go!"confState"] ↦ cs ∗
        "Hcfg" ∷ nodeConfig n W.cl tcRaftN v' ∗ "Hrun" ∷ nodeRunning n W.cl tcRaftN 1 ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ (ce.length : Int) ∧
          ViewAt (D ++ ce) (D.length + sint.nat j) v'⌝)
      $$ [i e r confApplied Happl Hcs Hcfg Hrun]
    · iexists W64 0, _, a0, cs0, false, v
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [show sint.nat (W64 0) = 0 from rfl, Nat.add_zero]; exact Hv0
    wp_for IH
    wp_if_destruct
    · have Hlt : sint.nat j < ce.length := tc_run_lt j _ _ _ Hif Hcelen.1 Hcebl Hj.1
      obtain ⟨en, Hen⟩ : ∃ en, ce[sint.nat j]? = some en := ⟨_, List.getElem?_eq_getElem Hlt⟩
      have Hget := tc_toEntries_get ce D.length (sint.nat j) en Hen
      ihave ⟨%ln, %Hln, #Hent⟩ := entsBig_lookup cls _ (sint.nat j) _ Hget $$ Hceb
      simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z rd.CommittedEntries'.len from ⟨Hj.1, Hif⟩,
        _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index rd.CommittedEntries' (sint.Z j) _ DFrac.discard ln Hj.1
        $$ [Hcel] as -
      · iframe Hcel; ipureintro; rw [tc_toNat_sint j Hj.1]; exact Hln
      have Hpos : (D ++ ce)[D.length + sint.nat j]? = some en := by
        rw [List.getElem?_append_right (by omega)]; rw [show D.length + sint.nat j - D.length = sint.nat j by omega]; exact Hen
      obtain ⟨Hvm, Hva, Hvn⟩ := Hj.2.2
      icases nodeConfig_confAt n W.cl tcRaftN v' $$ Hcfg with ⟨Hcfg, #Hca⟩
      ihave #Hca' : confAt W.cl v'.applied tcMem $$ []
      · rw [← Hvm]; iexact Hca
      ihave #Hcap := confAt_noConf W.cl (D ++ ce) v'.applied (D.length + sint.nat j) tcMem Hvn Hva
        (by rw [List.length_append]; omega) $$ [Hcl Hca']
      · iframe Hcl Hca'
      try wp_auto
      wp_apply wp_GetType.1 ln DFrac.discard _ $$ [$Hpb $Hent] as -
      simp only [LogEntry.toEntryM]
      try wp_auto
      obtain ⟨Hs0, Hs1, Hs2⟩ := tc_run_succ j _ Hif Hj.1
      have Hj1 : sint.Z (j + W64 1) ≤ (ce.length : Int) := by
        rw [Hs1]; have : (sint.nat j : Int) < ce.length := by exact_mod_cast Hlt
        rw [show (sint.nat j : Int) = sint.Z j from Int.toNat_of_nonneg Hj.1] at this; omega
      have Hp1 : D.length + sint.nat (j + W64 1) = (D.length + sint.nat j) + 1 := by rw [Hs2]; rfl
      wp_if_destruct
      · -- a `ConfChange`: the bootstrap log's, applied
        have Ht1 : en.type = W32 1 := Hif
        imod tc_conf1 W.cl W.boot (D ++ ce) (D.length + sint.nat j) en Hpure.2.2.2.2.1 Hpos Ht1
          $$ Hclu Hops Hpol Hboot Hcl Hcap with ⟨%cm, ⟨%Hcm, %Hap⟩, #Hdec⟩
        try wp_auto
        wp_apply wp_GetData.1 ln DFrac.discard _ $$ [$Hpb $Hent] as %ds ⟨#Hds, -⟩
        wp_apply wp_Unmarshal1 ds _ DFrac.discard «$r0_ptr» _ $$ [$Hproto $Hds $«$r0»]
          as %er ⟨-, Hres⟩
        irevert Hres
        rw [Hcm]
        iintro Hres
        icases Hres with ⟨%Herr, Hccm⟩
        subst Herr
        imod ownConfChange_persist «$r0_ptr» (DFrac.own 1) cm $$ Hccm with #Hccm
        ihave Hci : ownConfChangeI (interface.mkOk (go.GoType.PointerType raftpb.ConfChange.ty)
            #«$r0_ptr») DFrac.discard (some (.v1 cm)) $$ []
        · simp only [ownConfChangeI]; iexists «$r0_ptr»; iframe Hccm; ipureintro; rfl
        have Hsk := skippedIn_noConf (GF := GF) W.cl (D ++ ce) v'.applied (D.length + sint.nat j) Hvn
        ihave #Hsk' := Hsk
        try wp_auto
        wp_apply wp_ACC n W.cl tcRaftN id _ (.v1 cm) (.v1 cm) (D ++ ce) (D.length + sint.nat j) en v'
            tcMem Hva Hpos (.inl Ht1) (by rw [Hvm]; exact Hap) (by rw [Hvm]; exact Hap)
            (fun _ => Hvm.symm)
          $$ [$Hraft $Hnode $Hclu $Hdec $Hci $Hcfg $Hdl $Hsk'] as %csp %csm Hres
        icases Hres with (⟨Hcsp, Hcfg, -⟩ | ⟨-, Hstop⟩)
        · try wp_auto
          wp_apply wp_GetIndex.1 ln DFrac.discard _ $$ [$Hpb $Hent] as -
          try wp_auto
          wp_for_post
          iframe
          iexists j + W64 1, ln, _, _, true, ⟨D.length + sint.nat j + 1, tcMem⟩
          iframe
          ipureintro
          refine ⟨Hs0, Hj1, ?_⟩
          rw [Hp1]; exact viewAt_applied (D ++ ce) (D.length + sint.nat j)
        · iexfalso
          iapply nodeRunning_stopped n W.cl tcRaftN 1
          iframe Hrun Hstop
      · have Hif0 := Hif
        wp_if_destruct
        · -- a `ConfChangeV2`: refuted
          imod tc_noConf2 W.cl W.boot (D ++ ce) (D.length + sint.nat j) en Hpure.2.2.2.2.1 Hpos Hif
            $$ Hclu Hops Hcl Hcap with %F
          exact F.elim
        · -- another entry: no conf change
          have Hnc : ¬ en.isConfChange := fun h => h.elim Hif0 Hif
          have Hv1 := viewAt_noConf (D ++ ce) (D.length + sint.nat j) en v' ⟨Hvm, Hva, Hvn⟩ Hpos Hnc
          try wp_auto
          wp_apply wp_GetIndex.1 ln DFrac.discard _ $$ [$Hpb $Hent] as -
          try wp_auto
          wp_for_post
          iframe
          iexists j + W64 1, ln, _, _, cf, v'
          iframe
          ipureintro
          refine ⟨Hs0, Hj1, ?_⟩
          rw [Hp1]; exact Hv1
    · -- the loop's end: no snapshot (`SnapshotEvery = 0`)
      have Hfull : sint.nat j = ce.length := tc_run_eq j _ _ _ Hif Hcelen.1 Hcebl Hj.2.1
      have HS : W.cfg.SnapshotEvery' = W64 0 := Hpure.1.2.2.2.1
      try wp_auto
      rw [HS]
      try wp_auto
      iapply HΦ
      isplitl [Happl Hsi Hcs]
      · iunfold repOwn
        iexists _, _, _
        iframe
      iexists hs1, v'
      iframe Hmeta Hcfg Hrun
      isplitl [Hb]
      · iapply tc_advReceipt ms γs es k _ Hk $$ Hreg Hb
      ipureintro
      apply viewAt_end
      rw [List.length_append, ← Hfull]
      exact Hj.2.2

end proof

end TraceCheck
end EtcdGrove
end Perennial
