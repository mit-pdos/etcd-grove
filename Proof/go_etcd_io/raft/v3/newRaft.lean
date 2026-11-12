/-
Port of election_proof/proof_newRaft.v.

raft v3.7 (stage R4, 2026-10-16): ported from the old tree's proof. `Storage.InitialState` returns
the hard state `hsOpt hp hs` and the conf state read-only, its `AutoLeave` set or not (2026-10-16, stage R6b: `csPts cs □ csm al`, weakened at once; until then `csPts cs □
csm true`, D7) beside the storage; `confchange.Restore` and `assertConfStatesEquivalent` read the
conf state at `□`; `IsEmptyHardState` reads `hsOpt`, and `loadState`, reached only for a non-empty
hard state, its `hsRO` (a `nil` pointer holds the empty one).
-/
module

public import Spec.go_etcd_io.raft.v3.newRaft
public import Spec.go_etcd_io.raft.v3.Config__validate
public import Spec.go_etcd_io.raft.v3.newLogWithSize
public import Spec.go_etcd_io.raft.v3.tracker.MakeProgressTracker
public import Spec.go_etcd_io.raft.v3.newReadOnly
public import Spec.go_etcd_io.raft.v3.traceInitState
public import Spec.go_etcd_io.raft.v3.confchange.Restore
public import Spec.go_etcd_io.raft.v3.assertConfStatesEquivalent
public import Spec.go_etcd_io.raft.v3.IsEmptyHardState
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetCommit
public import Proof.go_etcd_io.raft.v3.LemmasSnapCfg
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetVote
public import Spec.go_etcd_io.raft.v3.traceConfChangeEvent
public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__ConfState
public import Spec.go_etcd_io.raft.v3.raft__becomeFollower
public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__VoterNodes
public import Spec.fmt.Sprintf
public import Spec.strings.Join
public import Proof.go_etcd_io.raft.v3.TracedUntraced
public import Spec.go_etcd_io.raft.v3.raftLog__lastEntryID
public import Proof.go_etcd_io.raft.v3.TracedNodeBoot
public import Proof.go_etcd_io.raft.v3.TracedHooks
public import Proof.go_etcd_io.raft.v3.RaftReadLend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A set's domain (`domSet`) of the empty map. -/
theorem domSet_empty_loc : domSet (∅ : GMap w64 Loc) = ∅ := by
  apply GMap.map_eq; intro k; rfl

/-- `confchange.Restore` on the empty tracker `MakeProgressTracker` built, for a voters-only
conf state -- possibly with **no** voter (2026-10-16, stage R8b: a new cluster's, before
`RawNode.Bootstrap` installs the peers): the configuration `switchToConfig` takes (`ownConfig` at
the voters): fresh maps when there is a voter (the general `spec`), the tracker's own `v0` and
(read-only) progress map when there is none (`spec_empty`: no op runs). -/
theorem wp_Restore_voters (H : confchange.Restore.spec (GF := GF) (hG := hG))
    (chg : confchange.Changer) (cs : Loc) (c : ConfStateM) (dq : DFrac) (v0 : Loc)
    (Hvnd : c.Voters'.Nodup) (Hv0n : W64 0 ∉ c.Voters') (Hvlen : (c.Voters'.length : Int) ≤ 2 ^ 62)
    (Hcvo : c.VotersOutgoing' = []) (Hcl : c.Learners' = []) (Hcln : c.LearnersNext' = [])
    (Hmi : 0 ≤ sint.Z chg.Tracker'.MaxInflight' ∧ sint.Z chg.Tracker'.MaxInflight' < 2 ^ 62)
    (Harr : chg.Tracker'.Config'.Voters'.arr = [v0, map.nil])
    (Hl : chg.Tracker'.Config'.Learners' = map.nil)
    (Hln : chg.Tracker'.Config'.LearnersNext' = map.nil)
    (Hal : chg.Tracker'.Config'.AutoLeave' = false) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗
        ownCSM cs dq c ∗ v0 ↦$ (∅ : GMap w64 Unit) ∗
        chg.Tracker'.Progress' ↦$□ (∅ : GMap w64 Loc) }}
      (App (App (Val #(functions confchange.Restore [])) (Val #chg)) (Val #cs))
    {{ (cfgv : tracker.Config) (prsm : Loc), RET (PairV (PairV #cfgv #prsm) #interface.nil);
        |==> (ownCSM cs dq c ∗
          ∃ prs : GMap w64 Loc, ownConfig (GMap.listToSet c.Voters') cfgv prsm prs ∗
            ⌜domSet prs = GMap.listToSet c.Voters'⌝) }} := by
  iintro %Φ ⟨#Hpkg, Hcs, Hv0, #Hpm⟩ HΦ
  have Hcsz : (GMap.size (GMap.listToSet c.Voters') : Int) ≤ 2 ^ 62 := by
    rw [GMap.size_list_to_set _ Hvnd]; exact Hvlen
  by_cases Hvne : c.Voters' = []
  · -- no voter: no op, the tracker's own maps
    wp_apply (confchange.Restore.spec_empty H) chg cs c dq v0 Hvne Hcvo Hcl Hcln Hmi Harr Hl Hln Hal
      $$ [$Hcs $Hv0 $Hpm] as %cfgv %prsm ⟨%Hcp, Hcs, Hv0, -⟩
    obtain ⟨Hcfgv, Hprsm⟩ := Hcp
    subst Hcfgv Hprsm
    iapply HΦ
    imodintro
    iframe Hcs
    iexists ∅
    have Hv0' : GMap.listToSet c.Voters' = ∅ := by rw [Hvne]; rfl
    rw [Hv0']
    isplitl [Hv0]
    · iapply ownConfig_restore ∅ ∅ chg.Tracker'.Config' chg.Tracker'.Progress' ∅ v0 ∅ Harr Hln Hal
        (domSet_gset _) (by rw [GMap.map_union_empty]; exact domSet_empty_loc)
        (fun k hk => absurd hk (GMap.not_elem_of_empty _))
        (by rw [GMap.map_union_empty, GMap.size_empty]; decide)
        $$ Hv0 [] Hpm []
      · rw [Hl]; iapply ownIdsetC_nil
      · iapply BigSepM.bigSepM_empty.2; iempintro
    · ipureintro; exact domSet_empty_loc
  · -- a voter: fresh maps; with no outgoing voter and no learner the model's answer is the
    -- voters (`simpleFold_restoreIn`)
    have Hm : restoreM c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext' c.AutoLeave' =
        some (cfgState (GMap.listToSet c.Voters') (GMap.listToSet c.Learners')) := by
      rw [Hcvo, Hcln]
      unfold restoreM restoreSimpleOps
      simp only [↓reduceIte]
      exact simpleFold_restoreIn c.Voters' c.Learners' Hvne
        (fun x hx => hx.elim (fun h e => Hv0n (e ▸ h)) (fun h _ => by rw [Hcl] at h; cases h))
        (fun x hx => by rw [Hcl] at hx; cases hx)
    wp_apply H chg cs c dq v0 _ Hm Hmi Harr Hl Hln Hal $$ [$Hcs $Hv0 $Hpm]
      as %cfgv %prsm %prs ⟨Hcs, -, -, (⟨%Hops, -⟩ | ⟨-, Hc, Hprsm, %Hdom, Hprogs⟩)⟩
    · exfalso; exact restoreSimpleOps_ne_nil_of_voters _ _ _ _ Hvne Hops
    icases ownCfgCC_elim _ _ _ $$ Hc with ⟨%vref, %vout, %Harr1, Hvref, Hout, Hlm, Hln1, %Hal1⟩
    icases ownIdsetC_nil_of _ _ (cfgState _ _).cfg.outgoing rfl $$ Hout with %Hvout
    icases ownIdsetC_nil_of _ _ (cfgState _ _).cfg.learnersNext rfl $$ Hln1 with %Hcfgln
    have Hcfgarr : cfgv.Voters'.arr = [vref, map.nil] := by rw [Harr1, Hvout]
    have Hcfgal := Hal1
    ihave Hlm := (show ownIdsetC (GF := GF) cfgv.Learners' (DFrac.own 1)
      (cfgState (GMap.listToSet c.Voters') (GMap.listToSet c.Learners')).cfg.learners ⊢
      ownIdsetC cfgv.Learners' (DFrac.own 1) (GMap.listToSet c.Learners') from .rfl) $$ Hlm
    ihave Hvref := (show (vref ↦$ (cfgState (GMap.listToSet c.Voters')
      (GMap.listToSet c.Learners')).cfg.incoming : IProp GF) ⊢
      vref ↦$ GMap.listToSet c.Voters' from .rfl) $$ Hvref
    have Hvm := domSet_gset (GMap.listToSet c.Voters')
    have Hprs : domSet prs = GMap.listToSet c.Voters' ∪ GMap.listToSet c.Learners' := by
      rw [Hdom]
      apply GMap.set_eq; intro k
      rw [GMap.elem_of_dom', cfgState, cfgFlags_mem, GMap.elem_of_union]
    have Hprs' : domSet prs = GMap.listToSet c.Voters' := by
      rw [Hprs, Hcl]; exact GMap.map_union_empty _
    ihave Hprogs : [∗map] k ↦ pr ∈ prs, ∃ p, ownProgress pr p ∗
        ⌜p.learner = !decide (k ∈ GMap.listToSet c.Voters')⌝ $$ [Hprogs]
    · iapply BigSepM.bigSepM_mono ?_ $$ Hprogs
      intro k pr _
      iintro ⟨%p, Hp, %Hpl⟩
      iexists p
      iframe Hp
      ipureintro
      simp only [cfgState] at Hpl
      rw [cfgFlags_lookup] at Hpl
      by_cases hv : k ∈ GMap.listToSet c.Voters'
      · rw [ite_eq_left hv] at Hpl; rw [← Option.some.inj Hpl]; simp [hv]
      · rw [ite_eq_right hv] at Hpl
        by_cases hl : k ∈ GMap.listToSet c.Learners'
        · rw [ite_eq_left hl] at Hpl; rw [← Option.some.inj Hpl]; simp [hv]
        · rw [ite_eq_right hl] at Hpl; cases Hpl
    iapply HΦ
    ipersist Hprsm
    imodintro
    iframe Hcs
    iexists prs
    isplitl [Hvref Hlm Hprogs]
    · iapply ownConfig_restore (GMap.listToSet c.Voters') (GMap.listToSet c.Learners') cfgv prsm prs
        vref _ Hcfgarr Hcfgln Hcfgal Hvm Hprs
        (fun k hk => by rw [Hcl] at hk; exact absurd hk (GMap.not_elem_of_empty _))
        (by rw [Hcl, show GMap.listToSet ([] : List w64) = ∅ from rfl, GMap.map_union_empty]; exact Hcsz)
        $$ Hvref Hlm Hprsm Hprogs
    · ipureintro; exact Hprs'

/-! ### The window (2026-11-02, stage II (r))

From `InitialState` to `appliedTo` no `ownRaftLog` holds: raft's view has caught up with the attach
record (`storCaught`: its floor at the record's applied bound `max b A`, its certified terms up to the
restored commit), while the struct is still at the base (`committed = applied = applying = b`), so
`FlOk`'s `fl ≤ applying` and `DtOk`'s `≤ committed` fail. The log is the raw struct
(`newLogWithSize`'s `l ↦ lv0`) beside the caught-up view; the window's reads (`lastIndex`,
`lastEntryID`) and writes (`loadState`, `appliedTo`) are proved here on that, over their bodies, and
`newLogWithSize`'s wand seals `ownRaftLog` once `appliedTo` is done. -/

omit [GooseInterp] [GooseSemantics] [GoGlobalContext] [StorageModel GF] in
/-- The map of an attach record's (index, term) pairs (the first pair of an index wins). -/
private def ctMap (ct : List (Nat × w64)) : GMap Nat w64 :=
  ct.foldr (fun p m => <[p.1 := p.2]> m) ∅

omit [GooseInterp] [GooseSemantics] [GoGlobalContext] [StorageModel GF] in
private theorem ctMap_mem {ct : List (Nat × w64)} {i : Nat} {t : w64}
    (h : ctMap ct !! i = some t) : (i, t) ∈ ct := by
  induction ct with
  | nil => simp [ctMap] at h
  | cons p ps ih =>
    change (<[p.1 := p.2]> (ctMap ps)) !! i = some t at h
    by_cases hi : p.1 = i
    · subst hi
      rw [GMap.lookup_insert_eq] at h
      cases h
      exact List.mem_cons_self
    · rw [GMap.lookup_insert_ne _ _ hi] at h
      exact List.mem_cons_of_mem _ (ih h)

omit [GooseInterp] [GooseSemantics] [GoGlobalContext] [StorageModel GF] in
private theorem ctMap_lookup {ct : List (Nat × w64)} {i : Nat} {t : w64} (h : (i, t) ∈ ct)
    (hu : ∀ t', (i, t') ∈ ct → t' = t) : ctMap ct !! i = some t := by
  induction ct with
  | nil => cases h
  | cons p ps ih =>
    change (<[p.1 := p.2]> (ctMap ps)) !! i = some t
    by_cases hi : p.1 = i
    · subst hi
      rw [GMap.lookup_insert_eq, hu p.2 List.mem_cons_self]
    · rw [GMap.lookup_insert_ne _ _ hi]
      have h' : (i, t) ∈ ps := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd (congrArg Prod.fst h).symm hi
        · exact h
      exact ih h' (fun t' ht' => hu t' (List.mem_cons_of_mem _ ht'))

/-- **The catch-up with the attach record**, at the attach: the floor raised to the record's applied
bound, the record's terms up to its commit certified (from nothing certified), so raft's view is at
the names with the record (`storCaught`). -/
private theorem ownStorage_catchUp (sn : StorNames) (st : Storage) (σ : StorState)
    (M : GMap Nat w64) (Hfl : uint.nat σ.fl ≤ sn.a0) (Ha0 : (sn.a0 : Int) < 2 ^ 64)
    (Hdt : σ.dt = ∅) (HM : ∀ i t, i ≤ sn.c0 ∧ (i, t) ∈ sn.ct → M !! i = some t) :
    ownStorage (GF := GF) sn.unrec st σ ⊢
      |==> ownStorage sn st { σ with fl := W64 (sn.a0 : Int), dt := M } := by
  unfold ownStorage storAuths
  simp only [StorNames.unrec]
  have Hk : ({ σ with fl := W64 (sn.a0 : Int), dt := M } : StorState).kOut = σ.kOut := rfl
  rw [Hk]
  iintro ⟨%e0, #Hcomp, #HFr, HO, Hend, ⟨Ha, Hg, Hd, -⟩, %Hw⟩
  have Hfl' : uint.nat (W64 (sn.a0 : Int)) = sn.a0 := by
    have := uint_Z_W64 (sn.a0 : Int) (by omega) Ha0; have := uint_nat_eq (W64 (sn.a0 : Int)); omega
  imod mono_nat_own_update (GF := GF) (γ := sn.ga) (uint.nat (W64 (sn.a0 : Int))) (by omega) $$ Ha
    with ⟨Ha, #Hlb⟩
  ihave Hd : ghostMapAuth (GF := GF) sn.gd 1 (∅ : GMap Nat w64) $$ [Hd]
  · rw [← Hdt]; iexact Hd
  imod ghost_map_insert_persist_big M (GMap.map_disjoint_empty_r M) $$ Hd with ⟨Hd, #Hfr⟩
  imodintro
  iexists e0
  iframe Hcomp HFr HO Hend Ha Hg
  isplitl [Hd]
  · isplitl [Hd]
    · iExactEq Hd; rw [GMap.map_union_empty]
    unfold storCaught
    isplitr
    · iExactEq Hlb; rw [Hfl']
    iintro !> %i %t %H
    iapply BigSepM.bigSepM_lookup (Φ := fun k v => (k ↪[sn.gd]□ v : IProp GF)) (HM i t H) $$ Hfr
  ipureintro; exact Hw

/-- `raftLog.lastIndex` in the window: nothing unstable, so the storage's `LastIndex`. -/
private theorem wp_lastIndex_w (l : Loc) (lv : raftLog) (si : GoInterfaceOk) (sn : StorNames)
    (σ : StorState) (Hst : lv.storage' = interface.ok si) (Hsn : lv.unstable'.snapshot' = null)
    (Hen : lv.unstable'.entries'.len = W64 0) (Hpend : σ.pend = []) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ l ↦ lv ∗
        isStorageD sn (interface.ok si) ∗ ownStorage sn (interface.ok si) σ }}
      (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"lastIndex")) (Val #()))
    {{ (li : w64), RET #li; l ↦ lv ∗ ownStorage sn (interface.ok si) σ ∗
        ⌜uint.Z li = uint.Z σ.prev.index' + (σ.ents.length : Int)⌝ }} := by
  wp_start as ⟨Hl, #HisSto, HSto⟩
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  rw [Hen]
  wp_auto
  rw [Hsn]
  wp_auto
  ihave #Hsto : isStorageWith (ownStorage sn (interface.ok si)) (storCut (interface.ok si))
    (svCert sn) (interface.ok si) $$ [HisSto]
  · unfold isStorageD; iexact HisSto
  unfold isStorageWith
  icases Hsto with ⟨%isv, #Hsto⟩
  iNamed Hsto
  rw [Hst]
  wp_auto
  cases Hstok
  wp_apply HLastIndex $$ [$HSto] as %li ⟨%Hli, HSto⟩
  · ipureintro; exact Hpend
  iapply HΦ
  iframe Hl HSto
  ipureintro; exact Hli

/-- `raftLog.firstIndex` in the window: no snapshot pending, so the storage's `FirstIndex`. -/
private theorem wp_firstIndex_w (l : Loc) (lv : raftLog) (si : GoInterfaceOk) (sn : StorNames)
    (σ : StorState) (Hst : lv.storage' = interface.ok si) (Hsn : lv.unstable'.snapshot' = null) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ l ↦ lv ∗
        isStorageD sn (interface.ok si) ∗ ownStorage sn (interface.ok si) σ }}
      (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"firstIndex")) (Val #()))
    {{ (fi : w64), RET #fi; l ↦ lv ∗ ownStorage sn (interface.ok si) σ ∗
        ⌜uint.Z σ.prev.index' + 1 ≤ uint.Z fi ∧
          uint.Z fi ≤ max (uint.Z σ.prev.index') (uint.Z σ.fl) + 1⌝ }} := by
  wp_start as ⟨Hl, #HisSto, HSto⟩
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  rw [Hsn]
  wp_auto
  ihave #Hsto : isStorageWith (ownStorage sn (interface.ok si)) (storCut (interface.ok si))
    (svCert sn) (interface.ok si) $$ [HisSto]
  · unfold isStorageD; iexact HisSto
  unfold isStorageWith
  icases Hsto with ⟨%isv, #Hsto⟩
  iNamed Hsto
  rw [Hst]
  wp_auto
  cases Hstok
  wp_apply HFirstIndex $$ [$HSto] as %fi ⟨%Hfi, -, HSto⟩
  iapply HΦ
  iframe Hl HSto
  ipureintro; exact Hfi

/-- `raftLog.lastEntryID` in the window: the storage's last index, and its term there, which the
storage holds (the client compacts at most to the floor, at most the last index). -/
private theorem wp_lastEntryID_w (l : Loc) (lv : raftLog) (si : GoInterfaceOk) (sn : StorNames)
    (σ : StorState) (Hst : lv.storage' = interface.ok si) (Hsn : lv.unstable'.snapshot' = null)
    (Hen : lv.unstable'.entries'.len = W64 0) (Hpend : σ.pend = [])
    (Hoff : uint.Z lv.unstable'.offset' = uint.Z σ.prev.index' + (σ.ents.length : Int) + 1)
    (Hfl : uint.Z σ.fl ≤ uint.Z σ.prev.index' + (σ.ents.length : Int))
    (Hnw : uint.Z σ.prev.index' + (σ.ents.length : Int) + 1 < 2 ^ 64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ l ↦ lv ∗
        isStorageD sn (interface.ok si) ∗ ownStorage sn (interface.ok si) σ }}
      (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"lastEntryID")) (Val #()))
    {{ (e : entryID), RET #e; l ↦ lv ∗ ownStorage sn (interface.ok si) σ }} := by
  wp_start as ⟨Hl, #HisSto, HSto⟩
  ihave #Hinit := isInitialized_access $$ Hpkg
  iNamed Hinit
  wp_auto
  wp_apply wp_lastIndex_w l lv si sn σ Hst Hsn Hen Hpend $$ [$Hl $HisSto $HSto]
    as %li ⟨Hl, HSto, %Hli⟩
  wp_method_call
  wp_call
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  rw [decide_eq_true (show uint.Z li < uint.Z lv.unstable'.offset' by omega)]
  wp_auto
  rw [Hsn]
  wp_auto
  ihave #Hsto : isStorageWith (ownStorage sn (interface.ok si)) (storCut (interface.ok si))
    (svCert sn) (interface.ok si) $$ [HisSto]
  · unfold isStorageD; iexact HisSto
  unfold isStorageWith
  icases Hsto with ⟨%isv, #Hsto⟩
  iNamed Hsto
  cases Hstok
  wp_apply wp_firstIndex_w l lv si sn σ Hst Hsn $$ [$Hl $HisSto $HSto] as %fi ⟨Hl, HSto, %Hfi⟩
  rw [decide_eq_false (show ¬ uint.Z (li + W64 1) < uint.Z fi by
    have : uint.Z (li + W64 1) = uint.Z li + 1 := by word
    omega)]
  wp_auto
  wp_apply wp_lastIndex_w l lv si sn σ Hst Hsn Hen Hpend $$ [$Hl $HisSto $HSto]
    as %li2 ⟨Hl, HSto, %Hli2⟩
  rw [decide_eq_false (show ¬ uint.Z li2 < uint.Z li by omega)]
  wp_auto
  rw [Hst]
  wp_auto
  wp_apply HTerm $$ %σ %li %errCompacted [$HSto] as %t %err ⟨Ht, HSto⟩
  · isplitr
    · ipureintro; omega
    isplitr
    · ipureintro; intro e0 He0; rw [Hpend] at He0; cases He0
    iexact ErrCompacted
  icases Ht with (%Ht | ⟨%Ht, -⟩)
  · obtain ⟨rfl, -⟩ := Ht
    wp_auto
    iapply HΦ
    iframe Hl HSto
  · exfalso; omega

/-- `raftLog.appliedTo(i, 0)` in the window, from `applying ≤ i` with nothing applying: `applied`
and `applying` move to `i`, the rest as it was. -/
private theorem wp_appliedTo_w (l : Loc) (lv : raftLog) (i : w64)
    (Hi : uint.Z lv.applied' ≤ uint.Z i ∧ uint.Z i ≤ uint.Z lv.committed')
    (Hapg : uint.Z lv.applying' ≤ uint.Z i) (Hasz : lv.applyingEntsSize' = W64 0)
    (Hamx : 0 < uint.Z lv.maxApplyingEntsSize') (Hpz : lv.applyingEntsPaused' = false) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ l ↦ lv }}
      (App (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"appliedTo")) (Val #i))
        (Val #(W64 0)))
    {{ RET #(); l ↦ { lv with applied' := i, applying' := i } }} := by
  wp_start as Hl
  wp_auto
  rw [decide_eq_false (show ¬ (uint.Z lv.committed' < uint.Z i) by omega)]
  wp_auto
  rw [decide_eq_false (show ¬ (uint.Z i < uint.Z lv.applied') by omega)]
  wp_auto
  wp_func_call
  wp_call
  wp_if_destruct
  · exfalso; omega
  rw [Hasz, decide_eq_false (show ¬ uint.Z (W64 0) < uint.Z (W64 0) by decide)]
  wp_auto
  iapply HΦ
  iExactEq Hl
  rw [decide_eq_false (show ¬ uint.Z lv.maxApplyingEntsSize' ≤ uint.Z (W64 0) by
    have : uint.Z (W64 0) = 0 := rfl
    omega), ← Hpz]

/-- `raft.loadState(hs)` in the window, on the raft struct's fields it touches: the commit index
within `[committed, lastIndex]` (the storage's last index), so no `Panicf`. -/
private theorem wp_loadState_w
    (wp_HardState_GetCommit : raftpb.HardState.GetCommit.spec (GF := GF) (hG := hG))
    (wp_HardState_GetTerm : raftpb.HardState.GetTerm.spec (GF := GF) (hG := hG))
    (wp_HardState_GetVote : raftpb.HardState.GetVote.spec (GF := GF) (hG := hG))
    (r l : Loc) (lv : raftLog) (t0 v0 : w64) (si : GoInterfaceOk) (sn : StorNames)
    (σ : StorState) (hp : Loc) (hs : HardStateM) (Hst : lv.storage' = interface.ok si)
    (Hsn : lv.unstable'.snapshot' = null) (Hen : lv.unstable'.entries'.len = W64 0)
    (Hpend : σ.pend = [])
    (Hc : uint.Z lv.committed' ≤ uint.Z hs.Commit' ∧
      uint.Z hs.Commit' ≤ uint.Z σ.prev.index' + (σ.ents.length : Int)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"raftLog"] ↦ l ∗
        r.[raft, go!"Term"] ↦ t0 ∗ r.[raft, go!"Vote"] ↦ v0 ∗ l ↦ lv ∗
        isStorageD sn (interface.ok si) ∗ ownStorage sn (interface.ok si) σ ∗ hsRO hp hs }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"loadState")) (Val #hp))
    {{ RET #(); r.[raft, go!"raftLog"] ↦ l ∗ r.[raft, go!"Term"] ↦ hs.Term' ∗
        r.[raft, go!"Vote"] ↦ hs.Vote' ∗ l ↦ { lv with committed' := hs.Commit' } ∗
        ownStorage sn (interface.ok si) σ }} := by
  wp_start as ⟨HrL, HrT, HrV, Hl, #HisSto, HSto, #Hhs⟩
  try wp_auto
  wp_apply wp_HardState_GetCommit.1 hp hs $$ [$Hhs]
  try wp_auto
  rw [decide_eq_false (show ¬ uint.Z hs.Commit' < uint.Z lv.committed' by omega)]
  try wp_auto
  wp_apply wp_HardState_GetCommit.1 hp hs $$ [$Hhs]
  wp_apply wp_lastIndex_w l lv si sn σ Hst Hsn Hen Hpend $$ [$Hl $HisSto $HSto]
    as %li ⟨Hl, HSto, %Hli⟩
  rw [decide_eq_false (show ¬ uint.Z li < uint.Z hs.Commit' by omega)]
  try wp_auto
  wp_apply wp_HardState_GetCommit.1 hp hs $$ [$Hhs]
  try wp_auto
  wp_apply wp_HardState_GetTerm.1 hp hs $$ [$Hhs]
  try wp_auto
  wp_apply wp_HardState_GetVote.1 hp hs $$ [$Hhs]
  try wp_auto
  iapply HΦ
  iframe

/-- `raft.switchToConfig(cfg, trk)` in the window, at a follower, on the raft struct's fields it
touches: the configuration installed, the conf state of it returned (the follower's arm: no
`becomeFollower`, no broadcast). -/
private theorem wp_switchToConfig_w
    (wp_traceConfChangeEvent : traceConfChangeEvent.spec (GF := GF) (hG := hG))
    (wp_ProgressTracker_ConfState : tracker.ProgressTracker.ConfState.spec (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (lok : GoInterfaceOk) (b0 : Bool)
    (tv0 : tracker.ProgressTracker) (votes : GMap w64 Bool)
    (cfgv : tracker.Config) (prsm : Loc) (prs : GMap w64 Loc) (pvs : GMap w64 Progress)
    (Hmi : 0 ≤ sint.Z tv0.MaxInflight' ∧ sint.Z tv0.MaxInflight' < 2 ^ 62)
    (tl : GoInterface) (Htlk : TraceLoggerOk tl) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"trk"] ↦ tv0 ∗
        r.[raft, go!"traceLogger"] ↦□ tl ∗
        r.[raft, go!"id"] ↦□ id ∗ r.[raft, go!"logger"] ↦□ interface.ok lok ∗ isLogger lok ∗
        r.[raft, go!"isLearner"] ↦ b0 ∗ r.[raft, go!"state"] ↦ StateFollower ∗
        tv0.Votes' ↦$ votes ∗ ownConfigC c cfgv prsm prs pvs }}
      (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"switchToConfig"))
        (Val #cfgv)) (Val #prsm))
    {{ (cs : Loc) (xs os ls lns : List w64) (b : Bool), RET #cs;
        r.[raft, go!"trk"] ↦ { tv0 with Config' := cfgv, Progress' := prsm } ∗
        ownTrackerC c { tv0 with Config' := cfgv, Progress' := prsm } ⟨votes, prs, pvs⟩ ∗
        r.[raft, go!"isLearner"] ↦ b ∗ r.[raft, go!"state"] ↦ StateFollower ∗
        csPts cs (DFrac.own 1) (ConfStateM.mk xs ls os lns c.autoLeave) true ∗
        ⌜xs ≡ₚ elements c.incoming ∧ os ≡ₚ elements c.outgoing ∧ ls ≡ₚ elements c.learners ∧
          lns ≡ₚ elements c.learnersNext⌝ }} := by
  have wp_traceConfChangeEvent := traceConfChangeEvent.untraced wp_traceConfChangeEvent
  wp_start as ⟨Htrkf, #Htl, #Hid, #Hlgf, #Hlg, HiL, Hst, Hvotes, Hnew⟩
  wp_auto
  wp_apply wp_traceConfChangeEvent $$ [Htl]
  · isplitr
    · iexact Htl
    ipureintro; exact Htlk
  try wp_auto
  -- the log line
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  try iintro %_ ⟨_, -⟩
  try wp_auto
  wp_apply Logger.wp_logf lok _ _ _ (by decide) $$ Hlg
  try wp_auto
  -- `cs := r.trk.ConfState()`
  ihave Htrk := ownTrackerC_reconfig c tv0 votes cfgv prsm prs pvs Hmi $$ Hvotes Hnew
  wp_apply wp_ProgressTracker_ConfState c _ _ _ $$ [$Htrkf $Htrk]
    as %cs %xs %os %ls %lns ⟨Htrkf, Htrk, Hcs, %Hcs0⟩
  -- `pr, ok := r.trk.Progress[r.id]`
  icases ownTrackerC_progress_map c _ _ $$ Htrk with ⟨#Hprs, %Hdom, Htrk⟩
  try wp_auto
  wp_apply wp_map_lookup2 $$ Hprs as -
  dsimp only
  cases Hlk : prs !! id with
  | none =>
    simp only [Option.getD_none, Option.isSome_none]
    try wp_auto
    iapply HΦ
    iframe Htrkf Htrk HiL Hst Hcs
    ipureintro; exact Hcs0
  | some pr =>
    simp only [Option.getD_some, Option.isSome_some]
    try wp_auto
    icases ownTrackerC_lookup_same c _ _ id pr Hlk $$ Htrk with ⟨%p, %Hpv, Hpr, Hprback⟩
    iNamed Hpr
    wp_auto
    ihave Htrk := Hprback $$ [Hpv Hinfl]
    · iapply ownProgress_intro $$ Hpv Hinfl
      ipureintro; exact Habs
    cases pv.IsLearner'
    all_goals
      wp_auto
      iapply HΦ
      iframe Htrkf Htrk HiL Hst Hcs
      ipureintro; exact Hcs0

/-- (2026-11-12, trace-check step 5) **Raft's state lent with the configuration it installs, when that is
the tracker's own** (`newRaft`'s `switchToConfig` after `Restore` of the empty conf state): the read view's
old configuration is the new one's maps. -/
private theorem raftReadLend_alias (c : CfgM) (r : Loc) (id : w64) (s : NState) (tv : tracker.ProgressTracker)
    (cfgv : tracker.Config) (prsm : Loc) (prs : GMap w64 Loc) (pvs : GMap w64 Progress)
    (h : tv.Config' = cfgv) :
    ⊢ RaftReadLend (GF := GF) iprop((ownRaftCore r id s ∗ r.[raft, go!"trk"] ↦ tv) ∗
      ownConfigC c cfgv prsm prs pvs) c r id s := by
  unfold RaftReadLend
  imodintro
  iintro ⟨⟨Hcore, Htrk⟩, Hnew⟩
  iunfold ownConfigC at Hnew
  iNamed Hnew
  have Hsz : CfgSizeOk c := by
    constructor
    · have := size_le_of_sub_dom c.incoming prs (by rw [Hdom]; exact incoming_sub_ids c)
      omega
    · have := size_le_of_sub_dom c.outgoing prs (by rw [Hdom]; exact outgoing_sub_ids c)
      omega
  subst h
  iexists tv
  isplitl [Hcore Htrk Hcfg]
  · unfold ownRaftReadT; iframe Hcore Htrk Hcfg; ipureintro; exact Hsz
  iintro Hrd
  unfold ownRaftReadT
  icases Hrd with ⟨Hcore, Htrk, Hcfg, -⟩
  iframe Hcore Htrk
  iunfold ownConfigC
  iframe Hcfg Hprsm Hprogs
  simp only [named]
  ipureintro; exact ⟨Hinv, Hdom, Hflags, Hsize⟩

/-- (2026-11-12, trace-check step 5) **The window's `switchToConfig`, traced**: as
`wp_switchToConfig_w`, at a traced fresh node whose new configuration is the tracker's own
(`Restore` of the empty conf state, `tv0.Config' = cfgv`): the hook's `ApplyConfChange` line fired, raft's
state lent read-only (its core, the `trk` field) with the configuration it installs, whose maps are the
old one's (`raftReadLend_alias`). -/
private theorem wp_switchToConfig_wT
    (wp_traceConfChangeEvent : traceConfChangeEvent.spec (GF := GF) (hG := hG))
    (wp_ProgressTracker_ConfState : tracker.ProgressTracker.ConfState.spec (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (lok : GoInterfaceOk) (b0 : Bool)
    (tv0 : tracker.ProgressTracker) (votes : GMap w64 Bool)
    (cfgv : tracker.Config) (prsm : Loc) (prs : GMap w64 Loc) (pvs : GMap w64 Progress)
    (Hmi : 0 ≤ sint.Z tv0.MaxInflight' ∧ sint.Z tv0.MaxInflight' < 2 ^ 62)
    (tl : GoInterface) (γd : GName) (Q : IProp GF) (Hcv : tv0.Config' = cfgv) (Hrole : s.role = .follower) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"trk"] ↦ tv0 ∗
        r.[raft, go!"traceLogger"] ↦□ tl ∗
        r.[raft, go!"logger"] ↦□ interface.ok lok ∗ isLogger lok ∗
        r.[raft, go!"isLearner"] ↦ b0 ∗ ownRaftCore r id s ∗
        tv0.Votes' ↦$ votes ∗ ownConfigC c cfgv prsm prs pvs ∗
        TraceFire (some γd) tl (CCEvOf id s c c) Q }}
      (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"switchToConfig"))
        (Val #cfgv)) (Val #prsm))
    {{ (cs : Loc) (xs os ls lns : List w64) (b : Bool), RET #cs;
        r.[raft, go!"trk"] ↦ { tv0 with Config' := cfgv, Progress' := prsm } ∗
        ownTrackerC c { tv0 with Config' := cfgv, Progress' := prsm } ⟨votes, prs, pvs⟩ ∗
        r.[raft, go!"isLearner"] ↦ b ∗ ownRaftCore r id s ∗
        csPts cs (DFrac.own 1) (ConfStateM.mk xs ls os lns c.autoLeave) true ∗
        ⌜xs ≡ₚ elements c.incoming ∧ os ≡ₚ elements c.outgoing ∧ ls ≡ₚ elements c.learners ∧
          lns ≡ₚ elements c.learnersNext⌝ ∗ Q }} := by
  wp_start as ⟨Htrkf, #Htl, #Hlgf, #Hlg, HiL, Hcore, Hvotes, Hnew, Hfire⟩
  wp_auto
  wp_apply wp_traceConfChangeEvent cfgv r tl (some γd) (CCEvOf id s c c) Q
      iprop((ownRaftCore r id s ∗ r.[raft, go!"trk"] ↦ tv0) ∗ ownConfigC c cfgv prsm prs pvs)
    $$ [Hcore Htrkf Hnew Hfire] as ⟨HR, HQ⟩
  · iframe Htl Hfire
    iapply (trOwn_some γd _).2
    iexists c, c, id, s, prsm, prs, pvs, iprop(ownRaftCore r id s ∗ r.[raft, go!"trk"] ↦ tv0)
    iframe Hcore Htrkf Hnew
    isplitr
    · iapply raftReadLend_alias c r id s tv0 cfgv prsm prs pvs Hcv
    isplitr
    · ipureintro; exact fun _ h => h
    iintro H; iexact H
  ihave HR := (trOwn_some γd _).1 $$ HR
  icases HR with ⟨⟨Hcore, Htrkf⟩, Hnew⟩
  iunfold ownRaftCore at Hcore
  icases Hcore with ⟨#Hid, HT, HV, Hst, HL, Hlog⟩
  ihave Hst : r.[raft, go!"state"] ↦ StateFollower $$ [Hst]
  · iExactEq Hst; rw [Hrole]; rfl
  try wp_auto
  -- the log line
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  try iintro %_ ⟨_, -⟩
  try wp_auto
  wp_apply Logger.wp_logf lok _ _ _ (by decide) $$ Hlg
  try wp_auto
  -- `cs := r.trk.ConfState()`
  ihave Htrk := ownTrackerC_reconfig c tv0 votes cfgv prsm prs pvs Hmi $$ Hvotes Hnew
  wp_apply wp_ProgressTracker_ConfState c _ _ _ $$ [$Htrkf $Htrk]
    as %cs %xs %os %ls %lns ⟨Htrkf, Htrk, Hcs, %Hcs0⟩
  -- `pr, ok := r.trk.Progress[r.id]`
  icases ownTrackerC_progress_map c _ _ $$ Htrk with ⟨#Hprs, %Hdom, Htrk⟩
  try wp_auto
  wp_apply wp_map_lookup2 $$ Hprs as -
  dsimp only
  cases Hlk : prs !! id with
  | none =>
    simp only [Option.getD_none, Option.isSome_none]
    try wp_auto
    iapply HΦ
    iframe Htrkf Htrk HiL Hcs HQ
    isplitl [HT HV Hst HL Hlog]
    · unfold ownRaftCore; iframe Hid HT HV HL Hlog; iExactEq Hst; rw [Hrole]; rfl
    ipureintro; exact Hcs0
  | some pr =>
    simp only [Option.getD_some, Option.isSome_some]
    try wp_auto
    icases ownTrackerC_lookup_same c _ _ id pr Hlk $$ Htrk with ⟨%p, %Hpv, Hpr, Hprback⟩
    iNamed Hpr
    wp_auto
    ihave Htrk := Hprback $$ [Hpv Hinfl]
    · iapply ownProgress_intro $$ Hpv Hinfl
      ipureintro; exact Habs
    cases pv.IsLearner'
    all_goals
      wp_auto
      iapply HΦ
      iframe Htrkf Htrk HiL Hcs HQ
      isplitl [HT HV Hst HL Hlog]
      · unfold ownRaftCore; iframe Hid HT HV HL Hlog; iExactEq Hst; rw [Hrole]; rfl
      ipureintro; exact Hcs0

omit [GooseInterp] [GooseSemantics] [GoGlobalContext] [StorageModel GF] in
/-- A well-formed conf state's configuration (`Restore`'s): its sets are the lists', `AutoLeave`
the conf state's; an empty one's the empty configuration. -/
private theorem confStateOk_cfg (c : ConfStateM) (cs' : CCState) (Hok : ConfStateOk c)
    (Hres : restoreM c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext' c.AutoLeave' =
      some cs') :
    cs' = cfgStateC (csCfgM c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext'
      c.AutoLeave') := by
  rcases Hok.1 with Hwf | ⟨h1, h2, h3, h4⟩
  · rw [restoreM_wf _ _ _ _ _ Hwf] at Hres
    exact (Option.some.inj Hres).symm
  · have Hal := Hok.2.2.2.2.2 h2
    rw [h1, h2, h3, h4, Hal] at Hres ⊢
    have : restoreM [] [] [] [] false = some (cfgState ∅ ∅) := rfl
    rw [this] at Hres
    rw [← Option.some.inj Hres, ← cfgStateC_simple]
    rfl

/-- The conf state `switchToConfig` reports of a well-formed conf state's configuration is it, up
to order: `assertConfStatesEquivalent`'s premises. -/
private theorem confStateOk_perm (c : ConfStateM) (cs' : CCState) (Hok : ConfStateOk c)
    (Hres : restoreM c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext' c.AutoLeave' =
      some cs') (xs os ls lns : List w64)
    (H : xs ≡ₚ elements cs'.cfg.incoming ∧ os ≡ₚ elements cs'.cfg.outgoing ∧
      ls ≡ₚ elements cs'.cfg.learners ∧ lns ≡ₚ elements cs'.cfg.learnersNext) :
    c.lists.Perm ⟨xs, ls, os, lns⟩ ∧ c.AutoLeave' = cs'.cfg.autoLeave := by
  rw [confStateOk_cfg c cs' Hok Hres] at H ⊢
  obtain ⟨-, Hvnd, Hond, Hlnd, Hnnd, Hal⟩ := Hok
  obtain ⟨Hx, Ho, Hl, Hn⟩ := H
  refine ⟨⟨(perm_elements_listToSet _ Hvnd).trans Hx.symm,
    (perm_elements_listToSet _ Hlnd).trans Hl.symm,
    (perm_elements_listToSet _ Hond).trans Ho.symm,
    (perm_elements_listToSet _ Hnnd).trans Hn.symm⟩, ?_⟩
  show c.AutoLeave' = if c.VotersOutgoing' = [] then false else c.AutoLeave'
  by_cases ho : c.VotersOutgoing' = []
  · rw [ite_eq_left ho]; exact Hal ho
  · rw [ite_eq_right ho]

/-- `confchange.Restore` of a well-formed conf state on the empty tracker: the configuration
`switchToConfig` takes (`ownConfigC`) at `Restore`'s model's answer. -/
private theorem wp_Restore_ok (H : confchange.Restore.spec (GF := GF) (hG := hG))
    (chg : confchange.Changer) (cs : Loc) (c : ConfStateM) (dq : DFrac) (v0 : Loc)
    (cs' : CCState) (Hok : ConfStateOk c)
    (Hres : restoreM c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext' c.AutoLeave' =
      some cs')
    (Hlen : (GMap.size (GMap.listToSet c.Voters' ∪ GMap.listToSet c.VotersOutgoing' ∪
      GMap.listToSet c.Learners' ∪ GMap.listToSet c.LearnersNext') : Int) ≤ 2 ^ 62)
    (Hmi : 0 ≤ sint.Z chg.Tracker'.MaxInflight' ∧ sint.Z chg.Tracker'.MaxInflight' < 2 ^ 62)
    (Harr : chg.Tracker'.Config'.Voters'.arr = [v0, map.nil])
    (Hl : chg.Tracker'.Config'.Learners' = map.nil)
    (Hln : chg.Tracker'.Config'.LearnersNext' = map.nil)
    (Hal : chg.Tracker'.Config'.AutoLeave' = false) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗
        ownCSM cs dq c ∗ v0 ↦$ (∅ : GMap w64 Unit) ∗
        chg.Tracker'.Progress' ↦$□ (∅ : GMap w64 Loc) }}
      (App (App (Val #(functions confchange.Restore [])) (Val #chg)) (Val #cs))
    {{ (cfgv : tracker.Config) (prsm : Loc), RET (PairV (PairV #cfgv #prsm) #interface.nil);
        |==> (ownCSM cs dq c ∗
          ∃ (prs : GMap w64 Loc) (pvs : GMap w64 Progress), ownConfigC cs'.cfg cfgv prsm prs pvs) }} := by
  have Hcs' := confStateOk_cfg c cs' Hok Hres
  subst Hcs'
  obtain ⟨Hwfe, Hvnd, Hond, Hlnd, Hnnd, Hal0⟩ := Hok
  rcases Hwfe with Hwf | ⟨h1, h2, h3, h4⟩
  · -- well-formed: fresh maps (`raft.appliedSnap`'s)
    iintro %Φ ⟨#Hpkg, Hcs, Hv0, #Hpm⟩ HΦ
    have Hvne : c.Voters' ≠ [] := Hwf.1
    have Hrm := restoreM_wf _ _ _ _ c.AutoLeave' Hwf
    have Hinv := restoreM_cfgInv Hrm
    iapply H chg cs c dq v0 _ Hrm Hmi Harr Hl Hln Hal $$ [$Hpkg $Hcs $Hv0 $Hpm]
    inext
    iintro %cfgv %prsm %prs ⟨Hcs, -, -, Hres⟩
    icases Hres with (⟨%Hops, -⟩ | ⟨-, Hcfg, Hprsm, %Hprs, Hprogs⟩)
    · exfalso; exact restoreSimpleOps_ne_nil_of_voters _ _ _ _ Hvne Hops
    iapply HΦ
    ipersist Hprsm
    have Hsz' : (GMap.size prs : Int) ≤ 2 ^ 62 :=
      restore_prs_size_ids c.lists Hlen prs c.AutoLeave' Hprs
    ihave Hcfg := ownCfgCC_cast cfgv (DFrac.own 1)
      (cfgStateC (csCfgM c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext' c.AutoLeave')).cfg
      (csCfgM c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext' c.AutoLeave') rfl $$ Hcfg
    icases ownConfigC_of_restore _ cfgv prsm prs Hinv Hprs Hsz' _ (fun _ _ h => h)
      $$ Hcfg Hprsm Hprogs with ⟨%pvs, Hnew⟩
    imodintro
    iframe Hcs
    iexists prs, pvs
    iExactEq Hnew; rfl
  · -- empty: no op, the tracker's own maps (`wp_Restore_voters`)
    iintro %Φ Hpre HΦ
    iapply wp_Restore_voters H chg cs c dq v0 Hvnd (by rw [h1]; exact List.not_mem_nil)
      (by rw [h1]; decide) h2 h3 h4 Hmi Harr Hl Hln Hal $$ Hpre
    inext
    iintro %cfgv %prsm Hr
    iapply HΦ
    imod Hr with ⟨Hcs, %prs, Hcfg, %Hdom⟩
    icases ownConfig_values $$ Hcfg with ⟨%pvs, Hcfg⟩
    ihave Hcfg := ownConfigV_toC _ _ _ _ _ $$ Hcfg
    imodintro
    iframe Hcs
    iexists prs, pvs
    rw [h1] at Hdom
    have Hd0 : domSet prs \ GMap.listToSet ([] : List w64) = (∅ : GSet w64) := by
      rw [Hdom]
      apply GMap.set_eq; intro k
      rw [GMap.elem_of_difference]
      exact ⟨fun h => absurd h.1 h.2, fun h => absurd h (GMap.not_elem_of_empty _)⟩
    iExactEq Hcfg
    rw [Hal0 h2, h1, h2, h3, h4, Hd0]
    rfl

-- (2026-11-12, trace-check step 5) both modes' proofs in one declaration
set_option maxHeartbeats 1600000 in
theorem newRaft.wp_proof
    (wp_Config_validate : Config.validate.spec (GF := GF) (hG := hG))
    (wp_newLogWithSize : newLogWithSize.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastEntryID : raftLog.lastEntryID.spec (GF := GF) (hG := hG))
    (wp_MakeProgressTracker : tracker.MakeProgressTracker.spec (GF := GF) (hG := hG))
    (wp_newReadOnly : newReadOnly.spec (GF := GF) (hG := hG))
    (wp_traceInitState : traceInitState.spec (GF := GF) (hG := hG))
    (wp_confchange_Restore : confchange.Restore.spec (GF := GF) (hG := hG))
    (wp_traceConfChangeEvent : traceConfChangeEvent.spec (GF := GF) (hG := hG))
    (wp_ProgressTracker_ConfState : tracker.ProgressTracker.ConfState.spec (GF := GF) (hG := hG))
    (wp_assertConfStatesEquivalent : assertConfStatesEquivalent.spec (GF := GF) (hG := hG))
    (wp_IsEmptyHardState : IsEmptyHardState.spec (GF := GF) (hG := hG))
    (wp_HardState_GetCommit : raftpb.HardState.GetCommit.spec (GF := GF) (hG := hG))
    (wp_HardState_GetTerm : raftpb.HardState.GetTerm.spec (GF := GF) (hG := hG))
    (wp_HardState_GetVote : raftpb.HardState.GetVote.spec (GF := GF) (hG := hG))
    (wp_raft_becomeFollower : raft.becomeFollower.spec (GF := GF) (hG := hG))
    (wp_ProgressTracker_VoterNodes : tracker.ProgressTracker.VoterNodes.spec (GF := GF) (hG := hG))
    (wp_fmt_Sprintf : fmt.Sprintf.spec (GF := GF) (hG := hG))
    (wp_strings_Join : strings.Join.spec (GF := GF) (hG := hG)) :
    newRaft.spec (GF := GF) (hG := hG) := by
  have wp_bfU := raft.becomeFollower.untraced wp_raft_becomeFollower
  intro c cv lok si sn σ hs csm R R' cs' γ vs Hvalid Hlok Hsto HmaxInfl Hdpf Hros Hdccv Hmcs Hidx Hpend
    Hfr1 Hfr2 Hfl0 Hsg0 Hdt Hwrap Hrec Hhs Happ Hres Hlen Hcsok Hfresh
  rcases Option.eq_none_or_eq_some γ.reTrace with Htrm | ⟨γd, Htrm⟩
  · rw [Htrm]
    obtain ⟨HvID, HvID1, HvID2, Hticks, HvSt, HvInfl, HvIB, HvLog, HvRO⟩ := Hvalid
    -- the restored commit `C`, the applied index `A'` the node starts at, the base `b`
    have HbZ := uint_nat_eq σ.prev.index'
    have HCle : uint.Z σ.prev.index' ≤ uint.Z (committedAfter σ.prev hs) ∧
        uint.Z (committedAfter σ.prev hs) ≤ uint.Z σ.prev.index' + (σ.ents.length : Int) := by
      unfold committedAfter
      split
      · constructor <;> omega
      · rcases Hhs with h | h
        · rename_i hn; exact absurd h hn
        · exact h
    wp_start as ⟨Hc, #Hlg0, HR, #HFI, #HLI, #HInit, Hcs0⟩
    wp_auto
    wp_apply wp_Config_validate _ _ ⟨HvID, HvID1, HvID2, Hticks, HvSt, HvInfl, HvIB, HvLog, HvRO⟩
      $$ [$Hc] as %cv' ⟨Hc, %Hpres⟩
    obtain ⟨HpID, HpET, HpHT, HpSt, HpAp, HpMI, HpCQ, HpPV, HpDPF, HpLg, HpMC, HpAW, HpRO, HpDCC,
      HpSDR, HpTL⟩ := Hpres
    rw [HpSt, Hsto, HpLg, Hlok]
    have Hmcs' : 0 < uint.Z cv'.MaxCommittedSizePerReady' := by
      rw [HpMC]
      split
      · rename_i Hz
        rcases Hmcs with Hc | Hc
        · exact absurd Hz Hc
        · have : uint.Z cv.MaxSizePerMsg' ≠ 0 := fun H0 => Hc (by word)
          word
      · rename_i Hz
        have : uint.Z cv.MaxCommittedSizePerReady' ≠ 0 := fun H0 => Hz (by word)
        word
    wp_apply wp_newLogWithSize _ _ _ sn lok R (uint.nat σ.prev.index')
        (uint.nat σ.prev.index' + σ.ents.length) rfl Hmcs' (by omega) (by push_cast; omega)
      $$ [$HR $Hlg0]
      as %l %ip ⟨HR, %Hip0, %lv0, Hl, %Hlv0, HLback⟩
    · isplitr
      · push_cast; iapply HFI
      · push_cast; iapply HLI
    obtain ⟨Hlst, Hlcm, Hlap, Hlapg, Hlsn, Hlen0, Hloff, Hlip, Hlsip, Hlasz, Hlpz, Hlamx⟩ := Hlv0
    rw [HpSt, Hsto]
    wp_apply HInit $$ [$HR] as %hp %cs %al ⟨#Hhsp, #Hcs, Hup⟩
    imod Hup with ⟨#HisSto, HSto, #Hnc, HR⟩
    -- the catch-up with the attach record (`storCaught`): the floor at `max b A`, the record's terms
    -- certified
    obtain ⟨Ha0, Hc0, Hct, Hcomp⟩ := Hrec
    let M : GMap Nat w64 := ctMap (sn.ct.filter (fun p => decide (p.1 ≤ sn.c0)))
    have HM : ∀ i t, i ≤ sn.c0 ∧ (i, t) ∈ sn.ct → M !! i = some t := by
      intro i t ⟨hi, hm⟩
      have h1 := (Hct i t hm (by omega)).1
      obtain ⟨t0, -, hu⟩ := Hcomp i h1 (by omega)
      refine ctMap_lookup (List.mem_filter.2 ⟨hm, by simp [hi]⟩) (fun t' ht' => ?_)
      rw [hu t' (List.mem_filter.1 ht').1, hu t hm]
    have HMk : ∀ k t, M !! k = some t → k ≤ uint.nat (committedAfter σ.prev hs) ∧
        (uint.nat σ.prev.index' ≤ k → termAt σ.prev σ.ents (W64 (k : Int)) = some t) := by
      intro k t h
      obtain ⟨hm, hk⟩ := List.mem_filter.1 (ctMap_mem h)
      simp only [decide_eq_true_eq] at hk
      rw [Hc0] at hk
      exact ⟨hk, (Hct k t hm (by omega)).2⟩
    have HA0 : (sn.a0 : Int) < 2 ^ 64 := by
      rw [Ha0]; have := uint_nat_eq cv.Applied'; have := word.unsigned_range cv.Applied'
      have := word.unsigned_range σ.prev.index'; omega
    imod ownStorage_catchUp sn (interface.ok si) σ M
      (by rw [Ha0]; have := uint_nat_eq σ.fl; omega) HA0 Hdt HM $$ HSto with HSto
    let σ1 : StorState := { σ with fl := W64 (sn.a0 : Int), dt := M }
    have Hfl1 : uint.nat σ1.fl = sn.a0 := by
      show uint.nat (W64 (sn.a0 : Int)) = sn.a0
      have := uint_Z_W64 (sn.a0 : Int) (by omega) HA0
      have := uint_nat_eq (W64 (sn.a0 : Int)); omega
    -- the struct
    wp_apply wp_MakeProgressTracker as %tv0 %v0 ⟨%Htv0, Hv0, Hvotes, Hprs0⟩
    obtain ⟨Htv0mi, Htv0mb, Htv0arr, Htv0l, Htv0ln, Htv0al⟩ := Htv0
    wp_apply wp_newReadOnly _ (HpRO.trans Hros) as %ro Hro
    imod raftOwn_of_pts «$r0_ptr» _ $$ «$r0» with «$r0»
    ihave #Htlf := raftOwn_traceLogger _ _ $$ «$r0»

    iunfold trCapStart at Hcs0
    icases Hcs0 with %Htlk
    have Htlk' : TraceLoggerOk cv'.TraceLogger' := HpTL ▸ Htlk
    wp_apply wp_traceInitState «$r0_ptr» _ none (fun _ => True) iprop(True) iprop(emp) $$ [Htlf] as -
    · isplitr
      · iexact Htlf
      isplitr
      · iapply trOwn_none_intro
      iapply (traceFire_none _ _ _).2
      isplitr
      · ipureintro; exact Htlk'
      itrivial
    have HA0C : sn.a0 ≤ uint.nat (committedAfter σ.prev hs) := by
      rw [Ha0]
      have := uint_nat_eq (committedAfter σ.prev hs); have := uint_nat_eq cv.Applied'
      rcases Happ with h | h
      · rw [h]; have : uint.nat (W64 0) = 0 := rfl; omega
      · omega
    have HfE : uint.Z σ1.fl ≤ uint.Z σ1.prev.index' + (σ1.ents.length : Int) := by
      have := uint_nat_eq σ1.fl; have := uint_nat_eq (committedAfter σ.prev hs); show _ ≤ uint.Z σ.prev.index' + (σ.ents.length : Int); omega
    iunfold raftOwn at «$r0»
    iNamed «$r0»
    wp_auto
    -- `lastID := r.raftLog.lastEntryID()`
    wp_apply wp_lastEntryID_w l lv0 si sn σ1 Hlst Hlsn Hlen0 Hpend
        (by rw [Hloff, Hip0]; push_cast; show _ = uint.Z σ.prev.index' + (σ.ents.length : Int) + 1; omega)
        HfE (by show uint.Z σ.prev.index' + (σ.ents.length : Int) + 1 < 2 ^ 64; omega)
      $$ [$Hl $HisSto $HSto] as %lastID ⟨Hl, HSto⟩
    -- `confchange.Restore` on the empty tracker: `Restore`'s configuration `cs'.cfg`
    have Hmi : 0 ≤ sint.Z tv0.MaxInflight' ∧ sint.Z tv0.MaxInflight' < 2 ^ 62 := by
      rw [Htv0mi, HpMI]; omega
    ipersist Hprs0
    ihave Hcsw := csPts_weaken $$ Hcs
    try wp_auto
    wp_apply wp_Restore_ok wp_confchange_Restore ⟨tv0, lastID.index'⟩ cs csm DFrac.discard v0 cs'
        Hcsok Hres Hlen Hmi Htv0arr Htv0l Htv0ln Htv0al $$ [$Hcsw $Hv0 $Hprs0]
      as %cfgv %prsm Hres'
    imod Hres' with ⟨Hcsw, %prs, %pvs, Hcfg⟩
    try wp_auto
    -- `assertConfStatesEquivalent(r.logger, cs, r.switchToConfig(cfg, trk))`
    ihave #Hlgf : «$r0_ptr».[raft, go!"logger"] ↦□ interface.ok lok $$ [H_logger]
    · rw [← Hlok, ← HpLg]; iexact H_logger
    ihave H_state : «$r0_ptr».[raft, go!"state"] ↦ StateFollower $$ [H_state]
    · iExactEq H_state; rfl
    wp_apply wp_switchToConfig_w wp_traceConfChangeEvent wp_ProgressTracker_ConfState cs'.cfg
        «$r0_ptr» cv'.ID' lok false tv0 ∅ cfgv prsm prs pvs Hmi _ Htlk'
      $$ [$H_trk $Htlf $H_id $Hlgf $Hlg0 $H_isLearner $H_state $Hvotes $Hcfg]
      as %cs2 %xs2 %os2 %ls2 %lns2 %bl ⟨H_trk, Htrk, H_isLearner, H_state, Hcs2, %Hcs2p⟩
    obtain ⟨Hperm, Hal2⟩ := confStateOk_perm csm cs' Hcsok Hres xs2 os2 ls2 lns2 Hcs2p
    icases ownTrackerC_progress_map _ _ _ $$ Htrk with ⟨-, %Hdom2, Htrk⟩
    ihave Hcs2v := csPts_weaken $$ Hcs2
    wp_apply wp_assertConfStatesEquivalent _ cs cs2 csm
        (ConfStateM.mk xs2 ls2 os2 lns2 cs'.cfg.autoLeave) DFrac.discard (DFrac.own 1) Hperm
        (lists_bounded_of_ids csm.lists Hcsok.2.1 Hcsok.2.2.1 Hcsok.2.2.2.1 Hcsok.2.2.2.2.1 Hlen) Hal2
      $$ [$Hcsw $Hcs2v] as ⟨-, -⟩
    have HbW : (W64 (uint.nat σ.prev.index' : Int)) = σ.prev.index' := by
      apply uint_Z_inj.1; rw [uint_Z_W64 _ (by omega) (by have := word.unsigned_range σ.prev.index'; omega)]
    -- `if !IsEmptyHardState(hs) { r.loadState(hs) }`: both arms at the restored commit
    wp_join iprop(«$r0_ptr».[raft, go!"Term"] ↦ hs.Term' ∗ «$r0_ptr».[raft, go!"Vote"] ↦ hs.Vote' ∗
        «$r0_ptr».[raft, go!"raftLog"] ↦ l ∗
        l ↦ { lv0 with committed' := committedAfter σ.prev hs } ∗
        ownStorage sn (interface.ok si) σ1 ∗ hs_ptr ↦ hp ∗ r_ptr ↦ «$r0_ptr») at next
      with [H_Term H_Vote H_raftLog Hl HSto hs r] as ⟨H_Term, H_Vote, H_raftLog, Hl, HSto, hs, r⟩
    · wp_apply wp_IsEmptyHardState hp hs $$ []
      · simp only [named]; iexact Hhsp
      by_cases Hemp : HsEmpty hs
      · rw [decide_eq_true (show hs.Term' = W64 0 ∧ hs.Vote' = W64 0 ∧ hs.Commit' = W64 0 from Hemp)]
        wp_auto
        have Hca : committedAfter σ.prev hs = σ.prev.index' := by
          unfold committedAfter; rw [ite_eq_left Hemp]
        obtain ⟨HT, HV, HC⟩ := Hemp
        isplitr
        · ipureintro; rfl
        iframe HSto hs r H_raftLog
        isplitl [H_Term]
        · iExactEq H_Term; rw [HT]; rfl
        isplitl [H_Vote]
        · iExactEq H_Vote; rw [HV]; rfl
        iExactEq Hl
        rw [Hca, ← HbW, ← Hlcm]
      · rw [decide_eq_false (show ¬ (hs.Term' = W64 0 ∧ hs.Vote' = W64 0 ∧ hs.Commit' = W64 0) from Hemp)]
        wp_auto
        iunfold hsOpt at Hhsp
        icases Hhsp with (⟨%Hn, %Hz⟩ | #Hhro)
        · exfalso; apply Hemp; rw [Hz]; exact ⟨rfl, rfl, rfl⟩
        have Hca : committedAfter σ.prev hs = hs.Commit' := by
          unfold committedAfter; rw [ite_eq_right Hemp]
        have Hcr := Hhs.resolve_left Hemp
        wp_apply wp_loadState_w wp_HardState_GetCommit wp_HardState_GetTerm wp_HardState_GetVote
            «$r0_ptr» l lv0 _ _ si sn σ1 hp hs Hlst Hlsn Hlen0 Hpend
            (by rw [Hlcm, HbW]; exact ⟨Hcr.1, Hcr.2⟩)
          $$ [$H_raftLog $H_Term $H_Vote $Hl $HisSto $HSto $Hhro]
          as ⟨H_raftLog, H_Term, H_Vote, Hl, HSto⟩
        try wp_auto
        isplitr
        · ipureintro; rfl
        iframe HSto hs r H_raftLog H_Term H_Vote
        iExactEq Hl
        rw [Hca]
    -- `if c.Applied > 0 { raftlog.appliedTo(c.Applied, 0) }`: both arms at the applied index `ap`
    let ap : w64 := if cv.Applied' = W64 0 then σ.prev.index' else cv.Applied'
    rw [HpAp]
    wp_join iprop(l ↦ ({ lv0 with committed' := committedAfter σ.prev hs, applied' := ap, applying' := ap } : raftLog) ∗ c_ptr ↦ c ∗ c ↦ cv' ∗ raftlog_ptr ↦ l)
      with [Hl c Hc raftlog] as ⟨Hl, c, Hc, raftlog⟩
    · have Ha0 : cv.Applied' ≠ W64 0 := by intro h; rw [h] at Hif; exact absurd Hif (by decide)
      have Har := Happ.resolve_left Ha0
      wp_apply wp_appliedTo_w l { lv0 with committed' := committedAfter σ.prev hs } cv'.Applied'
          (by simp only; rw [Hlap, HbW, HpAp]; exact Har)
          (by simp only; rw [Hlapg, HbW, HpAp]; exact Har.1)
          Hlasz (by rw [Hlamx]; exact Hmcs') Hlpz $$ [$Hl] as Hl
      try wp_auto
      try (isplitr; · ipureintro; rfl)
      iframe c Hc raftlog
      iExactEq Hl
      simp only [ap, Ha0, ↓reduceIte, HpAp]
    · have Ha0 : cv.Applied' = W64 0 := by word
      iframe c Hc raftlog
      iExactEq Hl
      simp only [ap, Ha0, ↓reduceIte]
      rw [Hlapg, Hlap, HbW]
    -- the window closes: the log at the restored commit and applied index (`newLogWithSize`'s wand)
    have HAap : uint.nat ap = sn.a0 := by
      rw [Ha0]
      by_cases h : cv.Applied' = W64 0
      · simp only [ap, h, ↓reduceIte]; have : uint.nat (W64 0) = 0 := rfl; omega
      · simp only [ap, h, ↓reduceIte]
        have := Happ.resolve_left h; have := uint_nat_eq cv.Applied'; omega
    have HCn := uint_nat_eq (committedAfter σ.prev hs)
    ihave HL := HLback $$ %σ1 %(committedAfter σ.prev hs) %ap
      %(by exact ⟨rfl, rfl, Hidx, Hpend, Hfr1, Hfr2, Hsg0, by omega, by omega, by omega, by omega, HMk⟩)
      Hl HisSto HSto
    -- the struct, sealed at `Restore`'s configuration
    ihave Hmisc : ownRaftMisc (GF := GF) slice.nil ro slice.nil ({} : RdState) $$ [Hro]
    · unfold ownRaftMisc
      simp only [named]
      isplitr
      · iunfold readStatesPts
        iexists []
        isplitr
        · iapply ownSlice_nil
        iapply BigSepL2.bigSepL2_nil.2; iempintro
      isplitr
      · iapply ownSliceCap_nil
      isplitl [Hro]
      · iexact Hro
      isplitr
      · iexists []
        isplitr
        · iapply ownSlice_nil
        iapply BigSepL2.bigSepL2_nil.2; iempintro
      iapply ownSliceCap_nil
    ihave Hnil1 : (slice.nil ↦* (([] : List QMsg).map QMsg.loc) : IProp GF) $$ []
    · rw [List.map_nil]; iapply ownSlice_nil
    ihave Hnil2 : (slice.nil ↦* (([] : List QMsg).map QMsg.loc) : IProp GF) $$ []
    · rw [List.map_nil]; iapply ownSlice_nil
    ihave Hcap1 := ownSliceCap_nil (V := Loc) (GF := GF)
    ihave Hcap2 := ownSliceCap_nil (V := Loc) (GF := GF)
    ihave Hob := outboxRel_nil (GF := GF)
    ihave #Hns0 := NsCap.off (GF := GF) (interface.ok si)
    ihave #Hsc0 : qSrcs (GF := GF) sn ([] ++ []) $$ []
    · rw [List.append_nil]; iapply qSrcs_nil
    let rv2 : raft :=
      { id' := cv'.ID', Term' := hs.Term', Vote' := hs.Vote', readStates' := slice.nil, raftLog' := l,
        maxMsgSize' := cv'.MaxSizePerMsg', maxUncommittedSize' := cv'.MaxUncommittedEntriesSize',
        trk' := { tv0 with Config' := cfgv, Progress' := prsm }, state' := StateFollower,
        isLearner' := bl, msgs' := slice.nil, msgsAfterAppend' := slice.nil, lead' := W64 0,
        leadTransferee' := 0, pendingConfIndex' := 0,
        disableConfChangeValidation' := cv'.DisableConfChangeValidation', uncommittedSize' := 0,
        readOnly' := ro, electionElapsed' := 0, heartbeatElapsed' := 0, checkQuorum' := cv'.CheckQuorum',
        preVote' := cv'.PreVote', heartbeatTimeout' := cv'.HeartbeatTick',
        electionTimeout' := cv'.ElectionTick', randomizedElectionTimeout' := 0,
        disableProposalForwarding' := cv'.DisableProposalForwarding',
        stepDownOnRemoval' := cv'.StepDownOnRemoval', tick' := func.nil, step' := func.nil,
        logger' := cv'.Logger', pendingReadIndexMessages' := slice.nil,
        traceLogger' := cv'.TraceLogger' }
    ihave Hro : raftOwn (GF := GF) «$r0_ptr» rv2 $$ [H_Term H_Vote H_readStates H_raftLog H_maxMsgSize
        H_maxUncommittedSize H_trk H_state H_isLearner H_msgs H_msgsAfterAppend H_lead
        H_leadTransferee H_pendingConfIndex H_disableConfChangeValidation H_uncommittedSize
        H_readOnly H_electionElapsed H_heartbeatElapsed H_checkQuorum H_preVote H_heartbeatTimeout
        H_electionTimeout H_randomizedElectionTimeout H_disableProposalForwarding H_tick H_step
        H_pendingReadIndexMessages H_traceLogger]
    · unfold raftOwn
      simp only [named]
      iframe
      isplitr
      · iexact H_id
      isplitr
      · iexact H_checkQuorum
      isplitr
      · iexact H_stepDownOnRemoval
      isplitr
      · iexact H_logger
      iexact Htlf
    let ls2 : LogState :=
      { prev := σ.prev, sents := σ.ents, uents := [], committed := committedAfter σ.prev hs,
        applied := ap, snap := none, inprogress := ip, applying := ap, unpersisted := [],
        stored := σ.ents, apsize := W64 0, apmax := cv'.MaxCommittedSizePerReady',
        storage := interface.ok si, ksn := [], sn := sn, fl := σ1.fl, sg := σ.sg,
        dtk := uint.nat (committedAfter σ.prev hs) }
    let s2 : NState :=
      { term := hs.Term', vote := hs.Vote', lead := W64 0, role := .follower, votes := ∅,
        outbox := [], stepfn := func.nil, ticking := false, progress := prs, log := l, logst := ls2,
        prvals := pvs, prevote := cv.PreVote', gh := { sn := sn }, isLearner := bl,
        sdr := cv'.StepDownOnRemoval', cq := cv.CheckQuorum' }
    ihave Hphys := ownRaftPhysCV_intro cs'.cfg cs'.cfg.voters «$r0_ptr» cv.ID' s2 rv2 [] [] lok
      HpID rfl rfl rfl rfl rfl ⟨HpPV, fun h => absurd h (by simp only [s2]; decide)⟩
      (by simp only [rv2]; rw [HpDPF, Hdpf]) (by simp only [rv2]; rw [HpDCC, Hdccv])
      HpCQ
      rfl ⟨rfl, fun h => HvID h.symm⟩ rfl rfl HvID
      (by show 0 < sint.Z cv'.ElectionTick'; rw [HpET]; omega) (by simp only [rv2]; rw [HpLg, Hlok])
      (by simp only [rv2]; exact Htlk')
      rfl (fun h => absurd h (by simp only [s2]; decide))
      ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
      (fun _ h => absurd h List.not_mem_nil) (Nat.zero_le _)
      ⟨fun h => absurd h Bool.false_ne_true,
        SnpOk.of_none rfl rfl rfl rfl, rfl⟩
      (fun h => absurd rfl h) (PrvalsOk.not_leader (by simp only [s2]; decide)) (LogNsOk.off rfl)
      (XfOk.nil (fun h => absurd h (by simp only [s2]; decide))) (LqOk.nil _ _)
      $$ Hro Hlg0 Htrk HL Hnil1 Hcap1 Hnil2 Hcap2 Hmisc Hob Hns0 Hsc0
    try wp_auto
    -- `r.becomeFollower(r.Term, None)`
    wp_apply wp_bfU _ _ _ s2 s2.term (W64 0) (Int.le_refl _) (by tr_none) $$ [$Hphys]
      as %pvs3 Hphys
    let s3 : NState := { becomeFollower s2 s2.term (W64 0) with prvals := pvs3 }
    -- `r.trk.VoterNodes()`
    icases ownRaftPhysC_tracker_same _ _ _ s3 $$ Hphys with ⟨%tv3, Htrkf, Htrk3, Htrkback⟩
    wp_apply wp_ProgressTracker_VoterNodes $$ [$Htrkf $Htrk3] as %nsl %nxs ⟨Htrkf, Htrk3, Hnsl, %Hnxs⟩
    ihave Hphys := Htrkback $$ %tv3 Htrkf Htrk3
    -- the log line's `nodesStrs` loop; what it builds is never read
    ihave IH : iprop(∃ (k x : w64) (sl' : GoSlice) (strs : List GoString),
        "i" ∷ i_ptr ↦ k ∗ "n" ∷ n_ptr ↦ x ∗ "nodesStrs" ∷ nodesStrs_ptr ↦ sl' ∗
        "Hstrs" ∷ sl' ↦* strs ∗
        "Hstrs_cap" ∷ ownSliceCap GoString sl' (DFrac.own 1) ∗
        "Hnsl" ∷ nsl ↦* nxs ∗
        "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (nxs.length : Int)⌝) $$ [i n nodesStrs Hnsl]
    · iexists W64 0, _, slice.nil, []
      iframe i n nodesStrs Hnsl
      isplitr
      · iapply ownSlice_nil
      isplitr
      · iapply ownSliceCap_nil
      ipureintro; constructor <;> word
    wp_for IH
    wp_if_destruct
    · ihave %Hnl := ownSlice_len $$ Hnsl
      have Hlt : (sint.Z k).toNat < nxs.length := by word
      list_elem nxs (sint.Z k).toNat as e
      rw [ite_eq_left (show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z nsl.len by word)]
      wp_apply wp_load_slice_index nsl (sint.Z k) nxs (DFrac.own 1) e Hk.1 $$ [Hnsl] as Hnsl
      · iframe; ipureintro; exact He_lookup
      wp_apply wp_slice_literal
      try (isplitr; (ipureintro; rfl))
      iintro %sla ⟨Hargs, -⟩
      wp_auto
      wp_apply wp_fmt_Sprintf $$ [$Hargs] as %str Hargs
      · ipureintro
        exact _root_.Perennial.fmt.ArgsWf.cons_int _ _ _ (.uint64 _) _root_.Perennial.fmt.ArgsWf.nil
      wp_apply wp_slice_literal
      try (isplitr; (ipureintro; rfl))
      iintro %sl2 ⟨Hsl2, -⟩
      wp_auto
      wp_apply wp_slice_append $$ [$Hstrs $Hstrs_cap $Hsl2] as %sl3 ⟨Hstrs, Hstrs_cap, -⟩
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro; constructor <;> word
    -- the log line: `r.id`, `strings.Join(nodesStrs, ",")`, `r.Term`, then
    -- `r.raftLog.committed` and `r.raftLog.applied` through the log
    wp_apply wp_strings_Join $$ [$Hstrs] as %joined Hstrs
    wp_apply raft.wp_load_TermC $$ Hphys as Hphys
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_same _ _ _ s3 $$ Hphys with ⟨Hlog3, Hlogback⟩
    icases ownRaftLog_struct _ _ $$ Hlog3 with ⟨%lv3, Hl3, -, Hl3back⟩
    wp_auto
    ihave Hlog3 := Hl3back $$ Hl3
    ihave Hphys := Hlogback $$ Hlog3
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_same _ _ _ s3 $$ Hphys with ⟨Hlog3, Hlogback⟩
    icases ownRaftLog_struct _ _ $$ Hlog3 with ⟨%lv4, Hl3, -, Hl3back⟩
    wp_auto
    ihave Hlog3 := Hl3back $$ Hl3
    ihave Hphys := Hlogback $$ Hlog3
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    try iintro %_ ⟨_, -⟩
    try wp_auto
    wp_apply Logger.wp_logf lok _ _ _ (by decide) $$ Hlg0
    try wp_auto
    iapply HΦ $$ %«$r0_ptr» %s3 %cv'
    iframe HR Hphys Hc
    isplitr
    · ipureintro; exact HpAW
    -- (step 5) untraced: the storage's no-compaction handed on, the capability `emp`
    ihave Hemp : trCapB (GF := GF) none γ «$r0_ptr» cv.ID' (bootCfg vs) false (bootPhase vs cv.ID')
        (bootAt vs cv.ID' 2) $$ []
    · simp only [trCapB]; iempintro
    iframe Hnc Hemp
    -- `becomeFollower(r.Term, None)` keeps the term, so `reset` keeps the
    -- vote: the state is the persisted `HardState`'s
    ipureintro
    refine ⟨⟨rfl, rfl⟩, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, HpSDR, ?_, rfl⟩
    · show (if s2.term = s2.term then s2.vote else W64 0) = hs.Vote'
      simp only [↓reduceIte]
      rfl
    · show ap = w64Max σ.prev.index' ap
      unfold w64Max
      rw [ite_eq_right (by
        by_cases h : cv.Applied' = W64 0
        · simp only [ap, h, ↓reduceIte]; exact Int.lt_irrefl _
        · simp only [ap, h, ↓reduceIte]; have := (Happ.resolve_left h).1; omega)]
    · show domSet prs = domSet cs'.prs
      rw [Hdom2, confStateOk_cfg csm cs' Hcsok Hres]
      apply GMap.set_eq; intro k
      rw [GMap.elem_of_dom']
      simp only [cfgStateC, CfgM.ids]
      rw [cfgFlags_mem, GMap.elem_of_union]

  · rw [Htrm]
    obtain ⟨HhsE, Hp0, He0, Hv0e, Hvo0, Hl0e, Hln0, Hal0⟩ := Hfresh (by rw [Htrm]; simp)
    have HAz : cv.Applied' = W64 0 := by
      rcases Happ with h | ⟨h1, h2⟩
      · exact h
      · have hc : committedAfter σ.prev hs = σ.prev.index' := by
          unfold committedAfter; rw [ite_eq_left HhsE]
        rw [hc] at h2
        apply uint_Z_inj.1
        have : uint.Z (W64 0) = 0 := rfl
        rw [Hp0] at h1 h2; simp only at h1 h2
        omega
    obtain ⟨HvID, HvID1, HvID2, Hticks, HvSt, HvInfl, HvIB, HvLog, HvRO⟩ := Hvalid
    -- the restored commit `C`, the applied index `A'` the node starts at, the base `b`
    have HbZ := uint_nat_eq σ.prev.index'
    have HCle : uint.Z σ.prev.index' ≤ uint.Z (committedAfter σ.prev hs) ∧
        uint.Z (committedAfter σ.prev hs) ≤ uint.Z σ.prev.index' + (σ.ents.length : Int) := by
      unfold committedAfter
      rw [ite_eq_left HhsE]
      constructor <;> omega
    wp_start as ⟨Hc, #Hlg0, HR, #HFI, #HLI, #HInit, Hcs0⟩
    wp_auto
    wp_apply wp_Config_validate _ _ ⟨HvID, HvID1, HvID2, Hticks, HvSt, HvInfl, HvIB, HvLog, HvRO⟩
      $$ [$Hc] as %cv' ⟨Hc, %Hpres⟩
    obtain ⟨HpID, HpET, HpHT, HpSt, HpAp, HpMI, HpCQ, HpPV, HpDPF, HpLg, HpMC, HpAW, HpRO, HpDCC,
      HpSDR, HpTL⟩ := Hpres
    rw [HpSt, Hsto, HpLg, Hlok]
    have Hmcs' : 0 < uint.Z cv'.MaxCommittedSizePerReady' := by
      rw [HpMC]
      split
      · rename_i Hz
        rcases Hmcs with Hc | Hc
        · exact absurd Hz Hc
        · have : uint.Z cv.MaxSizePerMsg' ≠ 0 := fun H0 => Hc (by word)
          word
      · rename_i Hz
        have : uint.Z cv.MaxCommittedSizePerReady' ≠ 0 := fun H0 => Hz (by word)
        word
    wp_apply wp_newLogWithSize _ _ _ sn lok R (uint.nat σ.prev.index')
        (uint.nat σ.prev.index' + σ.ents.length) rfl Hmcs' (by omega) (by push_cast; omega)
      $$ [$HR $Hlg0]
      as %l %ip ⟨HR, %Hip0, %lv0, Hl, %Hlv0, HLback⟩
    · isplitr
      · push_cast; iapply HFI
      · push_cast; iapply HLI
    obtain ⟨Hlst, Hlcm, Hlap, Hlapg, Hlsn, Hlen0, Hloff, Hlip, Hlsip, Hlasz, Hlpz, Hlamx⟩ := Hlv0
    rw [HpSt, Hsto]
    wp_apply HInit $$ [$HR] as %hp %cs %al ⟨#Hhsp, #Hcs, Hup⟩
    imod Hup with ⟨#HisSto, HSto, #Hnc, HR⟩
    -- the catch-up with the attach record (`storCaught`): the floor at `max b A`, the record's terms
    -- certified
    obtain ⟨Ha0, Hc0, Hct, Hcomp⟩ := Hrec
    let M : GMap Nat w64 := ctMap (sn.ct.filter (fun p => decide (p.1 ≤ sn.c0)))
    have HM : ∀ i t, i ≤ sn.c0 ∧ (i, t) ∈ sn.ct → M !! i = some t := by
      intro i t ⟨hi, hm⟩
      have h1 := (Hct i t hm (by omega)).1
      obtain ⟨t0, -, hu⟩ := Hcomp i h1 (by omega)
      refine ctMap_lookup (List.mem_filter.2 ⟨hm, by simp [hi]⟩) (fun t' ht' => ?_)
      rw [hu t' (List.mem_filter.1 ht').1, hu t hm]
    have HMk : ∀ k t, M !! k = some t → k ≤ uint.nat (committedAfter σ.prev hs) ∧
        (uint.nat σ.prev.index' ≤ k → termAt σ.prev σ.ents (W64 (k : Int)) = some t) := by
      intro k t h
      obtain ⟨hm, hk⟩ := List.mem_filter.1 (ctMap_mem h)
      simp only [decide_eq_true_eq] at hk
      rw [Hc0] at hk
      exact ⟨hk, (Hct k t hm (by omega)).2⟩
    have HA0 : (sn.a0 : Int) < 2 ^ 64 := by
      rw [Ha0]; have := uint_nat_eq cv.Applied'; have := word.unsigned_range cv.Applied'
      have := word.unsigned_range σ.prev.index'; omega
    imod ownStorage_catchUp sn (interface.ok si) σ M
      (by rw [Ha0]; have := uint_nat_eq σ.fl; omega) HA0 Hdt HM $$ HSto with HSto
    let σ1 : StorState := { σ with fl := W64 (sn.a0 : Int), dt := M }
    have Hfl1 : uint.nat σ1.fl = sn.a0 := by
      show uint.nat (W64 (sn.a0 : Int)) = sn.a0
      have := uint_Z_W64 (sn.a0 : Int) (by omega) HA0
      have := uint_nat_eq (W64 (sn.a0 : Int)); omega
    -- the struct
    wp_apply wp_MakeProgressTracker as %tv0 %v0 ⟨%Htv0, Hv0, Hvotes, Hprs0⟩
    obtain ⟨Htv0mi, Htv0mb, Htv0arr, Htv0l, Htv0ln, Htv0al⟩ := Htv0
    wp_apply wp_newReadOnly _ (HpRO.trans Hros) as %ro Hro
    imod raftOwn_of_pts «$r0_ptr» _ $$ «$r0» with «$r0»
    ihave #Htlf := raftOwn_traceLogger _ _ $$ «$r0»

    -- (step 5) **traced: a fresh node; the bootstrap lines 0-2.** The capability, once the struct has
    -- its logger field
    ihave #Htlf' : «$r0_ptr».[raft, go!"traceLogger"] ↦□ cv.TraceLogger' $$ []
    · iExactEq Htlf; rw [HpTL]
    icases trCapStart_trCapB (some γd) γ «$r0_ptr» cv.ID' cv.TraceLogger' (bootCfg vs)
        (bootPhase vs cv.ID') bootNone $$ [Hcs0] with ⟨-, Hcap⟩
    · iframe Htlf' Hcs0
    -- the applied index and commit of a fresh node: the base's (`0`)
    have Hca : committedAfter σ.prev hs = σ.prev.index' := by
      unfold committedAfter; rw [ite_eq_left HhsE]
    have HbW : (W64 (uint.nat σ.prev.index' : Int)) = σ.prev.index' := by
      apply uint_Z_inj.1; rw [uint_Z_W64 _ (by omega) (by have := word.unsigned_range σ.prev.index'; omega)]
    have HA0C : sn.a0 ≤ uint.nat (committedAfter σ.prev hs) := by
      rw [Ha0]
      have := uint_nat_eq (committedAfter σ.prev hs); have := uint_nat_eq cv.Applied'
      rcases Happ with h | h
      · rw [h]; have : uint.nat (W64 0) = 0 := rfl; omega
      · omega
    have HAap : uint.nat σ.prev.index' = sn.a0 := by
      rw [Ha0, HAz]; have : uint.nat (W64 0) = 0 := rfl; omega
    have HCn := uint_nat_eq (committedAfter σ.prev hs)
    -- the log window closed at once: its commit and applied index are already the final ones
    ihave Hl : l ↦ ({ lv0 with committed' := committedAfter σ.prev hs, applied' := σ.prev.index', applying' := σ.prev.index' } : raftLog) $$ [Hl]
    · iExactEq Hl
      rw [Hca, ← HbW]
      cases lv0
      simp only at Hlcm Hlap Hlapg
      rw [Hlcm, Hlap, Hlapg]
    ihave HL := HLback $$ %σ1 %(committedAfter σ.prev hs) %σ.prev.index'
      %(by exact ⟨rfl, rfl, Hidx, Hpend, Hfr1, Hfr2, Hsg0, by omega, by omega, by omega, by omega, HMk⟩)
      Hl HisSto HSto
    let ls2 : LogState :=
      { prev := σ.prev, sents := σ.ents, uents := [], committed := committedAfter σ.prev hs,
        applied := σ.prev.index', snap := none, inprogress := ip, applying := σ.prev.index', unpersisted := [],
        stored := σ.ents, apsize := W64 0, apmax := cv'.MaxCommittedSizePerReady',
        storage := interface.ok si, ksn := [], sn := sn, fl := σ1.fl, sg := σ.sg,
        dtk := uint.nat (committedAfter σ.prev hs) }
    let s0 : NState :=
      { term := hs.Term', vote := hs.Vote', lead := W64 0, role := .follower, votes := ∅,
        outbox := [], stepfn := func.nil, ticking := false, progress := ∅, log := l, logst := ls2,
        prvals := ∅, prevote := cv.PreVote', gh := { sn := sn, tr := some γd }, isLearner := false,
        sdr := cv'.StepDownOnRemoval', cq := cv.CheckQuorum' }
    obtain ⟨HT, HV, HC⟩ := HhsE
    have Hli0 : plastIndex (toPState s0) = W64 0 := by
      simp only [plastIndex, plogLastIndexZ, toPState, s0, ls2, Hp0, He0, List.append_nil,
        List.length_nil]
      rfl
    have Hcm0 : s0.logst.committed = W64 0 := by show committedAfter σ.prev hs = _; rw [Hca, Hp0]
    iunfold raftOwn at «$r0»
    iNamed «$r0»
    ihave Hcore : ownRaftCore (GF := GF) «$r0_ptr» cv.ID' s0 $$ [H_Term H_Vote H_state H_raftLog HL]
    · unfold ownRaftCore
      isplitr
      · iExactEq H_id; rw [HpID]
      isplitl [H_Term]
      · iExactEq H_Term; rw [show s0.term = W64 0 from HT]; rfl
      isplitl [H_Vote]
      · iExactEq H_Vote; rw [show s0.vote = W64 0 from HV]; rfl
      isplitl [H_state]
      · iExactEq H_state; rfl
      iframe H_raftLog HL
    -- the empty configuration's maps (`MakeProgressTracker`'s), for the read view
    ihave Hv0 : v0 ↦$ (cfgM ∅ ∅).incoming $$ [Hv0]
    · iExactEq Hv0; rfl
    ihave Hcfg0 := ownCfgCC_intro tv0.Config' (DFrac.own 1) (cfgM ∅ ∅) v0 map.nil Htv0arr Htv0al
      $$ Hv0 [] [] []
    · ihave H := ownIdsetC_nil (GF := GF) (DFrac.own 1); iExactEq H; rfl
    · rw [Htv0l]; ihave H := ownIdsetC_nil (GF := GF) (DFrac.own 1); iExactEq H; rfl
    · rw [Htv0ln]; ihave H := ownIdsetC_nil (GF := GF) (DFrac.own 1); iExactEq H; rfl
    have Hsz0 : CfgSizeOk (cfgM ∅ ∅) := by
      constructor <;> simp [cfgM, GMap.size_empty]
    have Hn0 : (elements (cfgM ∅ ∅).incoming).length ≤ (elements (bootCfg vs).incoming).length := by
      show (elements (∅ : GSet w64)).length ≤ _; rw [show elements (∅ : GSet w64) = [] from List.eq_nil_of_length_eq_zero (by rw [GMap.length_elements, GMap.size_empty])]; exact Nat.zero_le _
    -- position 0: `traceInitState(r)`
    ihave Hgate := trCapB_hookGate_init (some γd) γ «$r0_ptr» cv.ID' (cfgM ∅ ∅) (bootCfg vs) s0
      cv.TraceLogger' (bootPhase vs cv.ID') bootNone (bootAt vs cv.ID' 0)
      (fun _ C cs P hP e he o ho => by
        obtain ⟨rfl, -, -⟩ := hP
        unfold bootNone at ho; subst ho
        show BootEvAt C cv.ID' 0 e
        exact nodeEvOf_bootEvAt0 C _ _ _ _ he (by show hs.Term' = _; rw [HT]) (by show hs.Vote' = _; rw [HV])
          Hcm0 Hli0 rfl)
      (fun e he => ⟨e, rfl, nodeEvOf_bootEvAt0 vs _ _ _ _ he (by show hs.Term' = _; rw [HT])
          (by show hs.Vote' = _; rw [HV]) Hcm0 Hli0 rfl⟩)
      (fun _ e he => nodeEvOf_okBoot _ _ _ _ e _ he (by show uint.nat hs.Term' < _; rw [HT]; decide)
          (by rw [Hcm0]; decide) (by rw [Hli0]; decide) Hn0)
      (fun h => by cases h)
      $$ [$Htlf' $Hcap]
    iunfold HookGate at Hgate
    imod Hgate with ⟨%tl0, #Htl0, Hfire⟩
    wp_apply wp_traceInitState «$r0_ptr» tl0 (some γd) (NodeEvOf (W64 0) cv.ID' s0 (cfgM ∅ ∅)) _
        (ownRaftReadT (cfgM ∅ ∅) «$r0_ptr» cv.ID' s0 tv0) $$ [Hcore H_trk Hcfg0 Hfire]
      as ⟨HR0, Hcap⟩
    · iframe Htl0 Hfire
      iapply (trOwn_some γd _).2
      iexists (cfgM ∅ ∅), cv.ID', s0, ownRaftReadT (cfgM ∅ ∅) «$r0_ptr» cv.ID' s0 tv0
      isplitl [Hcore H_trk Hcfg0]
      · iunfold ownRaftReadT; iframe Hcore H_trk Hcfg0; ipureintro; exact Hsz0
      isplitr
      · iapply raftReadLend_readT
      isplitr
      · ipureintro; exact ⟨rfl, fun _ h => h⟩
      iintro H; iexact H
    ihave HR0 := (trOwn_some γd _).1 $$ HR0
    iunfold ownRaftReadT at HR0
    icases HR0 with ⟨Hcore, H_trk, Hcfg0, -⟩
    icases ownCfgCC_elim _ _ _ $$ Hcfg0 with ⟨%vin, %vout, %Harr', Hv0, -, -, -, -⟩
    have Hvin : v0 = vin := by
      rw [Htv0arr] at Harr'
      injection Harr' with h1
    subst vin
    -- `lastID := r.raftLog.lastEntryID()`, on the closed log
    iunfold ownRaftCore at Hcore
    icases Hcore with ⟨-, H_Term, H_Vote, H_state, H_raftLog, HL⟩
    wp_auto
    wp_apply wp_raftLog_lastEntryID l ls2 $$ [$HL] as %lastID ⟨HL, -⟩
    -- `confchange.Restore` on the empty tracker: the empty conf state, so the tracker's own
    -- configuration back (`spec_empty`)
    have Hmi : 0 ≤ sint.Z tv0.MaxInflight' ∧ sint.Z tv0.MaxInflight' < 2 ^ 62 := by
      rw [Htv0mi, HpMI]; omega
    ipersist Hprs0
    ihave Hcsw := csPts_weaken $$ Hcs
    ihave Hv0 : v0 ↦$ (∅ : GMap w64 Unit) $$ [Hv0]
    · iExactEq Hv0; rfl
    try wp_auto
    wp_apply (confchange.Restore.spec_empty wp_confchange_Restore) ⟨tv0, lastID.index'⟩ cs csm
        DFrac.discard v0 Hv0e Hvo0 Hl0e Hln0 Hmi Htv0arr Htv0l Htv0ln Htv0al $$ [$Hcsw $Hv0 $Hprs0]
      as %cfgv %prsm ⟨%Hcp, Hcsw, Hv0, -⟩
    obtain ⟨Hcfgv, Hprsm⟩ := Hcp
    simp only at Hcfgv Hprsm
    subst Hcfgv Hprsm
    have Hm : restoreM csm.VotersOutgoing' csm.Voters' csm.Learners' csm.LearnersNext' csm.AutoLeave' =
        some (cfgState ∅ ∅) := by rw [Hvo0, Hv0e, Hl0e, Hln0]; rfl
    rw [Hm] at Hres
    injection Hres with Hres
    subst Hres
    ihave Hown := ownConfig_restore ∅ ∅ tv0.Config' tv0.Progress' ∅ v0 ∅ Htv0arr Htv0ln Htv0al
        (domSet_gset _) (by rw [GMap.map_union_empty]; exact domSet_empty_loc)
        (fun k hk => absurd hk (GMap.not_elem_of_empty _))
        (by rw [GMap.map_union_empty, GMap.size_empty]; decide)
      $$ Hv0 [] Hprs0 []
    · rw [Htv0l]; iapply ownIdsetC_nil
    · iapply BigSepM.bigSepM_empty.2; iempintro
    icases ownConfig_values $$ Hown with ⟨%pvs, Hown⟩
    ihave Hnew := ownConfigV_toC _ _ _ _ _ $$ Hown
    ihave Hnew : ownConfigC (GF := GF) (cfgState ∅ ∅).cfg tv0.Config' tv0.Progress' ∅ pvs $$ [Hnew]
    · iExactEq Hnew
      have Hd0 : domSet (∅ : GMap w64 Loc) \ (∅ : GSet w64) = (∅ : GSet w64) := by
        rw [domSet_empty_loc]
        apply GMap.set_eq; intro k
        rw [GMap.elem_of_difference]
        exact ⟨fun h => absurd h.1 h.2, fun h => absurd h (GMap.not_elem_of_empty _)⟩
      rw [Hd0]; rfl
    try wp_auto
    -- position 1: `assertConfStatesEquivalent(r.logger, cs, r.switchToConfig(cfg, trk))`, the hook's
    -- line read through the configuration it installs (the same maps)
    ihave #Hlgf : «$r0_ptr».[raft, go!"logger"] ↦□ interface.ok lok $$ [H_logger]
    · rw [← Hlok, ← HpLg]; iexact H_logger
    ihave Hcore : ownRaftCore (GF := GF) «$r0_ptr» cv.ID' s0 $$ [H_Term H_Vote H_state H_raftLog HL]
    · unfold ownRaftCore
      isplitr
      · iExactEq H_id; rw [HpID]
      iframe H_Term H_Vote H_state H_raftLog HL
    have Hel0 : elements (cfgState ∅ ∅).cfg.incoming = [] := elements_empty_nil
    ihave Hgate := trCapB_hookGate_ccBoot (some γd) γ «$r0_ptr» cv.ID' (cfgState ∅ ∅).cfg
      (cfgState ∅ ∅).cfg (bootCfg vs) s0 cv.TraceLogger' (bootPhase vs cv.ID') (bootAt vs cv.ID' 0)
      (bootAt vs cv.ID' 1)
      (fun _ C cs P hP e he o ho => by
        obtain ⟨rfl, -, -⟩ := hP
        obtain ⟨x, rfl, hx⟩ := ho
        exact bootNext_some C cv.ID' x e 0 hx
          (ccEvOf_bootEvAt1 C _ _ _ _ e he (by show hs.Term' = _; rw [HT]) Hel0))
      (fun e he => ⟨e, rfl, ccEvOf_bootEvAt1 vs _ _ _ _ e he (by show hs.Term' = _; rw [HT])
          Hel0⟩)
      (fun _ e he => ccEvOf_okBoot _ _ _ _ e _ he (by show uint.nat hs.Term' < _; rw [HT]; decide)
          (by rw [Hcm0]; decide) (by rw [Hli0]; decide) Hn0 Hn0)
      (fun h => by cases h)
      $$ [$Htlf' $Hcap]
    iunfold HookGate at Hgate
    imod Hgate with ⟨%tl1, #Htl1, Hfire⟩
    wp_apply wp_switchToConfig_wT wp_traceConfChangeEvent wp_ProgressTracker_ConfState (cfgState ∅ ∅).cfg
        «$r0_ptr» cv.ID' s0 lok false tv0 ∅ tv0.Config' tv0.Progress' ∅ pvs Hmi tl1 γd _ rfl rfl
      $$ [$H_trk $Htl1 $Hlgf $Hlg0 $H_isLearner $Hcore $Hvotes $Hnew $Hfire]
      as %cs2 %xs2 %os2 %ls2' %lns2 %bl ⟨H_trk, Htrk, H_isLearner, Hcore, Hcs2, %Hcs2p, Hcap⟩
    obtain ⟨Hperm, Hal2⟩ := confStateOk_perm csm (cfgState ∅ ∅) Hcsok Hm xs2 os2 ls2' lns2 Hcs2p
    icases ownTrackerC_progress_map _ _ _ $$ Htrk with ⟨-, %Hdom2, Htrk⟩
    ihave Hcs2v := csPts_weaken $$ Hcs2
    ihave Hcs2v : ownCSM cs2 (DFrac.own 1) (ConfStateM.mk xs2 ls2' os2 lns2 false) $$ [Hcs2v]
    · iExactEq Hcs2v; rfl
    wp_apply wp_assertConfStatesEquivalent _ cs cs2 csm
        (ConfStateM.mk xs2 ls2' os2 lns2 false) DFrac.discard (DFrac.own 1) Hperm
        (lists_bounded_of_ids csm.lists Hcsok.2.1 Hcsok.2.2.1 Hcsok.2.2.2.1 Hcsok.2.2.2.2.1 Hlen) Hal2
      $$ [$Hcsw $Hcs2v] as ⟨-, -⟩
    -- `if !IsEmptyHardState(hs)`: empty, skipped; `if c.Applied > 0`: `0`, skipped
    wp_apply wp_IsEmptyHardState hp hs $$ []
    · simp only [named]; iexact Hhsp
    rw [decide_eq_true (show hs.Term' = W64 0 ∧ hs.Vote' = W64 0 ∧ hs.Commit' = W64 0 from ⟨HT, HV, HC⟩)]
    wp_auto
    rw [HpAp, HAz]
    wp_auto
    iunfold ownRaftCore at Hcore
    icases Hcore with ⟨-, H_Term, H_Vote, H_state, H_raftLog, HL⟩
    -- the struct, sealed at `Restore`'s configuration
    ihave Hmisc : ownRaftMisc (GF := GF) slice.nil ro slice.nil ({} : RdState) $$ [Hro]
    · unfold ownRaftMisc
      simp only [named]
      isplitr
      · iunfold readStatesPts
        iexists []
        isplitr
        · iapply ownSlice_nil
        iapply BigSepL2.bigSepL2_nil.2; iempintro
      isplitr
      · iapply ownSliceCap_nil
      isplitl [Hro]
      · iexact Hro
      isplitr
      · iexists []
        isplitr
        · iapply ownSlice_nil
        iapply BigSepL2.bigSepL2_nil.2; iempintro
      iapply ownSliceCap_nil
    ihave Hnil1 : (slice.nil ↦* (([] : List QMsg).map QMsg.loc) : IProp GF) $$ []
    · rw [List.map_nil]; iapply ownSlice_nil
    ihave Hnil2 : (slice.nil ↦* (([] : List QMsg).map QMsg.loc) : IProp GF) $$ []
    · rw [List.map_nil]; iapply ownSlice_nil
    ihave Hcap1 := ownSliceCap_nil (V := Loc) (GF := GF)
    ihave Hcap2 := ownSliceCap_nil (V := Loc) (GF := GF)
    ihave Hob := outboxRel_nil (GF := GF)
    ihave #Hns0 := NsCap.off (GF := GF) (interface.ok si)
    ihave #Hsc0 : qSrcs (GF := GF) sn ([] ++ []) $$ []
    · rw [List.append_nil]; iapply qSrcs_nil
    let rv2 : raft :=
      { id' := cv'.ID', Term' := hs.Term', Vote' := hs.Vote', readStates' := slice.nil, raftLog' := l,
        maxMsgSize' := cv'.MaxSizePerMsg', maxUncommittedSize' := cv'.MaxUncommittedEntriesSize',
        trk' := { tv0 with Config' := tv0.Config', Progress' := tv0.Progress' }, state' := StateFollower,
        isLearner' := bl, msgs' := slice.nil, msgsAfterAppend' := slice.nil, lead' := W64 0,
        leadTransferee' := 0, pendingConfIndex' := 0,
        disableConfChangeValidation' := cv'.DisableConfChangeValidation', uncommittedSize' := 0,
        readOnly' := ro, electionElapsed' := 0, heartbeatElapsed' := 0, checkQuorum' := cv'.CheckQuorum',
        preVote' := cv'.PreVote', heartbeatTimeout' := cv'.HeartbeatTick',
        electionTimeout' := cv'.ElectionTick', randomizedElectionTimeout' := 0,
        disableProposalForwarding' := cv'.DisableProposalForwarding',
        stepDownOnRemoval' := cv'.StepDownOnRemoval', tick' := func.nil, step' := func.nil,
        logger' := cv'.Logger', pendingReadIndexMessages' := slice.nil,
        traceLogger' := cv'.TraceLogger' }
    ihave Hro : raftOwn (GF := GF) «$r0_ptr» rv2 $$ [H_Term H_Vote H_readStates H_raftLog H_maxMsgSize
        H_maxUncommittedSize H_trk H_state H_isLearner H_msgs H_msgsAfterAppend H_lead
        H_leadTransferee H_pendingConfIndex H_disableConfChangeValidation H_uncommittedSize
        H_readOnly H_electionElapsed H_heartbeatElapsed H_checkQuorum H_preVote H_heartbeatTimeout
        H_electionTimeout H_randomizedElectionTimeout H_disableProposalForwarding H_tick H_step
        H_pendingReadIndexMessages H_traceLogger]
    · unfold raftOwn
      simp only [named]
      iframe
      isplitr
      · iexact H_id
      isplitr
      · iexact H_checkQuorum
      isplitr
      · iexact H_stepDownOnRemoval
      isplitr
      · iexact H_logger
      iexact Htlf
    let s2 : NState :=
      { term := hs.Term', vote := hs.Vote', lead := W64 0, role := .follower, votes := ∅,
        outbox := [], stepfn := func.nil, ticking := false, progress := ∅, log := l, logst := ls2,
        prvals := pvs, prevote := cv.PreVote', gh := { sn := sn, tr := some γd }, isLearner := bl,
        sdr := cv'.StepDownOnRemoval', cq := cv.CheckQuorum' }
    ihave Htrk : ownTrackerC (GF := GF) (cfgState ∅ ∅).cfg rv2.trk' ⟨s2.votes, s2.progress, s2.prvals⟩ $$ [Htrk]
    · iExactEq Htrk; rfl
    ihave HL : ownRaftLog (GF := GF) rv2.raftLog' s2.logst $$ [HL]
    · iExactEq HL; rfl
    ihave Hphys := ownRaftPhysCV_intro (cfgState ∅ ∅).cfg (cfgState ∅ ∅).cfg.voters «$r0_ptr» cv.ID' s2 rv2 [] [] lok
      HpID rfl rfl rfl rfl rfl ⟨HpPV, fun h => absurd h (by simp only [s2]; decide)⟩
      (by simp only [rv2]; rw [HpDPF, Hdpf]) (by simp only [rv2]; rw [HpDCC, Hdccv])
      HpCQ
      rfl ⟨rfl, fun h => HvID h.symm⟩ rfl rfl HvID
      (by show 0 < sint.Z cv'.ElectionTick'; rw [HpET]; omega) (by simp only [rv2]; rw [HpLg, Hlok])
      trivial
      rfl (fun h => absurd h (by simp only [s2]; decide))
      ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
      (fun _ h => absurd h List.not_mem_nil) (Nat.zero_le _)
      ⟨fun h => absurd h Bool.false_ne_true,
        SnpOk.of_none rfl rfl rfl rfl, rfl⟩
      (fun h => absurd rfl h) (PrvalsOk.not_leader (by simp only [s2]; decide)) (LogNsOk.off rfl)
      (XfOk.nil (fun h => absurd h (by simp only [s2]; decide))) (LqOk.nil _ _)
      $$ Hro Hlg0 Htrk HL Hnil1 Hcap1 Hnil2 Hcap2 Hmisc Hob Hns0 Hsc0
    try wp_auto
    -- `r.becomeFollower(r.Term, None)`
    -- position 2: `r.becomeFollower(r.Term, None)`, a bootstrap line (`b = false`)
    have Ht2 : s2.term = W64 0 := by show hs.Term' = _; rw [HT]
    have Hbf2 : ∀ e, NodeEvOf (W64 2) cv.ID' (becomeFollower s2 s2.term (W64 0)) (cfgState ∅ ∅).cfg e →
        BootEvAt vs cv.ID' 2 e := fun e he =>
      (nodeEvOf_bootEvAtBF _ _ _ _ _ he).1 Ht2
    ihave Hcap : trCapB (GF := GF) s2.gh.tr γ «$r0_ptr» cv.ID' (bootCfg vs) false (bootPhase vs cv.ID')
        (bootAt vs cv.ID' 1) $$ [Hcap]
    · iExactEq Hcap; rfl
    have Hpl2 : plastIndex (toPState (becomeFollower s2 s2.term (W64 0))) = W64 0 := by
      rw [← Hli0]; rfl
    try wp_auto
    wp_apply raft.wp_load_TermC $$ Hphys as Hphys
    try wp_auto
    ihave Hphys : ownRaftPhysCV (GF := GF) (cfgM ∅ ∅) (cfgM ∅ ∅).voters «$r0_ptr» cv.ID' s2 $$ [Hphys]
    · iExactEq Hphys; rfl
    wp_apply (raft.becomeFollower.traced wp_raft_becomeFollower (cfgM ∅ ∅) (V := (cfgM ∅ ∅).voters) (bootCfg vs) «$r0_ptr»
        cv.ID' s2 s2.term (W64 0) γ false (bootPhase vs cv.ID') (bootPhase vs cv.ID') (bootAt vs cv.ID' 1)
        (bootAt vs cv.ID' 2) (Int.le_refl _) (fun _ => rfl) (fun h => by cases h) (fun _ => rfl)
        (fun h => by cases h)
        (fun _ C cs P hP => ⟨hP, fun _ e he o ho => by
          obtain ⟨rfl, -, -⟩ := hP
          obtain ⟨x, rfl, hx⟩ := ho
          exact bootNext_some C cv.ID' x e 1 hx (Hbf2 e he)⟩)
        (fun e he => ⟨e, rfl, Hbf2 e he⟩)
        (fun _ => ⟨(fun h => by cases h), fun _ e he => nodeEvOf_okBoot _ _ _ _ e _ he
            (by show uint.nat s2.term < _; rw [Ht2]; show uint.nat (W64 0) < 2 ^ 61; decide)
            (by show uint.nat (committedAfter σ.prev hs) < _; rw [Hca, Hp0]; show uint.nat (W64 0) < 2 ^ 61; decide)
            (by rw [Hpl2]; decide) Hn0⟩))
      $$ [$Hphys $Hcap]
      as %pvs3 ⟨Hphys, Hcap⟩
    · simp only [trOwn]; iempintro
    let s3 : NState := { becomeFollower s2 s2.term (W64 0) with prvals := pvs3 }
    -- `r.trk.VoterNodes()`
    icases ownRaftPhysC_tracker_same _ _ _ s3 $$ Hphys with ⟨%tv3, Htrkf, Htrk3, Htrkback⟩
    wp_apply wp_ProgressTracker_VoterNodes $$ [$Htrkf $Htrk3] as %nsl %nxs ⟨Htrkf, Htrk3, Hnsl, %Hnxs⟩
    ihave Hphys := Htrkback $$ %tv3 Htrkf Htrk3
    -- the log line's `nodesStrs` loop; what it builds is never read
    ihave IH : iprop(∃ (k x : w64) (sl' : GoSlice) (strs : List GoString),
        "i" ∷ i_ptr ↦ k ∗ "n" ∷ n_ptr ↦ x ∗ "nodesStrs" ∷ nodesStrs_ptr ↦ sl' ∗
        "Hstrs" ∷ sl' ↦* strs ∗
        "Hstrs_cap" ∷ ownSliceCap GoString sl' (DFrac.own 1) ∗
        "Hnsl" ∷ nsl ↦* nxs ∗
        "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (nxs.length : Int)⌝) $$ [i n nodesStrs Hnsl]
    · iexists W64 0, _, slice.nil, []
      iframe i n nodesStrs Hnsl
      isplitr
      · iapply ownSlice_nil
      isplitr
      · iapply ownSliceCap_nil
      ipureintro; constructor <;> word
    wp_for IH
    wp_if_destruct
    · ihave %Hnl := ownSlice_len $$ Hnsl
      have Hlt : (sint.Z k).toNat < nxs.length := by word
      list_elem nxs (sint.Z k).toNat as e
      rw [ite_eq_left (show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z nsl.len by word)]
      wp_apply wp_load_slice_index nsl (sint.Z k) nxs (DFrac.own 1) e Hk.1 $$ [Hnsl] as Hnsl
      · iframe; ipureintro; exact He_lookup
      wp_apply wp_slice_literal
      try (isplitr; (ipureintro; rfl))
      iintro %sla ⟨Hargs, -⟩
      wp_auto
      wp_apply wp_fmt_Sprintf $$ [$Hargs] as %str Hargs
      · ipureintro
        exact _root_.Perennial.fmt.ArgsWf.cons_int _ _ _ (.uint64 _) _root_.Perennial.fmt.ArgsWf.nil
      wp_apply wp_slice_literal
      try (isplitr; (ipureintro; rfl))
      iintro %sl2 ⟨Hsl2, -⟩
      wp_auto
      wp_apply wp_slice_append $$ [$Hstrs $Hstrs_cap $Hsl2] as %sl3 ⟨Hstrs, Hstrs_cap, -⟩
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro; constructor <;> word
    -- the log line: `r.id`, `strings.Join(nodesStrs, ",")`, `r.Term`, then
    -- `r.raftLog.committed` and `r.raftLog.applied` through the log
    wp_apply wp_strings_Join $$ [$Hstrs] as %joined Hstrs
    wp_apply raft.wp_load_TermC $$ Hphys as Hphys
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_same _ _ _ s3 $$ Hphys with ⟨Hlog3, Hlogback⟩
    icases ownRaftLog_struct _ _ $$ Hlog3 with ⟨%lv3, Hl3, -, Hl3back⟩
    wp_auto
    ihave Hlog3 := Hl3back $$ Hl3
    ihave Hphys := Hlogback $$ Hlog3
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_same _ _ _ s3 $$ Hphys with ⟨Hlog3, Hlogback⟩
    icases ownRaftLog_struct _ _ $$ Hlog3 with ⟨%lv4, Hl3, -, Hl3back⟩
    wp_auto
    ihave Hlog3 := Hl3back $$ Hl3
    ihave Hphys := Hlogback $$ Hlog3
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    try iintro %_ ⟨_, -⟩
    try wp_auto
    wp_apply Logger.wp_logf lok _ _ _ (by decide) $$ Hlg0
    try wp_auto
    iapply HΦ $$ %«$r0_ptr» %s3 %cv'
    ihave Hphys : ownRaftPhysC (GF := GF) (cfgState ∅ ∅).cfg «$r0_ptr» cv.ID' s3 $$ [Hphys]
    · iExactEq Hphys; rfl
    iframe HR Hphys Hc
    isplitr
    · ipureintro; exact HpAW
    -- (step 5) the storage's no-compaction handed on, the capability after position 2
    iframe Hnc Hcap
    -- `becomeFollower(r.Term, None)` keeps the term, so `reset` keeps the
    -- vote: the state is the persisted `HardState`'s
    ipureintro
    refine ⟨⟨rfl, rfl⟩, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, HpSDR, ?_, rfl⟩
    · show (if s2.term = s2.term then s2.vote else W64 0) = hs.Vote'
      simp only [↓reduceIte]
      rfl
    · show σ.prev.index' = w64Max σ.prev.index' σ.prev.index'
      unfold w64Max; split <;> rfl
    · show domSet (∅ : GMap w64 Loc) = domSet (cfgState ∅ ∅).prs
      apply GMap.set_eq; intro k
      rw [domSet_empty_loc, GMap.elem_of_dom']
      simp only [cfgState]
      rw [cfgFlags_mem]
      simp [GMap.not_elem_of_empty]

end proof

end EtcdGrove
end Perennial
