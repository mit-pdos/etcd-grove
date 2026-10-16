/-
`stepLeader`'s `MsgProp` branch (split out of `stepLeader.lean` on 2026-10-13, with the
conf-change loop of reconfiguration stage D): `wp_stepLeader_prop`.
-/
module

public import Raft37.Spec.go_etcd_io.raft.v3.stepLeader
public import Raft37.Proof.go_etcd_io.raft.v3.LemmasStepR
public import Raft37.Spec.go_etcd_io.raft.v3.raft__bcastAppend
public import Raft37.Spec.go_etcd_io.raft.v3.raft__appendEntry
public import Raft37.Spec.go_etcd_io.raft.v3.raftLog__lastIndex
public import Spec.google_golang_org.protobuf.proto.UnmarshalConfChange
public import Spec.google_golang_org.protobuf.proto.UnmarshalConfChangeV2
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.ConfChange__AsV2
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__AsV2
public import Raft37.Spec.fmt.Sprintf
public import Raft37.Spec.go_etcd_io.raft.v3.traceChangeConfEvent
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetType
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetData
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.EntryType__Enum
public import Raft37.Spec.go_etcd_io.raft.v3.DescribeConfChange

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

variable (c : CfgM)

/-- The loop's batch with entry `n` overwritten (2026-10-13). -/
private theorem list_set_mid {A : Type} (P l : List A) (n : Nat) (x e : A) (hP : P.length = n)
    (he : l[n]? = some e) : (P ++ l.drop n).set n x = P ++ x :: l.drop (n + 1) := by
  rw [list_drop_S l n e he]
  subst hP
  clear he
  generalize l.drop (P.length + 1) = T
  induction P with
  | nil => rfl
  | cons y P ih =>
    simp only [List.cons_append, List.length_cons, List.set_cons_succ]
    exact congrArg (y :: ·) ih

/-- A list written back at the element it holds. -/
private theorem list_set_self {A : Type} (l : List A) (i : Int) (x : A)
    (H : l[i.toNat]? = some x) : l.set i.toNat x = l := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 H
  rw [← hget]; exact List.set_getElem_self hlt


set_option maxHeartbeats 1600000 in
/-- **`MsgProp`**

`len(m.Entries) == 0` is false (`ents ≠ []`); `r.trk.Progress[r.id]` is a hit
(`id ∈ c.voters`, and a `Progress` pointer is never nil); a leader transfer in progress drops
the proposal. Then (2026-10-13, reconfiguration stage D) the conf-change loop: entry `n`
of the batch -- the loop's state is the batch with the first `n` entries as the loop
left them (`leaderPropConf` of the first `n`), and `pendingConfIndex` as it left it --
is decoded (`Unmarshal`, from `ccEntsOk`'s bytes, never failing) when it is a conf change,
and checked: refused (overwritten with `pb.Entry{Type: EntryNormal}`) when a conf change
is pending or its `wantsLeaveJoint` (an empty `ConfChangeV2`) disagrees with `alreadyJoint`,
else accepted (`pendingConfIndex` moved). `alreadyJoint` is `len(r.trk.Config.Voters[1]) >
0`, `c.joint` (since 2026-10-14, reconfiguration stage A3: until then the outgoing half was
`nil`); `disableConfChangeValidation` is false (`ownRaftPhysC`). Then `appendEntry`
stamps the loop's batch and, if it accepts it, `bcastAppend`.

raft v3.7 (2026-10-15, stage R4): the message is `Step`'s `msgIn` with the entry pointers owned;
its `Entries` field is held apart (`msgPtsC_acc_entries`) and every `m.GetEntries()` is read
through the getter's body (`wp_Message_GetEntries_field`), so the range loop's slice and the
body's calls are one slice `es0`; an entry is read by `Entry.GetType`/`GetData` (its bytes
decoded by the `proto.UnmarshalConfChange(V2)` axioms over `ccEntOk`), a refused change's slot
gets a fresh `&pb.Entry{Type: EntryNormal.Enum()}`, frozen (`entRO_normal_of_struct`); the
refusal's log line formats the change by `DescribeConfChange` (a trust-boundary axiom);
`appendEntry` takes the slice as `entsPts` and clones it. -/
theorem wp_stepLeader_prop
    (wp_raft_bcastAppend : raft.bcastAppend.spec (GF := GF) (hG := hG))
    (wp_raft_appendEntry : raft.appendEntry.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_UnmarshalConfChange : proto.UnmarshalConfChange.spec (GF := GF) (hG := hG))
    (wp_UnmarshalConfChangeV2 : proto.UnmarshalConfChangeV2.spec (GF := GF) (hG := hG))
    (wp_ConfChange_AsV2 : raftpb.ConfChange.AsV2.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_AsV2 : raftpb.ConfChangeV2.AsV2.spec (GF := GF) (hG := hG))
    (wp_fmt_Sprintf : fmt.Sprintf.spec (GF := GF) (hG := hG))
    (wp_traceChangeConfEvent : traceChangeConfEvent.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_Entry_GetType : raftpb.Entry.GetType.spec (GF := GF) (hG := hG))
    (wp_Entry_GetData : raftpb.Entry.GetData.spec (GF := GF) (hG := hG))
    (wp_EntryType_Enum : raftpb.EntryType.Enum.spec (GF := GF) (hG := hG))
    (wp_DescribeConfChange : DescribeConfChange.spec (GF := GF) (hG := hG))
    (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM) (ents : List EntryM)
    (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) (cs : List (Option CCMsg))
    (Hty : m.Type' = MsgProp) (Hid : id ∈ c.voters) (Hne : ents ≠ [])
    (Hsmall : (ents.length : Int) < 2^61) (Hnz : s.term ≠ W64 0) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s ∗
        msgIn ml (DFrac.own 1) ⟨m, ents, sn, ctx, rs⟩ ∗ ccEntsOk ents cs }}
      (App (App (Val #(functions stepLeader [])) (Val #r)) (Val #ml))
    {{ (err : GoInterface) (s' : NState) (dropped : Bool), RET #err;
        ownRaftPhysCV c c.voters r id s' ∗
        ⌜LeaderProposeResult id s ents dropped s' c.joint⌝ ∗
        (if dropped then globalAddr ErrProposalDropped ↦□ err
         else ⌜err = interface.nil⌝) }} := by
  wp_start as ⟨Hphys, Hm, #Hcc⟩
  ihave %Hct := ccEntsOk_types ents cs $$ Hcc
  have Hcslen : cs.length = ents.length := (List.Forall₂.length_eq Hct).symm
  iunfold ccEntsOk at Hcc
  ihave #Hinit := isInitialized_access $$ Hpkg
  unfold isInitialized
  icases Hinit with ⟨%e1, %e2, %e3, %e4, %errPropDropped, %gr, %_, %_, %_, %_, #Hinit⟩
  iNamed Hinit
  wp_auto
  wp_apply wp_GetType.1 ml _ _ _ _ $$ [$Hm] as Hm
  simp only [Hty, MsgProp]
  wp_auto
  -- the `Entries` field held apart: every `m.GetEntries()` below is this slice
  icases msgPtsC_acc_entries ml _ _ _ _ $$ Hm with ⟨%es0, %els0, %Hmnn, HEs, Hes, #Hents, -, -⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hes
  ihave %Hl2 := BigSepL2.bigSepL2_length $$ Hents
  wp_apply wp_Message_GetEntries_field ml _ es0 Hmnn $$ [$HEs] as HEs
  wp_if_destruct
  · exfalso
    apply Hne
    apply List.eq_nil_of_length_eq_zero
    rw [← Hl2, Hl.1, Hif]; rfl
  wp_apply raft.wp_load_idC $$ Hphys as Hphys
  icases ownRaftPhysC_tracker_same c r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  icases ownTrackerC_progress_map c tv _ $$ Htrk with ⟨#Hprs, %Hdom, Htrk⟩
  icases ownTrackerC_prvals_dom c tv _ $$ Htrk with ⟨%Hpdom, Htrk⟩
  dsimp only at Hdom Hpdom
  wp_auto
  ihave Hphys := Hback $$ Htrkf Htrk
  wp_apply wp_map_lookup1 go.uint64 (go.GoType.PointerType tracker.Progress.ty) _ s.progress
    id _ $$ Hprs with -
  obtain ⟨pr, Hlk⟩ : ∃ pr, s.progress !! id = some pr := by
    rw [← GMap.elem_of_dom, Hdom]; exact (GMap.elem_of_subseteq _ _).1 (voters_sub_ids c) _ Hid
  obtain ⟨p, Hpvs⟩ : ∃ p, s.prvals !! id = some p := by
    rw [← GMap.elem_of_dom, Hpdom, GMap.elem_of_dom]; exact ⟨pr, Hlk⟩
  icases ownRaftPhysC_pr c r id s id pr p $$ Hphys %Hlk %Hpvs with ⟨Hpa, Hpback⟩
  iNamed Hpa
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hpv
  ihave Hphys := Hpback $$ [Hpv Hinfl]
  · iapply ownProgress_intro $$ Hpv Hinfl %Habs
  rw [Hlk]
  simp only [Option.getD_some]
  wp_if_destruct
  · exact absurd rfl Hnn
  wp_apply raft.wp_load_leadTransfereeC $$ Hphys as Hphys
  -- (2026-10-13) a leader transfer in progress drops the proposal
  by_cases Hlt : s.lt = W64 0
  rotate_left
  · rw [decide_eq_false Hlt]
    wp_auto
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    wp_apply raft.wp_load_TermC $$ Hphys as Hphys
    wp_apply raft.wp_load_leadTransfereeC $$ Hphys as Hphys
    wp_raft_logC
    iapply HΦ $$ %errPropDropped %s %true
    iframe Hphys
    isplitr
    · ipureintro
      exact ⟨cs, Hct, by simp⟩
    simp only [↓reduceIte]
    iexact ErrPropDropped
  rw [decide_eq_true Hlt]
  wp_auto
  wp_apply wp_Message_GetEntries_field ml _ es0 Hmnn $$ [$HEs] as HEs
  rename_i gi_ptr
  irename : (gi_ptr ↦ zero_val w64 : IProp GF) => Hgi
  -- the loop's state after `n` entries
  let lpc : Nat → List EntryM × w64 := fun n =>
    propConf s.logst.applied (logLast s.logst) s.pci (ents.take n) (cs.take n) c.joint
  have Hlpc_len : ∀ n, n ≤ ents.length → (lpc n).1.length = n := by
    intro n hn
    simp only [lpc]
    rw [propConf_length]; simp only [List.length_take]; omega
  ihave IH : iprop(∃ (n k : w64) (els : List Loc),
      "Hj" ∷ i_ptr ↦ n ∗
      "Hgi" ∷ gi_ptr ↦ k ∗
      "Hes" ∷ es0 ↦* els ∗
      "#Hents" ∷ ([∗list] p;e ∈ els;((lpc (sint.nat n)).1 ++ ents.drop (sint.nat n)), entRO p e) ∗
      "HEs" ∷ ml.[raftpb.Message, go!"Entries"] ↦ es0 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id { s with pci := (lpc (sint.nat n)).2 } ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ents.length : Int)⌝) $$ [i Hgi Hes HEs Hphys]
  · iexists W64 0, zero_val w64, els0
    simp only [lpc, show sint.nat (W64 0) = 0 from rfl, propConf_take_zero, List.nil_append,
      List.drop_zero]
    iframe
    iframe Hents
    ipureintro
    word
  wp_for IH
  ihave %Hl' := ownSlice_len _ _ _ $$ Hes
  ihave %Hlen' := BigSepL2.bigSepL2_length $$ Hents
  have Hcurlen : ((lpc (sint.nat n)).1 ++ ents.drop (sint.nat n)).length = ents.length := by
    rw [List.length_append, Hlpc_len _ (by word), List.length_drop]; word
  wp_if_destruct
  · -- entry `n`
    have Hnlt : sint.nat n < ents.length := by
      have := Hl.1; rw [Hl2] at this; word
    obtain ⟨e, He_lookup⟩ : ∃ e, ents[sint.nat n]? = some e :=
      ⟨_, List.getElem?_eq_getElem Hnlt⟩
    obtain ⟨o, Ho_lookup⟩ : ∃ o, cs[sint.nat n]? = some o :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have Hlpcn := Hlpc_len (sint.nat n) (by word)
    have Hcur_lookup : ((lpc (sint.nat n)).1 ++ ents.drop (sint.nat n))[sint.nat n]? =
        some e := by
      rw [List.getElem?_append_right (Nat.le_of_eq Hlpcn), Hlpcn, Nat.sub_self,
        List.getElem?_drop, Nat.add_zero, He_lookup]
    icases entsBig_lookup _ _ (sint.nat n) e Hcur_lookup $$ Hents with ⟨%l0, %Hl0, #He⟩
    have Hl0' : els[(sint.Z n).toNat]? = some l0 := by
      rw [show (sint.Z n).toNat = sint.nat n by word]; exact Hl0
    have Hes0len : sint.Z n < sint.Z es0.len := by
      have := Hl'.1; rw [Hlen', Hcurlen] at this; word
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hn.1, Hes0len⟩)]
    wp_apply wp_load_slice_index es0 (sint.Z n) els (DFrac.own 1) l0 Hn.1 $$ [Hes] as Hes
    · iframe; ipureintro; exact Hl0'
    wp_apply wp_Message_GetEntries_field ml _ es0 Hmnn $$ [$HEs] as HEs
    ihave #Heo := BigSepL2.bigSepL2_lookup (Φ := fun _ e o => ccEntOk (GF := GF) e o)
      He_lookup Ho_lookup $$ Hcc
    have Hstep := propConf_take_succ c.joint s.logst.applied (logLast s.logst) s.pci ents cs
      (sint.nat n) e o He_lookup Ho_lookup
    have Hnext : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    have Hcur_lookup' : ((lpc (sint.nat n)).1 ++ ents.drop (sint.nat n))[(sint.Z n).toNat]? =
        some e := by rw [show (sint.Z n).toNat = sint.nat n by word]; exact Hcur_lookup
    -- the next state, when the loop keeps entry `n` or overwrites it
    have Hkeep : ∀ p', propConfStep c.joint s.logst.applied (logLast s.logst) (lpc (sint.nat n)) (e, o) =
        ((lpc (sint.nat n)).1 ++ [e], p') →
        (lpc (sint.nat (n + W64 1))).1 ++ ents.drop (sint.nat (n + W64 1)) =
          (lpc (sint.nat n)).1 ++ ents.drop (sint.nat n) ∧ (lpc (sint.nat (n + W64 1))).2 = p' := by
      intro p' Hp
      simp only [lpc, Hnext, Hstep] at Hp ⊢
      rw [Hp, list_drop_S ents _ e He_lookup]
      simp
    have Hzero : ∀ p', propConfStep c.joint s.logst.applied (logLast s.logst) (lpc (sint.nat n)) (e, o) =
        ((lpc (sint.nat n)).1 ++ [zero_val EntryM], p') →
        (lpc (sint.nat (n + W64 1))).1 ++ ents.drop (sint.nat (n + W64 1)) =
          ((lpc (sint.nat n)).1 ++ ents.drop (sint.nat n)).set (sint.Z n).toNat
            (zero_val EntryM) ∧ (lpc (sint.nat (n + W64 1))).2 = p' := by
      intro p' Hp
      simp only [lpc, Hnext, Hstep] at Hp ⊢
      rw [Hp, show (sint.Z n).toNat = sint.nat n by word,
        list_set_mid _ ents (sint.nat n) _ e (by simpa [lpc] using Hlpcn) He_lookup]
      simp
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hn.1, Hes0len⟩)]
    wp_apply wp_load_slice_index es0 (sint.Z n) els (DFrac.own 1) l0 Hn.1 $$ [Hes] as Hes
    · iframe; ipureintro; exact Hl0'
    wp_apply wp_Entry_GetType.1 l0 DFrac.discard e $$ [$He] as -
    rcases o with _ | (c1 | c2)
    · -- not a conf change: `cc` stays `nil`
      iunfold ccEntOk at Heo
      icases Heo with %Hnc
      have H1 : e.Type' ≠ W32 1 := fun h => Hnc (Or.inl h)
      have H2 : e.Type' ≠ W32 2 := fun h => Hnc (Or.inr h)
      rw [decide_eq_false (by intro h; apply H1; rw [h])]
      wp_auto
      wp_apply wp_Entry_GetType.1 l0 DFrac.discard e $$ [$He] as -
      rw [decide_eq_false (by intro h; apply H2; rw [h])]
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, n, els
      have Hcur' : (lpc (sint.nat (n + W64 1))).1 ++ ents.drop (sint.nat (n + W64 1)) =
          (lpc (sint.nat n)).1 ++ ents.drop (sint.nat n) := by
        simp only [lpc, Hnext, Hstep, propConfStep, List.append_assoc, List.singleton_append]
        rw [list_drop_S ents _ e He_lookup]
      rw [Hcur']
      have Hpci' : (lpc (sint.nat (n + W64 1))).2 = (lpc (sint.nat n)).2 := by
        simp only [lpc, Hnext, Hstep, propConfStep]
      rw [Hpci']
      iframe
      iframe Hents
      ipureintro
      word
    · -- a `ConfChange`
      iunfold ccEntOk at Heo
      icases Heo with ⟨%H1, %Hdec⟩
      rw [decide_eq_true (by rw [H1])]
      wp_auto
      wp_apply wp_Entry_GetData.1 l0 DFrac.discard e $$ [$He] as %ds ⟨#Hds, -⟩
      wp_apply wp_UnmarshalConfChange ds e.Data' DFrac.discard _ _ $$ [$Hds $«$r0»] as %err ⟨-, Hm⟩
      rw [Hdec]
      icases Hm with ⟨%Herr, Hown⟩
      subst Herr
      wp_auto
      -- `alreadyPending := r.pendingConfIndex > r.raftLog.applied`
      wp_apply raft.wp_load_pendingConfIndexC $$ Hphys as Hphys
      wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
      icases ownRaftPhysC_log_same c r id _ $$ Hphys with ⟨Hlog, Hback⟩
      icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
      wp_auto
      ihave Hlog := Hlb $$ Hl
      ihave Hphys := Hback $$ Hlog
      -- `alreadyJoint := len(r.trk.Config.Voters[1]) > 0`: `c.joint` (2026-10-14)
      icases ownRaftPhysC_tracker_same c r id _ $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
      icases ownTrackerC_halves c tv _ $$ Htrk with ⟨%vin, %vout, %Harr, %Hcsz, Hv0, Hv1, Htrkback⟩
      have Hset1 : array.mk 2 (tv.Config'.Voters'.arr.set (sint.Z (W64 1)).toNat vout) =
          tv.Config'.Voters' := by
        generalize tv.Config'.Voters' = a at Harr ⊢
        cases a
        simp only at Harr
        subst Harr
        rfl
      icases (Access.access
          (A := r.[raft, go!"trk"].[tracker.ProgressTracker, go!"Config"].[tracker.Config, go!"Voters"]
            ↦ tv.Config'.Voters')
          (A' := r.[raft, go!"trk"].[tracker.ProgressTracker, go!"Config"].[tracker.Config, go!"Voters"]
            ↦ tv.Config'.Voters')
          (P := r.[raft, go!"trk"] ↦ tv)) $$ Htrkf with ⟨Hvf, Htrkfback⟩
      icases array_acc _ (sint.Z (W64 1)) _ _ _ vout (by decide) (by rw [Harr]; rfl)
        $$ Hvf with ⟨Hc1, Hcback⟩
      wp_auto
      ihave Hvf := Hcback $$ Hc1
      rw [Hset1]
      ihave Htrkf := Htrkfback $$ Hvf
      wp_apply wp_idset_len $$ Hv1 as ⟨Hv1, %Hlt1⟩
      have Hjd : decide (sint.Z (W64 0) < sint.Z (W64 (GMap.size c.outgoing : Int))) = c.joint := by
        unfold CfgM.joint
        apply decide_eq_decide.2
        have : sint.Z (W64 (GMap.size c.outgoing : Int)) = GMap.size c.outgoing := by word
        rw [this]; simp
      rw [Hjd]
      ihave Htrk := Htrkback $$ Hv0 Hv1
      ihave Hphys := Hback $$ %tv Htrkf Htrk
      -- `wantsLeaveJoint := len(cc.AsV2().Changes) == 0`: a `ConfChange` has one change
      wp_apply wp_ConfChange_AsV2 _ _ _ $$ [$Hown] as %v2 ⟨Hown, Hv2⟩
      icases ownCCV2_changes _ _ _ $$ Hv2 with ⟨%chs, HCh, %Hchl, -⟩
      try wp_auto
      have Happ : lv.applied' = s.logst.applied := Hlv.2
      wp_if_destruct
      · -- a conf change is pending: refused
        have Hpend : uint.Z s.logst.applied < uint.Z (lpc (sint.nat n)).2 := by
          rw [← Happ]; exact Hif
        wp_apply raft.wp_load_pendingConfIndexC $$ Hphys as Hphys
        wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
        icases ownRaftPhysC_log_same c r id _ $$ Hphys with ⟨Hlog, Hback⟩
        icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv2, Hl, %Hlv2, Hlb⟩
        wp_auto
        ihave Hlog := Hlb $$ Hl
        ihave Hphys := Hback $$ Hlog
        wp_apply wp_slice_literal (V := GoInterface)
          [interface.mkOk go.uint64 #(lpc (sint.nat n)).2, interface.mkOk go.uint64 #lv2.applied']
        isplitr
        · ipureintro; rfl
        iintro %sla Hargs0
        icases Hargs0 with ⟨Hargs, -⟩
        wp_auto
        wp_apply wp_fmt_Sprintf $$ [$Hargs] as %str ⟨Hargs, %Hout⟩
        · ipureintro
          exact _root_.Perennial.fmt.ArgsWf.cons_int _ _ _ (.uint64 _)
            (_root_.Perennial.fmt.ArgsWf.cons_int _ _ _ (.uint64 _) _root_.Perennial.fmt.ArgsWf.nil)
        have Hstr : str ≠ [] := by
          obtain ⟨o', rfl, -⟩ := _root_.Perennial.fmt.SprintfOut.byte_inv (by decide) Hout
          simp
        simp only [decide_eq_false Hstr, Bool.not_false]
        wp_auto
        have Hstep0 : propConfStep c.joint s.logst.applied (logLast s.logst) (lpc (sint.nat n))
            (e, some (.v1 c1)) = ((lpc (sint.nat n)).1 ++ [zero_val EntryM], (lpc (sint.nat n)).2) := by
          unfold propConfStep
          simp only [Hpend, _root_.true_or, ↓reduceIte]
        wp_apply raft.wp_load_disableConfChangeValidationC $$ Hphys as Hphys
        wp_apply raft.wp_load_idC $$ Hphys as Hphys
        first
        | wp_apply wp_DescribeConfChange.1 _ _ _ $$ [$Hown] as %str Hown
        | (ihave Hown := Hownback $$ HCh
           wp_apply wp_DescribeConfChange.2 _ _ _ $$ [$Hown] as %str Hown)
        icases ownRaftPhysC_tracker_same c r id _ $$ Hphys with ⟨%tv2, Htrkf, Htrk, Hback⟩
        icases (Access.access
            (A := r.[raft, go!"trk"].[tracker.ProgressTracker, go!"Config"] ↦ tv2.Config')
            (A' := r.[raft, go!"trk"].[tracker.ProgressTracker, go!"Config"] ↦ tv2.Config')
            (P := r.[raft, go!"trk"] ↦ tv2)) $$ Htrkf with ⟨Hcf, Htrkfback⟩
        wp_auto
        ihave Htrkf := Htrkfback $$ Hcf
        ihave Hphys := Hback $$ %tv2 Htrkf Htrk
        wp_raft_logC
        rw [show raftpb.EntryNormal = #(W32 0 : raftpb.EntryType) from rfl]
        haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
        wp_apply wp_EntryType_Enum (W32 0) as %pty Hpty
        imod entRO_normal_of_struct _ pty (normalEntryV pty) ⊤ rfl rfl rfl rfl rfl $$ [«$r0» Hpty] with #Hnew
        · iframe
        wp_apply wp_Message_GetEntries_field ml _ es0 Hmnn $$ [$HEs] as HEs
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hn.1, Hes0len⟩)]
        wp_apply wp_store_slice_index es0 (sint.Z n) els _ $$ [$Hes] as Hes
        · ipureintro; refine ⟨Hn.1, ?_⟩; rw [Hlen', Hcurlen]; word
        icases (BigSepL2.bigSepL2_insert_acc (Φ := fun _ p e => entRO (GF := GF) p e) Hl0' Hcur_lookup') $$ Hents with ⟨-, Hset⟩
        ihave Hents' := Hset $$ %_ %(zero_val EntryM) Hnew
        obtain ⟨Hcur', Hpci'⟩ := Hzero _ Hstep0
        wp_for_post
        iframe
        iexists n + W64 1, n, _
        rw [Hcur', Hpci']
        iframe
        iframe Hents'
        ipureintro; word
      · -- no conf change pending, one change (`wantsLeaveJoint` false)
        have Hnp : ¬ uint.Z s.logst.applied < uint.Z (lpc (sint.nat n)).2 := by
          rw [← Happ]; exact Hif
        have Hch0 : chs.len ≠ W64 0 := by
          intro h; have h1 := Hchl.1; rw [h] at h1; simp [CCV1M.asV2, sint.nat] at h1
        rw [decide_eq_false Hch0]
        try wp_auto
        rcases Bool.eq_false_or_eq_true c.joint with Hjv | Hjv
        rotate_left
        · -- outside a joint configuration: accepted
          rw [Hjv]
          try wp_auto
          have Hstep1 : propConfStep c.joint s.logst.applied (logLast s.logst) (lpc (sint.nat n))
              (e, some (.v1 c1)) = ((lpc (sint.nat n)).1 ++ [e],
                logLast s.logst + W64 ((sint.nat n : Nat) : Int) + W64 1) := by
            unfold propConfStep
            simp only [Hnp, ccWantsLeave, Hjv, ne_eq, not_true_eq_false, _root_.or_self, ↓reduceIte, Hlpcn]
          wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
          icases ownRaftPhysC_log_same c r id _ $$ Hphys with ⟨Hlog, Hback⟩
          wp_apply wp_raftLog_lastIndex $$ [$Hlog] as %li ⟨Hlog, %Hli⟩
          ihave Hphys := Hback $$ Hlog
          try wp_auto
          wp_apply raft.wp_store_pendingConfIndexC $$ Hphys as Hphys
          wp_apply wp_traceChangeConfEvent
          have Hli' : li = logLast s.logst := by
            unfold logLast; simp only at Hli; word
          obtain ⟨Hcur', Hpci'⟩ := Hkeep _ Hstep1
          wp_for_post
          iframe
          iexists n + W64 1, n, els
          rw [Hcur', Hpci']
          ihave Hphys := ownRaftPhysC_eq c r id _
            { s with pci := logLast s.logst + W64 ((sint.nat n : Nat) : Int) + W64 1 }
            (by rw [Hli']; congr 2; word) $$ Hphys
          iframe
          iframe Hents
          ipureintro; word
        · -- inside one (`must transition out of joint config first`): refused
          rw [Hjv]
          wp_auto
          have Hstep0 : propConfStep c.joint s.logst.applied (logLast s.logst) (lpc (sint.nat n))
              (e, some (.v1 c1)) = ((lpc (sint.nat n)).1 ++ [zero_val EntryM], (lpc (sint.nat n)).2) := by
            unfold propConfStep
            simp only [ccWantsLeave, Hjv, ne_eq, Bool.false_eq_true, not_false_eq_true, _root_.or_true, ↓reduceIte]
          wp_apply raft.wp_load_disableConfChangeValidationC $$ Hphys as Hphys
          wp_apply raft.wp_load_idC $$ Hphys as Hphys
          first
          | wp_apply wp_DescribeConfChange.1 _ _ _ $$ [$Hown] as %str Hown
          | (ihave Hown := Hownback $$ HCh
             wp_apply wp_DescribeConfChange.2 _ _ _ $$ [$Hown] as %str Hown)
          icases ownRaftPhysC_tracker_same c r id _ $$ Hphys with ⟨%tv2, Htrkf, Htrk, Hback⟩
          icases (Access.access
              (A := r.[raft, go!"trk"].[tracker.ProgressTracker, go!"Config"] ↦ tv2.Config')
              (A' := r.[raft, go!"trk"].[tracker.ProgressTracker, go!"Config"] ↦ tv2.Config')
              (P := r.[raft, go!"trk"] ↦ tv2)) $$ Htrkf with ⟨Hcf, Htrkfback⟩
          wp_auto
          ihave Htrkf := Htrkfback $$ Hcf
          ihave Hphys := Hback $$ %tv2 Htrkf Htrk
          wp_raft_logC
          rw [show raftpb.EntryNormal = #(W32 0 : raftpb.EntryType) from rfl]
          haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
          wp_apply wp_EntryType_Enum (W32 0) as %pty Hpty
          imod entRO_normal_of_struct _ pty (normalEntryV pty) ⊤ rfl rfl rfl rfl rfl $$ [«$r0» Hpty] with #Hnew
          · iframe
          wp_apply wp_Message_GetEntries_field ml _ es0 Hmnn $$ [$HEs] as HEs
          rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hn.1, Hes0len⟩)]
          wp_apply wp_store_slice_index es0 (sint.Z n) els _ $$ [$Hes] as Hes
          · ipureintro; refine ⟨Hn.1, ?_⟩; rw [Hlen', Hcurlen]; word
          icases (BigSepL2.bigSepL2_insert_acc (Φ := fun _ p e => entRO (GF := GF) p e) Hl0' Hcur_lookup') $$ Hents with ⟨-, Hset⟩
          ihave Hents' := Hset $$ %_ %(zero_val EntryM) Hnew
          obtain ⟨Hcur', Hpci'⟩ := Hzero _ Hstep0
          wp_for_post
          iframe
          iexists n + W64 1, n, _
          rw [Hcur', Hpci']
          iframe
          iframe Hents'
          ipureintro; word
    · -- a `ConfChangeV2`
      iunfold ccEntOk at Heo
      icases Heo with ⟨%H2, %Hdec⟩
      rw [decide_eq_false (show e.Type' ≠ W32 1 by rw [H2]; word)]
      wp_auto
      wp_apply wp_Entry_GetType.1 l0 DFrac.discard e $$ [$He] as -
      rw [decide_eq_true (by rw [H2])]
      wp_auto
      wp_apply wp_Entry_GetData.1 l0 DFrac.discard e $$ [$He] as %ds ⟨#Hds, -⟩
      wp_apply wp_UnmarshalConfChangeV2 ds e.Data' DFrac.discard _ _ $$ [$Hds $«$r0»] as %err ⟨-, Hm⟩
      rw [Hdec]
      icases Hm with ⟨%Herr, Hown⟩
      subst Herr
      icases ownCCV2_changes _ _ _ $$ Hown with ⟨%chs, HCh, %Hchl, Hownback⟩
      wp_auto
      -- `alreadyPending := r.pendingConfIndex > r.raftLog.applied`
      wp_apply raft.wp_load_pendingConfIndexC $$ Hphys as Hphys
      wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
      icases ownRaftPhysC_log_same c r id _ $$ Hphys with ⟨Hlog, Hback⟩
      icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
      wp_auto
      ihave Hlog := Hlb $$ Hl
      ihave Hphys := Hback $$ Hlog
      -- `alreadyJoint := len(r.trk.Config.Voters[1]) > 0`: `c.joint` (2026-10-14)
      icases ownRaftPhysC_tracker_same c r id _ $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
      icases ownTrackerC_halves c tv _ $$ Htrk with ⟨%vin, %vout, %Harr, %Hcsz, Hv0, Hv1, Htrkback⟩
      have Hset1 : array.mk 2 (tv.Config'.Voters'.arr.set (sint.Z (W64 1)).toNat vout) =
          tv.Config'.Voters' := by
        generalize tv.Config'.Voters' = a at Harr ⊢
        cases a
        simp only at Harr
        subst Harr
        rfl
      icases (Access.access
          (A := r.[raft, go!"trk"].[tracker.ProgressTracker, go!"Config"].[tracker.Config, go!"Voters"]
            ↦ tv.Config'.Voters')
          (A' := r.[raft, go!"trk"].[tracker.ProgressTracker, go!"Config"].[tracker.Config, go!"Voters"]
            ↦ tv.Config'.Voters')
          (P := r.[raft, go!"trk"] ↦ tv)) $$ Htrkf with ⟨Hvf, Htrkfback⟩
      icases array_acc _ (sint.Z (W64 1)) _ _ _ vout (by decide) (by rw [Harr]; rfl)
        $$ Hvf with ⟨Hc1, Hcback⟩
      wp_auto
      ihave Hvf := Hcback $$ Hc1
      rw [Hset1]
      ihave Htrkf := Htrkfback $$ Hvf
      wp_apply wp_idset_len $$ Hv1 as ⟨Hv1, %Hlt1⟩
      have Hjd : decide (sint.Z (W64 0) < sint.Z (W64 (GMap.size c.outgoing : Int))) = c.joint := by
        unfold CfgM.joint
        apply decide_eq_decide.2
        have : sint.Z (W64 (GMap.size c.outgoing : Int)) = GMap.size c.outgoing := by word
        rw [this]; simp
      rw [Hjd]
      ihave Htrk := Htrkback $$ Hv0 Hv1
      ihave Hphys := Hback $$ %tv Htrkf Htrk
      -- `wantsLeaveJoint := len(cc.AsV2().Changes) == 0`: `AsV2` is the change itself
      wp_apply wp_ConfChangeV2_AsV2
      try wp_auto
      have Happ : lv.applied' = s.logst.applied := Hlv.2
      wp_if_destruct
      · -- a conf change is pending: refused
        have Hpend : uint.Z s.logst.applied < uint.Z (lpc (sint.nat n)).2 := by
          rw [← Happ]; exact Hif
        wp_apply raft.wp_load_pendingConfIndexC $$ Hphys as Hphys
        wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
        icases ownRaftPhysC_log_same c r id _ $$ Hphys with ⟨Hlog, Hback⟩
        icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv2, Hl, %Hlv2, Hlb⟩
        wp_auto
        ihave Hlog := Hlb $$ Hl
        ihave Hphys := Hback $$ Hlog
        wp_apply wp_slice_literal (V := GoInterface)
          [interface.mkOk go.uint64 #(lpc (sint.nat n)).2, interface.mkOk go.uint64 #lv2.applied']
        isplitr
        · ipureintro; rfl
        iintro %sla Hargs0
        icases Hargs0 with ⟨Hargs, -⟩
        wp_auto
        wp_apply wp_fmt_Sprintf $$ [$Hargs] as %str ⟨Hargs, %Hout⟩
        · ipureintro
          exact _root_.Perennial.fmt.ArgsWf.cons_int _ _ _ (.uint64 _)
            (_root_.Perennial.fmt.ArgsWf.cons_int _ _ _ (.uint64 _) _root_.Perennial.fmt.ArgsWf.nil)
        have Hstr : str ≠ [] := by
          obtain ⟨o', rfl, -⟩ := _root_.Perennial.fmt.SprintfOut.byte_inv (by decide) Hout
          simp
        simp only [decide_eq_false Hstr, Bool.not_false]
        wp_auto
        have Hstep0 : propConfStep c.joint s.logst.applied (logLast s.logst) (lpc (sint.nat n))
            (e, some (.v2 c2)) = ((lpc (sint.nat n)).1 ++ [zero_val EntryM], (lpc (sint.nat n)).2) := by
          unfold propConfStep
          simp only [Hpend, _root_.true_or, ↓reduceIte]
        wp_apply raft.wp_load_disableConfChangeValidationC $$ Hphys as Hphys
        wp_apply raft.wp_load_idC $$ Hphys as Hphys
        first
        | wp_apply wp_DescribeConfChange.1 _ _ _ $$ [$Hown] as %str Hown
        | (ihave Hown := Hownback $$ HCh
           wp_apply wp_DescribeConfChange.2 _ _ _ $$ [$Hown] as %str Hown)
        icases ownRaftPhysC_tracker_same c r id _ $$ Hphys with ⟨%tv2, Htrkf, Htrk, Hback⟩
        icases (Access.access
            (A := r.[raft, go!"trk"].[tracker.ProgressTracker, go!"Config"] ↦ tv2.Config')
            (A' := r.[raft, go!"trk"].[tracker.ProgressTracker, go!"Config"] ↦ tv2.Config')
            (P := r.[raft, go!"trk"] ↦ tv2)) $$ Htrkf with ⟨Hcf, Htrkfback⟩
        wp_auto
        ihave Htrkf := Htrkfback $$ Hcf
        ihave Hphys := Hback $$ %tv2 Htrkf Htrk
        wp_raft_logC
        rw [show raftpb.EntryNormal = #(W32 0 : raftpb.EntryType) from rfl]
        haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
        wp_apply wp_EntryType_Enum (W32 0) as %pty Hpty
        imod entRO_normal_of_struct _ pty (normalEntryV pty) ⊤ rfl rfl rfl rfl rfl $$ [«$r0» Hpty] with #Hnew
        · iframe
        wp_apply wp_Message_GetEntries_field ml _ es0 Hmnn $$ [$HEs] as HEs
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hn.1, Hes0len⟩)]
        wp_apply wp_store_slice_index es0 (sint.Z n) els _ $$ [$Hes] as Hes
        · ipureintro; refine ⟨Hn.1, ?_⟩; rw [Hlen', Hcurlen]; word
        icases (BigSepL2.bigSepL2_insert_acc (Φ := fun _ p e => entRO (GF := GF) p e) Hl0' Hcur_lookup') $$ Hents with ⟨-, Hset⟩
        ihave Hents' := Hset $$ %_ %(zero_val EntryM) Hnew
        obtain ⟨Hcur', Hpci'⟩ := Hzero _ Hstep0
        wp_for_post
        iframe
        iexists n + W64 1, n, _
        rw [Hcur', Hpci']
        iframe
        iframe Hents'
        ipureintro; word
      · have Hnp : ¬ uint.Z s.logst.applied < uint.Z (lpc (sint.nat n)).2 := by
          rw [← Happ]; exact Hif
        have Hlv0 : chs.len = W64 0 ↔ c2.changes = [] := by
          obtain ⟨h1, h2⟩ := Hchl
          constructor
          · intro h; apply List.eq_nil_of_length_eq_zero; rw [h1, h]; rfl
          · intro h; rw [h] at h1; simp only [List.length_nil] at h1; word
        by_cases Hcw : c2.changes = []
        · rw [decide_eq_true (Hlv0.2 Hcw)]
          try wp_auto
          rcases Bool.eq_false_or_eq_true c.joint with Hjv | Hjv
          rotate_left
          · -- an empty change outside a joint configuration: refused
            rw [Hjv]
            wp_auto
            have Hstep0 : propConfStep c.joint s.logst.applied (logLast s.logst) (lpc (sint.nat n))
                (e, some (.v2 c2)) = ((lpc (sint.nat n)).1 ++ [zero_val EntryM], (lpc (sint.nat n)).2) := by
              unfold propConfStep
              simp only [ccWantsLeave, Hcw, Hjv, List.isEmpty_nil, ne_eq, Bool.true_eq_false, not_false_eq_true, _root_.or_true, ↓reduceIte]
            wp_apply raft.wp_load_disableConfChangeValidationC $$ Hphys as Hphys
            wp_apply raft.wp_load_idC $$ Hphys as Hphys
            first
            | wp_apply wp_DescribeConfChange.1 _ _ _ $$ [$Hown] as %str Hown
            | (ihave Hown := Hownback $$ HCh
               wp_apply wp_DescribeConfChange.2 _ _ _ $$ [$Hown] as %str Hown)
            icases ownRaftPhysC_tracker_same c r id _ $$ Hphys with ⟨%tv2, Htrkf, Htrk, Hback⟩
            icases (Access.access
                (A := r.[raft, go!"trk"].[tracker.ProgressTracker, go!"Config"] ↦ tv2.Config')
                (A' := r.[raft, go!"trk"].[tracker.ProgressTracker, go!"Config"] ↦ tv2.Config')
                (P := r.[raft, go!"trk"] ↦ tv2)) $$ Htrkf with ⟨Hcf, Htrkfback⟩
            wp_auto
            ihave Htrkf := Htrkfback $$ Hcf
            ihave Hphys := Hback $$ %tv2 Htrkf Htrk
            wp_raft_logC
            rw [show raftpb.EntryNormal = #(W32 0 : raftpb.EntryType) from rfl]
            haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
            wp_apply wp_EntryType_Enum (W32 0) as %pty Hpty
            imod entRO_normal_of_struct _ pty (normalEntryV pty) ⊤ rfl rfl rfl rfl rfl $$ [«$r0» Hpty] with #Hnew
            · iframe
            wp_apply wp_Message_GetEntries_field ml _ es0 Hmnn $$ [$HEs] as HEs
            rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hn.1, Hes0len⟩)]
            wp_apply wp_store_slice_index es0 (sint.Z n) els _ $$ [$Hes] as Hes
            · ipureintro; refine ⟨Hn.1, ?_⟩; rw [Hlen', Hcurlen]; word
            icases (BigSepL2.bigSepL2_insert_acc (Φ := fun _ p e => entRO (GF := GF) p e) Hl0' Hcur_lookup') $$ Hents with ⟨-, Hset⟩
            ihave Hents' := Hset $$ %_ %(zero_val EntryM) Hnew
            obtain ⟨Hcur', Hpci'⟩ := Hzero _ Hstep0
            wp_for_post
            iframe
            iexists n + W64 1, n, _
            rw [Hcur', Hpci']
            iframe
            iframe Hents'
            ipureintro; word
          · -- a request to leave the joint configuration: accepted
            rw [Hjv]
            try wp_auto
            have Hstep1 : propConfStep c.joint s.logst.applied (logLast s.logst) (lpc (sint.nat n))
                (e, some (.v2 c2)) = ((lpc (sint.nat n)).1 ++ [e],
                  logLast s.logst + W64 ((sint.nat n : Nat) : Int) + W64 1) := by
              unfold propConfStep
              simp only [Hnp, ccWantsLeave, Hcw, Hjv, List.isEmpty_nil, ne_eq, not_true_eq_false, _root_.or_self, ↓reduceIte, Hlpcn]
            wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
            icases ownRaftPhysC_log_same c r id _ $$ Hphys with ⟨Hlog, Hback⟩
            wp_apply wp_raftLog_lastIndex $$ [$Hlog] as %li ⟨Hlog, %Hli⟩
            ihave Hphys := Hback $$ Hlog
            try wp_auto
            wp_apply raft.wp_store_pendingConfIndexC $$ Hphys as Hphys
            wp_apply wp_traceChangeConfEvent
            have Hli' : li = logLast s.logst := by
              unfold logLast; simp only at Hli; word
            obtain ⟨Hcur', Hpci'⟩ := Hkeep _ Hstep1
            wp_for_post
            iframe
            iexists n + W64 1, n, els
            rw [Hcur', Hpci']
            ihave Hphys := ownRaftPhysC_eq c r id _
              { s with pci := logLast s.logst + W64 ((sint.nat n : Nat) : Int) + W64 1 }
              (by rw [Hli']; congr 2; word) $$ Hphys
            iframe
            iframe Hents
            ipureintro; word
        · rw [decide_eq_false (fun h => Hcw (Hlv0.1 h))]
          try wp_auto
          have Hne : c2.changes.isEmpty = false := by
            cases h : c2.changes with
            | nil => exact absurd h Hcw
            | cons _ _ => rfl
          rcases Bool.eq_false_or_eq_true c.joint with Hjv | Hjv
          rotate_left
          · -- a change outside a joint configuration: accepted
            rw [Hjv]
            try wp_auto
            have Hstep1 : propConfStep c.joint s.logst.applied (logLast s.logst) (lpc (sint.nat n))
                (e, some (.v2 c2)) = ((lpc (sint.nat n)).1 ++ [e],
                  logLast s.logst + W64 ((sint.nat n : Nat) : Int) + W64 1) := by
              unfold propConfStep
              simp only [Hnp, ccWantsLeave, Hne, Hjv, ne_eq, not_true_eq_false, _root_.or_self, ↓reduceIte, Hlpcn]
            wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
            icases ownRaftPhysC_log_same c r id _ $$ Hphys with ⟨Hlog, Hback⟩
            wp_apply wp_raftLog_lastIndex $$ [$Hlog] as %li ⟨Hlog, %Hli⟩
            ihave Hphys := Hback $$ Hlog
            try wp_auto
            wp_apply raft.wp_store_pendingConfIndexC $$ Hphys as Hphys
            wp_apply wp_traceChangeConfEvent
            have Hli' : li = logLast s.logst := by
              unfold logLast; simp only at Hli; word
            obtain ⟨Hcur', Hpci'⟩ := Hkeep _ Hstep1
            wp_for_post
            iframe
            iexists n + W64 1, n, els
            rw [Hcur', Hpci']
            ihave Hphys := ownRaftPhysC_eq c r id _
              { s with pci := logLast s.logst + W64 ((sint.nat n : Nat) : Int) + W64 1 }
              (by rw [Hli']; congr 2; word) $$ Hphys
            iframe
            iframe Hents
            ipureintro; word
          · -- a change inside one: refused
            rw [Hjv]
            wp_auto
            have Hstep0 : propConfStep c.joint s.logst.applied (logLast s.logst) (lpc (sint.nat n))
                (e, some (.v2 c2)) = ((lpc (sint.nat n)).1 ++ [zero_val EntryM], (lpc (sint.nat n)).2) := by
              unfold propConfStep
              simp only [ccWantsLeave, Hne, Hjv, ne_eq, Bool.false_eq_true, not_false_eq_true, _root_.or_true, ↓reduceIte]
            wp_apply raft.wp_load_disableConfChangeValidationC $$ Hphys as Hphys
            wp_apply raft.wp_load_idC $$ Hphys as Hphys
            first
            | wp_apply wp_DescribeConfChange.1 _ _ _ $$ [$Hown] as %str Hown
            | (ihave Hown := Hownback $$ HCh
               wp_apply wp_DescribeConfChange.2 _ _ _ $$ [$Hown] as %str Hown)
            icases ownRaftPhysC_tracker_same c r id _ $$ Hphys with ⟨%tv2, Htrkf, Htrk, Hback⟩
            icases (Access.access
                (A := r.[raft, go!"trk"].[tracker.ProgressTracker, go!"Config"] ↦ tv2.Config')
                (A' := r.[raft, go!"trk"].[tracker.ProgressTracker, go!"Config"] ↦ tv2.Config')
                (P := r.[raft, go!"trk"] ↦ tv2)) $$ Htrkf with ⟨Hcf, Htrkfback⟩
            wp_auto
            ihave Htrkf := Htrkfback $$ Hcf
            ihave Hphys := Hback $$ %tv2 Htrkf Htrk
            wp_raft_logC
            rw [show raftpb.EntryNormal = #(W32 0 : raftpb.EntryType) from rfl]
            haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
            wp_apply wp_EntryType_Enum (W32 0) as %pty Hpty
            imod entRO_normal_of_struct _ pty (normalEntryV pty) ⊤ rfl rfl rfl rfl rfl $$ [«$r0» Hpty] with #Hnew
            · iframe
            wp_apply wp_Message_GetEntries_field ml _ es0 Hmnn $$ [$HEs] as HEs
            rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hn.1, Hes0len⟩)]
            wp_apply wp_store_slice_index es0 (sint.Z n) els _ $$ [$Hes] as Hes
            · ipureintro; refine ⟨Hn.1, ?_⟩; rw [Hlen', Hcurlen]; word
            icases (BigSepL2.bigSepL2_insert_acc (Φ := fun _ p e => entRO (GF := GF) p e) Hl0' Hcur_lookup') $$ Hents with ⟨-, Hset⟩
            ihave Hents' := Hset $$ %_ %(zero_val EntryM) Hnew
            obtain ⟨Hcur', Hpci'⟩ := Hzero _ Hstep0
            wp_for_post
            iframe
            iexists n + W64 1, n, _
            rw [Hcur', Hpci']
            iframe
            iframe Hents'
            ipureintro; word
  · -- the loop is done: `appendEntry` of the loop's batch
    have Hnend : sint.nat n = ents.length := by
      have := Hl'.1; rw [Hlen', Hcurlen] at this; word
    have Htake : ∀ {A : Type} (l : List A), l.length = ents.length → l.take (sint.nat n) = l := by
      intro A l hl; rw [Hnend, ← hl, List.take_length]
    have Hfin : lpc (sint.nat n) = leaderPropConf s ents cs c.joint := by
      simp only [lpc, leaderPropConf, Htake ents rfl, Htake cs Hcslen]
    rw [Hnend] at Hfin
    rw [Hnend, List.drop_length, List.append_nil, Hfin]
    wp_apply wp_Message_GetEntries_field ml _ es0 Hmnn $$ [$HEs] as HEs
    have Hlen' : ((leaderPropConf s ents cs c.joint).1.length : Int) < 2^61 := by
      simp only [leaderPropConf]
      rw [propConf_length, Hcslen, Nat.min_self]; exact Hsmall
    wp_apply wp_raft_appendEntry c r id { s with pci := (leaderPropConf s ents cs c.joint).2 } _
        (leaderPropConf s ents cs c.joint).1 (DFrac.own 1) Hlen' Hnz $$ [$Hphys Hes]
      as %acc ⟨-, -, Hphys⟩
    · iunfold entsPts
      iexists els
      iframe Hes Hents
    cases acc <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · -- dropped
      wp_auto
      iapply HΦ $$ %errPropDropped %_ %true
      iframe Hphys
      isplitr
      · ipureintro
        exact ⟨cs, Hct, by simp⟩
      simp only [↓reduceIte]
      iexact ErrPropDropped
    · wp_auto
      wp_apply wp_raft_bcastAppend $$ [$Hphys] as %ms %pvs ⟨Hphys, %Hms, %Hmm⟩
      iapply HΦ $$ %interface.nil %_ %false
      iframe Hphys
      isplitr
      · ipureintro
        refine ⟨cs, Hct, ?_⟩
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨ms, pvs, rfl, Hms, Hmm⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro; trivial


end proof

end EtcdGrove
end Perennial
