/-
`stepLeader`'s `MsgProp` branch (split out of `stepLeader.lean` on 2026-10-13, with the
conf-change loop of reconfiguration stage D): `wp_stepLeader_prop`.
-/
module

public import Spec.go_etcd_io.raft.v3.stepLeader
public import Spec.go_etcd_io.raft.v3.raft__bcastAppend
public import Spec.go_etcd_io.raft.v3.raft__appendEntry
public import Spec.go_etcd_io.raft.v3.raftLog__lastIndex
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChange__Unmarshal
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__Unmarshal
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChange__AsV2
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__AsV2
public import Spec.fmt.Sprintf
public import Spec.go_etcd_io.raft.v3.traceChangeConfEvent

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

variable (cfg : GSet w64)

/-- The voter map out of a tracker, back at any map with the same key set. -/
private theorem ownTracker_voters (tv : tracker.ProgressTracker) (t : Trk) :
    ⊢ ownTracker (GF := GF) cfg tv t -∗
      ∃ (vr : Loc) (voters : GMap w64 Unit),
        ⌜tv.Config'.Voters'.arr = [vr, map.nil]⌝ ∗ ⌜domSet voters = cfg⌝ ∗
        ⌜(GMap.size cfg : Int) ≤ 2 ^ 62⌝ ∗ vr ↦$ voters ∗
        (∀ voters' : GMap w64 Unit, ⌜domSet voters' = cfg⌝ -∗ vr ↦$ voters' -∗
           ownTracker cfg tv t) := by
  iintro Hown
  iunfold ownTracker at Hown
  icases Hown with ⟨%voters_ref, %voters, %learners, %learnersNext, Hown⟩
  iNamed Hown
  iexists voters_ref, voters
  isplitr
  · ipureintro; exact Hvoters_arr
  isplitr
  · ipureintro; exact Hvoters_dom
  isplitr
  · ipureintro; exact cfg_size_le cfg _ Hprs_dom Hcfg_size
  iframe Hvoters
  iintro %voters' %Hd Hv
  iapply ownTracker_intro cfg tv t.votes t.prs t.peers voters_ref voters' learners learnersNext
    Hprs_dom Hvoters_arr Hautoleave Hd Hno_learners Hcfg_size HmaxInfl
    $$ Hvotes Hprs Hprogs Hv Hlearners HlearnersNext

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

/-- `pb.Entry{Type: EntryNormal}`, as the translation builds it, is the zero entry. -/
private theorem entry_normal_lit :
    ({ Term' := 0, Index' := 0, Type' := W32 0, Data' := slice.nil } : raftpb.Entry) =
      zero_val raftpb.Entry := rfl

/-- A list written back at the element it holds. -/
private theorem list_set_self {A : Type} (l : List A) (i : Int) (x : A)
    (H : l[i.toNat]? = some x) : l.set i.toNat x = l := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 H
  rw [← hget]; exact List.set_getElem_self hlt


set_option maxHeartbeats 1600000 in
/-- **`MsgProp`**

`len(m.Entries) == 0` is false (`ents ≠ []`); `r.trk.Progress[r.id]` is a hit
(`id ∈ cfg`, and a `Progress` pointer is never nil); a leader transfer in progress drops
the proposal. Then (2026-10-13, reconfiguration stage D) the conf-change loop: entry `n`
of the batch -- the loop's state is the batch with the first `n` entries as the loop
left them (`leaderPropConf` of the first `n`), and `pendingConfIndex` as it left it --
is decoded (`Unmarshal`, from `ccEntsOk`'s bytes, never failing) when it is a conf change,
and checked: refused (overwritten with `pb.Entry{Type: EntryNormal}`) when a conf change
is pending or it is an empty `ConfChangeV2`, else accepted (`pendingConfIndex` moved).
`r.trk.Config.Voters[1]` is `nil` (the configuration in use is simple), so `alreadyJoint`
is false; `disableConfChangeValidation` is false (`ownRaftPhys`). Then `appendEntry`
stamps the loop's batch and, if it accepts it, `bcastAppend`. -/
theorem wp_stepLeader_prop
    (wp_raft_bcastAppend : raft.bcastAppend.spec (GF := GF) (hG := hG))
    (wp_raft_appendEntry : raft.appendEntry.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_ConfChange_Unmarshal : raftpb.ConfChange.Unmarshal.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_Unmarshal : raftpb.ConfChangeV2.Unmarshal.spec (GF := GF) (hG := hG))
    (wp_ConfChange_AsV2 : raftpb.ConfChange.AsV2.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_AsV2 : raftpb.ConfChangeV2.AsV2.spec (GF := GF) (hG := hG))
    (wp_fmt_Sprintf : fmt.Sprintf.spec (GF := GF) (hG := hG))
    (wp_traceChangeConfEvent : traceChangeConfEvent.spec (GF := GF) (hG := hG))
    (r : Loc) (id : w64) (s : NState) (m : raftpb.Message) (ents : List raftpb.Entry)
    (cs : List (Option CCMsg))
    (Hty : m.Type' = MsgProp) (Hid : id ∈ cfg) (Hne : ents ≠ [])
    (Hsmall : (ents.length : Int) < 2^61) (Hnz : s.term ≠ W64 0) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s ∗
        m.Entries' ↦* ents ∗ ccEntsOk ents cs }}
      (App (App (Val #(functions stepLeader [])) (Val #r)) (Val #m))
    {{ (err : GoInterface) (s' : NState) (dropped : Bool), RET #err;
        ownRaftPhys cfg r id s' ∗
        ⌜LeaderProposeResult id s ents dropped s'⌝ ∗
        (if dropped then globalAddr ErrProposalDropped ↦□ err
         else ⌜err = interface.nil⌝) ∗
        (∃ ents' : List raftpb.Entry, m.Entries' ↦* ents') }} := by
  wp_start as ⟨Hphys, Hes, #Hcc⟩
  ihave %Hct := ccEntsOk_types ents cs $$ Hcc
  have Hcslen : cs.length = ents.length := (List.Forall₂.length_eq Hct).symm
  iunfold ccEntsOk at Hcc
  ihave #Hinit := isInitialized_access $$ Hpkg
  unfold isInitialized
  icases Hinit with ⟨%e1, %e2, %e3, %e4, %errPropDropped, %gr, %_, %_, %_, %_, #Hinit⟩
  iNamed Hinit
  wp_auto
  simp only [Hty, MsgProp]
  wp_auto
  ihave %Hl := ownSlice_len _ _ _ $$ Hes
  wp_if_destruct
  · exfalso
    apply Hne
    apply List.eq_nil_of_length_eq_zero
    rw [Hl.1, Hif]; rfl
  wp_apply raft.wp_load_id $$ Hphys as Hphys
  icases ownRaftPhys_tracker_same cfg r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  icases ownTracker_progress_map cfg tv _ $$ Htrk with ⟨#Hprs, %Hdom, Htrk⟩
  icases ownTracker_prvals_dom cfg tv _ $$ Htrk with ⟨%Hpdom, Htrk⟩
  dsimp only at Hdom Hpdom
  wp_auto
  ihave Hphys := Hback $$ Htrkf Htrk
  wp_apply wp_map_lookup1 go.uint64 (go.GoType.PointerType tracker.Progress.ty) _ s.progress
    id _ $$ Hprs with -
  obtain ⟨pr, Hlk⟩ : ∃ pr, s.progress !! id = some pr := by
    rw [← GMap.elem_of_dom]; exact (GMap.elem_of_subseteq _ _).1 Hdom _ Hid
  obtain ⟨p, Hpvs⟩ : ∃ p, s.prvals !! id = some p := by
    rw [← GMap.elem_of_dom, Hpdom, GMap.elem_of_dom]; exact ⟨pr, Hlk⟩
  icases ownRaftPhys_pr cfg r id s id pr p $$ Hphys %Hlk %Hpvs with ⟨Hpa, Hpback⟩
  iNamed Hpa
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hpv
  ihave Hphys := Hpback $$ [Hpv Hinfl]
  · iapply ownProgress_intro $$ Hpv Hinfl %Habs
  rw [Hlk]
  simp only [Option.getD_some]
  wp_if_destruct
  · exact absurd rfl Hnn
  wp_apply raft.wp_load_leadTransferee $$ Hphys as Hphys
  -- (2026-10-13) a leader transfer in progress drops the proposal
  by_cases Hlt : s.lt = W64 0
  rotate_left
  · rw [decide_eq_false Hlt]
    wp_auto
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    wp_apply raft.wp_load_Term $$ Hphys as Hphys
    wp_apply raft.wp_load_leadTransferee $$ Hphys as Hphys
    wp_raft_log
    iapply HΦ $$ %errPropDropped %s %true
    iframe Hphys
    isplitr
    · ipureintro
      exact ⟨cs, Hct, by simp⟩
    simp only [↓reduceIte]
    iframe ErrPropDropped
    iexists ents
    iexact Hes
  rw [decide_eq_true Hlt]
  wp_auto
  rename_i gi_ptr
  irename : (gi_ptr ↦ zero_val w64 : IProp GF) => Hgi
  -- the loop's state after `n` entries
  let lpc : Nat → List raftpb.Entry × w64 := fun n =>
    propConf s.logst.applied (logLast s.logst) s.pci (ents.take n) (cs.take n)
  have Hlpc_len : ∀ n, n ≤ ents.length → (lpc n).1.length = n := by
    intro n hn
    simp only [lpc]
    rw [propConf_length]; simp only [List.length_take]; omega
  ihave IH : iprop(∃ (n k : w64),
      "Hj" ∷ i_ptr ↦ n ∗
      "Hgi" ∷ gi_ptr ↦ k ∗
      "Hes" ∷ m.Entries' ↦* ((lpc (sint.nat n)).1 ++ ents.drop (sint.nat n)) ∗
      "Hphys" ∷ ownRaftPhys cfg r id { s with pci := (lpc (sint.nat n)).2 } ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ents.length : Int)⌝) $$ [i Hgi Hes Hphys]
  · iexists W64 0, zero_val w64
    simp only [lpc, show sint.nat (W64 0) = 0 from rfl, propConf_take_zero, List.nil_append,
      List.drop_zero]
    iframe
    ipureintro
    word
  wp_for IH
  ihave %Hl' := ownSlice_len _ _ _ $$ Hes
  have Hcurlen : ((lpc (sint.nat n)).1 ++ ents.drop (sint.nat n)).length = ents.length := by
    rw [List.length_append, Hlpc_len _ (by word), List.length_drop]; word
  wp_if_destruct
  · -- entry `n`
    have Hnlt : sint.nat n < ents.length := by word
    obtain ⟨e, He_lookup⟩ : ∃ e, ents[sint.nat n]? = some e :=
      ⟨_, List.getElem?_eq_getElem Hnlt⟩
    obtain ⟨o, Ho_lookup⟩ : ∃ o, cs[sint.nat n]? = some o :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have Hcur_lookup : ((lpc (sint.nat n)).1 ++ ents.drop (sint.nat n))[(sint.Z n).toNat]? =
        some e := by
      rw [show (sint.Z n).toNat = sint.nat n by word, List.getElem?_append_right
        (Nat.le_of_eq (Hlpc_len _ (by word))), Hlpc_len _ (by word), Nat.sub_self,
        List.getElem?_drop, Nat.add_zero, He_lookup]
    ihave #Heo := BigSepL2.bigSepL2_lookup (Φ := fun _ e o => ccEntOk (GF := GF) e o)
      He_lookup Ho_lookup $$ Hcc
    have Hstep := propConf_take_succ s.logst.applied (logLast s.logst) s.pci ents cs
      (sint.nat n) e o He_lookup Ho_lookup
    have Hnext : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    have Hlpcn := Hlpc_len (sint.nat n) (by word)
    -- the next state, when the loop keeps entry `n` or overwrites it
    have Hkeep : ∀ p', propConfStep s.logst.applied (logLast s.logst) (lpc (sint.nat n)) (e, o) =
        ((lpc (sint.nat n)).1 ++ [e], p') →
        (lpc (sint.nat (n + W64 1))).1 ++ ents.drop (sint.nat (n + W64 1)) =
          (lpc (sint.nat n)).1 ++ ents.drop (sint.nat n) ∧ (lpc (sint.nat (n + W64 1))).2 = p' := by
      intro p' Hp
      simp only [lpc, Hnext, Hstep] at Hp ⊢
      rw [Hp, list_drop_S ents _ e He_lookup]
      simp
    have Hzero : ∀ p', propConfStep s.logst.applied (logLast s.logst) (lpc (sint.nat n)) (e, o) =
        ((lpc (sint.nat n)).1 ++ [zero_val raftpb.Entry], p') →
        (lpc (sint.nat (n + W64 1))).1 ++ ents.drop (sint.nat (n + W64 1)) =
          ((lpc (sint.nat n)).1 ++ ents.drop (sint.nat n)).set (sint.Z n).toNat
            (zero_val raftpb.Entry) ∧ (lpc (sint.nat (n + W64 1))).2 = p' := by
      intro p' Hp
      simp only [lpc, Hnext, Hstep] at Hp ⊢
      rw [Hp, show (sint.Z n).toNat = sint.nat n by word,
        list_set_mid _ ents (sint.nat n) _ e (by simpa [lpc] using Hlpcn) He_lookup]
      simp
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
    wp_apply wp_load_slice_index _ (sint.Z n) _ (DFrac.own 1) e Hn.1 $$ [Hes] with Hes
    · iframe
      ipureintro
      exact Hcur_lookup
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
    icases ownSlice_elem_acc (sint.Z n) e _ (DFrac.own 1) _ Hn.1 Hcur_lookup $$ Hes
      with ⟨He, Hesback⟩
    wp_auto
    rcases o with _ | (c1 | c2)
    · -- not a conf change: `cc` stays `nil`
      iunfold ccEntOk at Heo
      icases Heo with %Hnc
      have H1 : e.Type' ≠ W32 1 := fun h => Hnc (Or.inl h)
      have H2 : e.Type' ≠ W32 2 := fun h => Hnc (Or.inr h)
      rw [decide_eq_false (by intro h; apply H1; rw [h])]
      wp_auto
      rw [decide_eq_false (by intro h; apply H2; rw [h])]
      wp_auto
      ihave Hes := Hesback $$ %e He
      rw [list_set_self _ (sint.Z n) e Hcur_lookup]
      wp_for_post
      iframe
      iexists n + W64 1, n
      have Hcur' : (lpc (sint.nat (n + W64 1))).1 ++ ents.drop (sint.nat (n + W64 1)) =
          (lpc (sint.nat n)).1 ++ ents.drop (sint.nat n) := by
        simp only [lpc, Hnext, Hstep, propConfStep, List.append_assoc, List.singleton_append]
        rw [list_drop_S ents _ e He_lookup]
      rw [Hcur']
      have Hpci' : (lpc (sint.nat (n + W64 1))).2 = (lpc (sint.nat n)).2 := by
        simp only [lpc, Hnext, Hstep, propConfStep]
      rw [Hpci']
      iframe
      ipureintro
      word
    · -- a `ConfChange`
      iunfold ccEntOk at Heo
      icases Heo with ⟨%H1, %bs, #Hbs, %Hdec⟩
      rw [decide_eq_true (by rw [H1])]
      wp_auto
      wp_apply wp_ConfChange_Unmarshal ccc_ptr e.Data' bs DFrac.discard $$ [$ccc $Hbs]
        as %err ⟨-, %v, Hccc, Hm⟩
      rw [Hdec]
      icases Hm with ⟨%Herr, Hown⟩
      subst Herr
      wp_auto
      -- `alreadyPending := r.pendingConfIndex > r.raftLog.applied`
      wp_apply raft.wp_load_pendingConfIndex $$ Hphys as Hphys
      wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
      icases ownRaftPhys_log_same cfg r id _ $$ Hphys with ⟨Hlog, Hback⟩
      icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
      wp_auto
      ihave Hlog := Hlb $$ Hl
      ihave Hphys := Hback $$ Hlog
      -- `alreadyJoint := len(r.trk.Config.Voters[1]) > 0`: the outgoing half is `nil`
      icases ownRaftPhys_tracker_same cfg r id _ $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
      icases ownTracker_voters cfg tv _ $$ Htrk with ⟨%vr, %voters, %Harr, %Hvd, %Hcsz, Hv, Htrkback⟩
      have Hset1 : array.mk 2 (tv.Config'.Voters'.arr.set (sint.Z (W64 1)).toNat map.nil) =
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
      icases array_acc _ (sint.Z (W64 1)) _ _ _ map.nil (by decide) (by rw [Harr]; rfl)
        $$ Hvf with ⟨Hc1, Hcback⟩
      wp_auto
      ihave Hvf := Hcback $$ Hc1
      rw [Hset1]
      ihave Htrkf := Htrkfback $$ Hvf
      ihave Htrk := Htrkback $$ %voters %Hvd Hv
      ihave Hphys := Hback $$ %tv Htrkf Htrk
      -- `wantsLeaveJoint := len(cc.AsV2().Changes) == 0`: a `ConfChange` has one change
      wp_apply wp_ConfChange_AsV2 as %v2 ⟨-, Hch⟩
      ihave %Hchl := ownSlice_len _ _ _ $$ Hch
      try wp_auto
      have Happ : lv.applied' = s.logst.applied := Hlv.2
      wp_if_destruct
      · -- a conf change is pending: refused
        have Hpend : uint.Z s.logst.applied < uint.Z (lpc (sint.nat n)).2 := by
          rw [← Happ]; exact Hif
        wp_apply raft.wp_load_pendingConfIndex $$ Hphys as Hphys
        wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
        icases ownRaftPhys_log_same cfg r id _ $$ Hphys with ⟨Hlog, Hback⟩
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
        have Hstep0 : propConfStep s.logst.applied (logLast s.logst) (lpc (sint.nat n))
            (e, some (.v1 c1)) = ((lpc (sint.nat n)).1 ++ [zero_val raftpb.Entry], (lpc (sint.nat n)).2) := by
          unfold propConfStep
          simp only [Hpend, true_or, ↓reduceIte]
        wp_apply raft.wp_load_disableConfChangeValidation $$ Hphys as Hphys
        wp_apply raft.wp_load_id $$ Hphys as Hphys
        icases ownRaftPhys_tracker_same cfg r id _ $$ Hphys with ⟨%tv2, Htrkf, Htrk, Hback⟩
        icases (Access.access
            (A := r.[raft, go!"trk"].[tracker.ProgressTracker, go!"Config"] ↦ tv2.Config')
            (A' := r.[raft, go!"trk"].[tracker.ProgressTracker, go!"Config"] ↦ tv2.Config')
            (P := r.[raft, go!"trk"] ↦ tv2)) $$ Htrkf with ⟨Hcf, Htrkfback⟩
        wp_auto
        ihave Htrkf := Htrkfback $$ Hcf
        ihave Hphys := Hback $$ %tv2 Htrkf Htrk
        wp_raft_log
        ihave Hes := Hesback $$ %e He
        rw [list_set_self _ (sint.Z n) e Hcur_lookup]
        rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
        wp_apply wp_store_slice_index _ (sint.Z n) _ _ $$ [$Hes] as Hes
        · ipureintro; rw [Hcurlen]; word
        rw [entry_normal_lit]
        obtain ⟨Hcur', Hpci'⟩ := Hzero _ Hstep0
        wp_for_post
        iframe
        iexists n + W64 1, n
        rw [Hcur', Hpci']
        iframe
        ipureintro; word
      · -- no conf change pending and one change: accepted
        have Hnp : ¬ uint.Z s.logst.applied < uint.Z (lpc (sint.nat n)).2 := by
          rw [← Happ]; exact Hif
        have Hch0 : v2.Changes'.len ≠ W64 0 := by
          intro h; have h1 := Hchl.1; rw [h] at h1; simp [sint.nat] at h1
        rw [decide_eq_false Hch0]
        try wp_auto
        have Hstep1 : propConfStep s.logst.applied (logLast s.logst) (lpc (sint.nat n))
            (e, some (.v1 c1)) = ((lpc (sint.nat n)).1 ++ [e],
              logLast s.logst + W64 ((sint.nat n : Nat) : Int) + W64 1) := by
          unfold propConfStep
          simp only [Hnp, ccWantsLeave, Bool.false_eq_true, _root_.or_self, ↓reduceIte, Hlpcn]
        wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
        icases ownRaftPhys_log_same cfg r id _ $$ Hphys with ⟨Hlog, Hback⟩
        wp_apply wp_raftLog_lastIndex $$ [$Hlog] as %li ⟨Hlog, %Hli⟩
        ihave Hphys := Hback $$ Hlog
        try wp_auto
        wp_apply raft.wp_store_pendingConfIndex $$ Hphys as Hphys
        wp_apply wp_traceChangeConfEvent
        ihave Hes := Hesback $$ %e He
        rw [list_set_self _ (sint.Z n) e Hcur_lookup]
        have Hli' : li = logLast s.logst := by
          unfold logLast; simp only at Hli; word
        obtain ⟨Hcur', Hpci'⟩ := Hkeep _ Hstep1
        wp_for_post
        iframe
        iexists n + W64 1, n
        rw [Hcur', Hpci']
        ihave Hphys := ownRaftPhys_eq cfg r id _
          { s with pci := logLast s.logst + W64 ((sint.nat n : Nat) : Int) + W64 1 }
          (by rw [Hli']; congr 2; word) $$ Hphys
        iframe
        ipureintro; word
    · -- a `ConfChangeV2`
      iunfold ccEntOk at Heo
      icases Heo with ⟨%H2, %bs, #Hbs, %Hdec⟩
      rw [decide_eq_false (show e.Type' ≠ W32 1 by rw [H2]; word)]
      wp_auto
      rw [decide_eq_true (by rw [H2])]
      wp_auto
      wp_apply wp_ConfChangeV2_Unmarshal ccc_ptr e.Data' bs DFrac.discard $$ [$ccc $Hbs]
        as %err ⟨-, %v, Hccc, Hm⟩
      rw [Hdec]
      icases Hm with ⟨%Herr, Hown⟩
      subst Herr
      iunfold ownCCV2 at Hown
      icases Hown with ⟨%Htr, Hch, Hctx⟩
      ihave %Hchl := ownSlice_len _ _ _ $$ Hch
      wp_auto
      -- `alreadyPending := r.pendingConfIndex > r.raftLog.applied`
      wp_apply raft.wp_load_pendingConfIndex $$ Hphys as Hphys
      wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
      icases ownRaftPhys_log_same cfg r id _ $$ Hphys with ⟨Hlog, Hback⟩
      icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
      wp_auto
      ihave Hlog := Hlb $$ Hl
      ihave Hphys := Hback $$ Hlog
      -- `alreadyJoint := len(r.trk.Config.Voters[1]) > 0`: the outgoing half is `nil`
      icases ownRaftPhys_tracker_same cfg r id _ $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
      icases ownTracker_voters cfg tv _ $$ Htrk with ⟨%vr, %voters, %Harr, %Hvd, %Hcsz, Hv, Htrkback⟩
      have Hset1 : array.mk 2 (tv.Config'.Voters'.arr.set (sint.Z (W64 1)).toNat map.nil) =
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
      icases array_acc _ (sint.Z (W64 1)) _ _ _ map.nil (by decide) (by rw [Harr]; rfl)
        $$ Hvf with ⟨Hc1, Hcback⟩
      wp_auto
      ihave Hvf := Hcback $$ Hc1
      rw [Hset1]
      ihave Htrkf := Htrkfback $$ Hvf
      ihave Htrk := Htrkback $$ %voters %Hvd Hv
      ihave Hphys := Hback $$ %tv Htrkf Htrk
      -- `wantsLeaveJoint := len(cc.AsV2().Changes) == 0`: `AsV2` is the change itself
      wp_apply wp_ConfChangeV2_AsV2
      try wp_auto
      have Happ : lv.applied' = s.logst.applied := Hlv.2
      wp_if_destruct
      · -- a conf change is pending: refused
        have Hpend : uint.Z s.logst.applied < uint.Z (lpc (sint.nat n)).2 := by
          rw [← Happ]; exact Hif
        wp_apply raft.wp_load_pendingConfIndex $$ Hphys as Hphys
        wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
        icases ownRaftPhys_log_same cfg r id _ $$ Hphys with ⟨Hlog, Hback⟩
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
        have Hstep0 : propConfStep s.logst.applied (logLast s.logst) (lpc (sint.nat n))
            (e, some (.v2 c2)) = ((lpc (sint.nat n)).1 ++ [zero_val raftpb.Entry], (lpc (sint.nat n)).2) := by
          unfold propConfStep
          simp only [Hpend, true_or, ↓reduceIte]
        wp_apply raft.wp_load_disableConfChangeValidation $$ Hphys as Hphys
        wp_apply raft.wp_load_id $$ Hphys as Hphys
        icases ownRaftPhys_tracker_same cfg r id _ $$ Hphys with ⟨%tv2, Htrkf, Htrk, Hback⟩
        icases (Access.access
            (A := r.[raft, go!"trk"].[tracker.ProgressTracker, go!"Config"] ↦ tv2.Config')
            (A' := r.[raft, go!"trk"].[tracker.ProgressTracker, go!"Config"] ↦ tv2.Config')
            (P := r.[raft, go!"trk"] ↦ tv2)) $$ Htrkf with ⟨Hcf, Htrkfback⟩
        wp_auto
        ihave Htrkf := Htrkfback $$ Hcf
        ihave Hphys := Hback $$ %tv2 Htrkf Htrk
        wp_raft_log
        ihave Hes := Hesback $$ %e He
        rw [list_set_self _ (sint.Z n) e Hcur_lookup]
        rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
        wp_apply wp_store_slice_index _ (sint.Z n) _ _ $$ [$Hes] as Hes
        · ipureintro; rw [Hcurlen]; word
        rw [entry_normal_lit]
        obtain ⟨Hcur', Hpci'⟩ := Hzero _ Hstep0
        wp_for_post
        iframe
        iexists n + W64 1, n
        rw [Hcur', Hpci']
        iframe
        ipureintro; word
      · have Hnp : ¬ uint.Z s.logst.applied < uint.Z (lpc (sint.nat n)).2 := by
          rw [← Happ]; exact Hif
        have Hlv0 : v.Changes'.len = W64 0 ↔ c2.changes = [] := by
          obtain ⟨h1, h2⟩ := Hchl
          constructor
          · intro h; apply List.eq_nil_of_length_eq_zero; rw [h1, h]; rfl
          · intro h; rw [h] at h1; simp only [List.length_nil] at h1; word
        by_cases Hcw : c2.changes = []
        · -- an empty change, outside a joint configuration: refused
          rw [decide_eq_true (Hlv0.2 Hcw)]
          wp_auto
          have Hstep0 : propConfStep s.logst.applied (logLast s.logst) (lpc (sint.nat n))
              (e, some (.v2 c2)) = ((lpc (sint.nat n)).1 ++ [zero_val raftpb.Entry], (lpc (sint.nat n)).2) := by
            unfold propConfStep
            simp only [ccWantsLeave, Hcw, List.isEmpty_nil, or_true, ↓reduceIte]
          wp_apply raft.wp_load_disableConfChangeValidation $$ Hphys as Hphys
          wp_apply raft.wp_load_id $$ Hphys as Hphys
          icases ownRaftPhys_tracker_same cfg r id _ $$ Hphys with ⟨%tv2, Htrkf, Htrk, Hback⟩
          icases (Access.access
              (A := r.[raft, go!"trk"].[tracker.ProgressTracker, go!"Config"] ↦ tv2.Config')
              (A' := r.[raft, go!"trk"].[tracker.ProgressTracker, go!"Config"] ↦ tv2.Config')
              (P := r.[raft, go!"trk"] ↦ tv2)) $$ Htrkf with ⟨Hcf, Htrkfback⟩
          wp_auto
          ihave Htrkf := Htrkfback $$ Hcf
          ihave Hphys := Hback $$ %tv2 Htrkf Htrk
          wp_raft_log
          ihave Hes := Hesback $$ %e He
          rw [list_set_self _ (sint.Z n) e Hcur_lookup]
          rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
          wp_apply wp_store_slice_index _ (sint.Z n) _ _ $$ [$Hes] as Hes
          · ipureintro; rw [Hcurlen]; word
          rw [entry_normal_lit]
          obtain ⟨Hcur', Hpci'⟩ := Hzero _ Hstep0
          wp_for_post
          iframe
          iexists n + W64 1, n
          rw [Hcur', Hpci']
          iframe
          ipureintro; word
        · -- accepted
          rw [decide_eq_false (fun h => Hcw (Hlv0.1 h))]
          try wp_auto
          have Hstep1 : propConfStep s.logst.applied (logLast s.logst) (lpc (sint.nat n))
              (e, some (.v2 c2)) = ((lpc (sint.nat n)).1 ++ [e],
                logLast s.logst + W64 ((sint.nat n : Nat) : Int) + W64 1) := by
            unfold propConfStep
            have Hne : c2.changes.isEmpty = false := by
              cases h : c2.changes with
              | nil => exact absurd h Hcw
              | cons _ _ => rfl
            simp only [Hnp, ccWantsLeave, Hne, Bool.false_eq_true, _root_.or_self, ↓reduceIte, Hlpcn]
          wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
          icases ownRaftPhys_log_same cfg r id _ $$ Hphys with ⟨Hlog, Hback⟩
          wp_apply wp_raftLog_lastIndex $$ [$Hlog] as %li ⟨Hlog, %Hli⟩
          ihave Hphys := Hback $$ Hlog
          try wp_auto
          wp_apply raft.wp_store_pendingConfIndex $$ Hphys as Hphys
          wp_apply wp_traceChangeConfEvent
          ihave Hes := Hesback $$ %e He
          rw [list_set_self _ (sint.Z n) e Hcur_lookup]
          have Hli' : li = logLast s.logst := by
            unfold logLast; simp only at Hli; word
          obtain ⟨Hcur', Hpci'⟩ := Hkeep _ Hstep1
          wp_for_post
          iframe
          iexists n + W64 1, n
          rw [Hcur', Hpci']
          ihave Hphys := ownRaftPhys_eq cfg r id _
            { s with pci := logLast s.logst + W64 ((sint.nat n : Nat) : Int) + W64 1 }
            (by rw [Hli']; congr 2; word) $$ Hphys
          iframe
          ipureintro; word
  · -- the loop is done: `appendEntry` of the loop's batch
    have Hnend : sint.nat n = ents.length := by word
    have Htake : ∀ {A : Type} (l : List A), l.length = ents.length → l.take (sint.nat n) = l := by
      intro A l hl; rw [Hnend, ← hl, List.take_length]
    have Hfin : lpc (sint.nat n) = leaderPropConf s ents cs := by
      simp only [lpc, leaderPropConf, Htake ents rfl, Htake cs Hcslen]
    rw [Hnend] at Hfin
    rw [Hnend, List.drop_length, List.append_nil, Hfin]
    have Hlen' : ((leaderPropConf s ents cs).1.length : Int) < 2^61 := by
      simp only [leaderPropConf]
      rw [propConf_length, Hcslen, Nat.min_self]; exact Hsmall
    wp_apply (raft.appendEntry.spec_simple wp_raft_appendEntry) cfg r id { s with pci := (leaderPropConf s ents cs).2 } _
        (leaderPropConf s ents cs).1 Hlen' Hnz $$ [$Hphys $Hes]
      as %acc ⟨-, Hes, Hphys⟩
    cases acc <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · -- dropped
      wp_auto
      iapply HΦ $$ %errPropDropped %_ %true
      iframe Hphys
      isplitr
      · ipureintro
        exact ⟨cs, Hct, by simp⟩
      simp only [↓reduceIte]
      iframe ErrPropDropped
      iexists _
      iexact Hes
    · wp_auto
      wp_apply wp_raft_bcastAppend $$ [$Hphys] as %ms %pvs ⟨Hphys, %Hms, %Hmm⟩
      iapply HΦ $$ %interface.nil %_ %false
      iframe Hphys
      isplitr
      · ipureintro
        refine ⟨cs, Hct, ?_⟩
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨ms, pvs, rfl, Hms, Hmm⟩
      isplitr
      · simp only [Bool.false_eq_true, ↓reduceIte]
        ipureintro; trivial
      iexists _
      iexact Hes


end proof

end EtcdGrove
end Perennial
