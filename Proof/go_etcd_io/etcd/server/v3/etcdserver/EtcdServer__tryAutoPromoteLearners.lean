/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__tryAutoPromoteLearners.lean`
(PR `etcd-io/etcd#21744`), plus mechanized characterization theorems for Findings 1 and 2.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__tryAutoPromoteLearners
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__Members
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.errors.Is
public import Spec.errors.IsCtxErr
public import Proof.errors.NewVarCell
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

instance notInterface_uint64_autoPromote [FfiSyntax] : go.NotInterface go.uint64 :=
  ⟨by unfold go.uint64; trivial⟩

/-- One label value for a one-label metric vector (`learnerPromoteFailed`). -/
theorem prometheus.labelValuesOk_one (a l1 : GoString) (ha : utf8Valid a) :
    prometheus.labelValuesOk [l1] [a] := by
  refine ⟨rfl, ?_⟩
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  subst hv
  exact ha

/-- If a leaf error `e` is distinct from all 10 `AutoPromoteTargets`, `ts.mem e = false`
(Finding 2: the `switch` in `tryAutoPromoteLearners` misses all 10 cases and enters `default:`,
incrementing `learnerPromoteFailed` and logging `Warn("auto-promote failed")`). -/
theorem AutoPromoteTargets.mem_eq_false_of_ne [FfiSyntax] (ts : AutoPromoteTargets)
    (e : GoInterfaceOk)
    (h1 : e ≠ ts.idNotFound) (h2 : e ≠ ts.notLearner)
    (h3 : e ≠ ts.canceled) (h4 : e ≠ ts.stopped)
    (h5 : e ≠ ts.timeoutWaitApplied) (h6 : e ≠ ts.timeout)
    (h7 : e ≠ ts.leaderChanged) (h8 : e ≠ ts.notLeader)
    (h9 : e ≠ ts.notEnoughStarted) (h10 : e ≠ ts.learnerNotReady) :
    ts.mem e = false := by
  unfold AutoPromoteTargets.mem
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

/-- The 10 error messages of the `switch` targets in `tryAutoPromoteLearners`. -/
def autoPromoteTargetMsgs : List GoString :=
  [go!"membership: member not found",
   go!"membership: can only promote a learner member",
   go!"etcdserver: request cancelled",
   go!"etcdserver: server stopped",
   go!"etcdserver: request timed out, waiting for the applied index took too long",
   go!"etcdserver: request timed out",
   go!"etcdserver: leader changed",
   go!"etcdserver: not leader",
   go!"etcdserver: re-configuration failed due to not enough started members",
   go!"etcdserver: can only promote a learner member which is in sync with leader"]

/-- **Finding 2 (pure message distinctness)**:
- `raft.ErrProposalDropped` (`"raft proposal dropped"`),
- `errors.ErrTimeoutDueToLeaderFail` (`"etcdserver: request timed out, possibly due to previous leader failure"`), and
- `errors.ErrTimeoutDueToConnectionLost` (`"etcdserver: request timed out, possibly due to connection lost"`)
have messages distinct from all 10 `autoPromoteTargetMsgs` in `tryAutoPromoteLearners`. -/
theorem finding2_transient_msgs_not_in_targets :
    go!"raft proposal dropped" ∉ autoPromoteTargetMsgs ∧
    go!"etcdserver: request timed out, possibly due to previous leader failure" ∉ autoPromoteTargetMsgs ∧
    go!"etcdserver: request timed out, possibly due to connection lost" ∉ autoPromoteTargetMsgs := by
  decide

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- Borrow both `m.ID` and `m.RaftAttributes.IsLearner` from `membership.memberIs m id`. -/
theorem membership.memberIs_id_learner_acc (m : Loc) (id : w64) :
    membership.memberIs (GF := GF) m id ⊢
      ∃ il : Bool, membership.mIDAddr m ↦ id ∗ membership.mIsLearnerAddr m ↦ il ∗
        (membership.mIDAddr m ↦ id ∗ membership.mIsLearnerAddr m ↦ il -∗
          membership.memberIs m id) := by
  unfold membership.memberIs
  iintro ⟨%Hnn, %pu, %cu, %il, %nm, %pus, %cus, Hid, Hpu, Hil, Hnm, Hcu, Hpus, Hcus, %Hpok⟩
  iexists il
  iframe Hid Hil
  iintro ⟨Hid, Hil⟩
  isplitr
  · ipureintro; exact Hnn
  iexists pu, cu, il, nm, pus, cus
  iframe
  ipureintro; exact Hpok

/-- **`errors.Is(GoInterface.ok e, GoInterface.ok eT)`** on a leaf pointer error `e` and a pointer
target `eT` returns `#(decide (e = eT))`. -/
theorem wp_Is_leaf (hIs : errors.Is.spec (GF := GF) (hG := hG)) (e eT : GoInterfaceOk)
    (hl : errLeaf e) (hpt : _root_.Perennial.errors.IsPointerError eT) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors }}
      (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #(GoInterface.ok e)))
        (Val #(GoInterface.ok eT)))
    {{ RET #(decide (e = eT)); True }} := by
  iintro %Φ #Hp HΦ
  iapply hIs (· = GoInterface.ok e) (fun _ => False) (GoInterface.ok e) (GoInterface.ok eT)
    (fun tii h => by cases h; exact hpt)
    (_root_.Perennial.errors.treeTyped_pointer e _ hl.1) $$ []
  · iframe Hp
    isplitl
    · iapply _root_.Perennial.errors.errorIsTree_leaf e (fun _ => False) _ hl.2.1 hl.2.2
    ipureintro; rfl
  iintro !> %b ⟨-, %h2, %h3⟩
  by_cases heq : e = eT
  · have hb : b = true := h2 eT rfl hpt (congrArg GoInterface.ok heq)
    subst hb
    rw [decide_eq_true heq]
    iapply HΦ
    itrivial
  · cases b
    · rw [decide_eq_false heq]
      iapply HΦ
      itrivial
    · exfalso
      obtain ⟨ii, hii, hor⟩ := h3 eT rfl hpt (by simp) rfl
      cases hii
      rcases hor with h | h
      · cases h; exact heq rfl
      · exact h

set_option hygiene false in
local macro "zap_fields" : tactic => `(tactic| (
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨-, -⟩
  (try wp_auto)))

set_option hygiene false in
/-- Helper tactic for the `lg.Debug("auto-promote skipped", ...)` branch of the 10-way switch
in `EtcdServer.tryAutoPromoteLearners`. -/
local macro "skip_branch" : tactic => `(tactic| (
  (try wp_auto)
  wp_apply (hIDSp (membership.mIDAddr m0) (DFrac.own 1) id) $$ [Hid] as %lstr ⟨Hid, -⟩
  · iframe #; iframe Hid
  wp_apply hZS as %f1 -
  (try wp_auto)
  wp_apply hZE as %f2 -
  (try wp_auto)
  zap_fields
  wp_apply hDbg _ _ _ $$ []
  · iframe #; ipureintro; exact Hlgnn
  (try wp_auto)
  ihave Hm := Hback $$ [Hid Hil]
  · iframe Hid Hil
  ihave Hown := Hclose $$ [Hm]
  · iunfold membership.ownMember; iexists id; iexact Hm
  rw [hs]
  wp_for_post
  iframe
  iexists n + W64 1, m0
  simp only [named]
  iframe
  ipureintro; constructor <;> word))

set_option maxHeartbeats 1600000 in
theorem EtcdServer.tryAutoPromoteLearners.wp_proof
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hMem : membership.RaftCluster.Members.spec (GF := GF) (hG := hG))
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hIDS : types.ID.String.spec (GF := GF) (hG := hG))
    (hIDSp : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hZS : zap.String.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hIs : errors.Is.spec (GF := GF) (hG := hG))
    (hZE : zap.Error.spec (GF := GF) (hG := hG))
    (hDbg : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (hCV : prometheus.CounterVec.WithLabelValues.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    EtcdServer.tryAutoPromoteLearners.spec (GF := GF) (hG := hG) := by
  intro s lg
  wp_start as ⟨#Hpre, Hlr⟩
  iunfold srvAutoPromotePre at Hpre
  icases Hpre with ⟨#Hlgf, %Hlgnn, ⟨%lgMu, #Hlgmu⟩, ⟨%mid, #Hmid⟩, ⟨%cl, #Hclf, #Hrc⟩,
    ⟨%sctx, %st, %rctx, #Hctxf, #Hstf, #Hwr, #Hprom⟩, ⟨%cSucc, #Hsuccf, #HcSucc⟩,
    ⟨%cvFail, #Hfailf, %HcvLbl⟩, ⟨%ts, #Hts⟩⟩
  iunfold authWithRootOk at Hwr
  icases Hwr with ⟨%ai, %Hai, #HWithRoot⟩
  subst Hai
  iunfold promoteMemberOk at Hprom
  iunfold prometheus.counterSpec at HcSucc
  iunfold autoPromoteTargetVars at Hts
  icases Hts with ⟨%Hptr, #HT1, #HT2, #HT3, #HT4, #HT5, #HT6, #HT7, #HT8, #HT9, #HT10⟩
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10⟩ := Hptr
  ihave #Pmem : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  ihave #Ptyp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Perr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Pprom : isPkgInit (PROP := IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus $$ []
  · iPkgInit
  wp_auto
  wp_apply (hLg s lg) $$ [Hlr] as ⟨%_, Hlr⟩
  · iframe #; iframe Hlr; ipureintro; exact Hlgnn
  wp_apply HWithRoot $$ []
  wp_apply (hMem cl) $$ [] as %sl ⟨%ms, Hms⟩
  · iframe #
  iunfold membership.membersAt at Hms
  icases Hms with ⟨Hsl, Hown⟩
  ihave %Hsll := ownSlice_len $$ Hsl
  ihave IH : iprop(∃ (n : w64) (x : Loc),
      "i" ∷ i_ptr ↦ n ∗ "m" ∷ m_ptr ↦ x ∗
      "s" ∷ s_ptr ↦ s ∗ "lg" ∷ lg_ptr ↦ lg ∗ "ctx" ∷ ctx_ptr ↦ rctx ∗
      "Hsl" ∷ sl ↦* ms ∗ "Hown" ∷ ([∗list] m ∈ ms, membership.ownMember m) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ms.length : Int)⌝)
    $$ [i m s lg ctx Hsl Hown]
  · iexists W64 0, zero_val Loc
    simp only [named]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < ms.length := by word
    obtain ⟨m0, Hm0⟩ : ∃ m0, ms[sint.nat n]? = some m0 := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, Hif⟩
    rw [ite_eq_left Hbnd]
    wp_apply wp_load_slice_index sl (sint.Z n) ms (DFrac.own 1) m0 Hn.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hm0
    icases (BigSepL.bigSepL_lookup_acc (PROP := IProp GF)
      (Φ := fun (_ : Nat) (y : Loc) => membership.ownMember (GF := GF) y) Hm0).1 $$ Hown
      with ⟨Hm, Hclose⟩
    iunfold membership.ownMember at Hm
    icases Hm with ⟨%id, Hm⟩
    icases membership.memberIs_id_learner_acc m0 id $$ Hm with ⟨%il, Hid, Hil, Hback⟩
    have hs : ms.set (sint.nat n) m0 = ms := by
      apply List.ext_getElem?
      intro k
      rw [List.getElem?_set]
      split
      · rename_i hk; subst hk; rw [Hm0]; try simp [Hlt]
      · rfl
    (try wp_auto)
    cases il
    · -- `!m.IsLearner`: continue
      (try wp_auto)
      ihave Hm := Hback $$ [Hid Hil]
      · iframe Hid Hil
      ihave Hown := Hclose $$ [Hm]
      · iunfold membership.ownMember; iexists id; iexact Hm
      rw [hs]
      wp_for_post
      iframe
      iexists n + W64 1, m0
      simp only [named]
      iframe
      ipureintro; constructor <;> word
    · -- `m.IsLearner`: call `s.promoteMember(ctx, uint64(m.ID))`
      (try wp_auto)
      wp_apply Hprom $$ [] as %sl_p %err #Herr
      (try wp_auto)
      iunfold promoteErrOk at Herr
      icases Herr with (%Hnil | ⟨%e, %msg, %He, #Hemsg⟩)
      · -- `err == nil`: `learnerPromoteSucceed.Inc()` and `lg.Info(...)`
        subst Hnil
        (try wp_auto)
        wp_apply HcSucc $$ []
        (try wp_auto)
        wp_apply (hMID s mid) $$ []
        · iframe #
        wp_apply (hIDS mid) $$ [$Ptyp] as %mstr -
        wp_apply hZS as %f1 -
        wp_apply (hIDSp (membership.mIDAddr m0) (DFrac.own 1) id) $$ [Hid] as %lstr ⟨Hid, -⟩
        · iframe #; iframe Hid
        wp_apply hZS as %f2 -
        (try wp_auto)
        zap_fields
        wp_apply hInfo _ _ _ $$ []
        · iframe #; ipureintro; exact Hlgnn
        (try wp_auto)
        ihave Hm := Hback $$ [Hid Hil]
        · iframe Hid Hil
        ihave Hown := Hclose $$ [Hm]
        · iunfold membership.ownMember; iexists id; iexact Hm
        rw [hs]
        wp_for_post
        iframe
        iexists n + W64 1, m0
        simp only [named]
        iframe
        ipureintro; constructor <;> word
      · -- `err != nil`: 10-way `errors.Is` switch
        obtain ⟨rfl, hl, hutf⟩ := He
        (try wp_auto)
        wp_apply (wp_Is_leaf hIs e ts.idNotFound hl hp1) $$ [$Perr]
        wp_if_destruct
        · skip_branch
        wp_apply (wp_Is_leaf hIs e ts.notLearner hl hp2) $$ [$Perr]
        wp_if_destruct
        · skip_branch
        wp_apply (wp_Is_leaf hIs e ts.canceled hl hp3) $$ [$Perr]
        wp_if_destruct
        · skip_branch
        wp_apply (wp_Is_leaf hIs e ts.stopped hl hp4) $$ [$Perr]
        wp_if_destruct
        · skip_branch
        wp_apply (wp_Is_leaf hIs e ts.timeoutWaitApplied hl hp5) $$ [$Perr]
        wp_if_destruct
        · skip_branch
        wp_apply (wp_Is_leaf hIs e ts.timeout hl hp6) $$ [$Perr]
        wp_if_destruct
        · skip_branch
        wp_apply (wp_Is_leaf hIs e ts.leaderChanged hl hp7) $$ [$Perr]
        wp_if_destruct
        · skip_branch
        wp_apply (wp_Is_leaf hIs e ts.notLeader hl hp8) $$ [$Perr]
        wp_if_destruct
        · skip_branch
        wp_apply (wp_Is_leaf hIs e ts.notEnoughStarted hl hp9) $$ [$Perr]
        wp_if_destruct
        · skip_branch
        wp_apply (wp_Is_leaf hIs e ts.learnerNotReady hl hp10) $$ [$Perr]
        wp_if_destruct
        · skip_branch
        -- `default:` branch: `learnerPromoteFailed.WithLabelValues(err.Error()).Inc()` and `lg.Warn(...)`
        (try wp_auto)
        wp_apply Hemsg $$ []
        wp_apply wp_slice_literal (V := GoString) [msg]
        isplitr
        · ipureintro; rfl
        iintro %lvs ⟨Hlvs, -⟩
        (try wp_auto)
        wp_apply hCV cvFail _ [go!"ReasonForFailure"] _ _ $$ [Hlvs]
          as %c ⟨%ci, %Hci, #HciSpec, -⟩
        · iframe #; iframe Hlvs
          ipureintro
          exact ⟨HcvLbl, prometheus.labelValuesOk_one msg go!"ReasonForFailure" hutf⟩
        subst Hci
        (try wp_auto)
        iunfold prometheus.counterSpec at HciSpec
        wp_apply HciSpec $$ []
        (try wp_auto)
        wp_apply (hIDSp (membership.mIDAddr m0) (DFrac.own 1) id) $$ [Hid] as %lstr ⟨Hid, -⟩
        · iframe #; iframe Hid
        wp_apply hZS as %f1 -
        (try wp_auto)
        wp_apply hZE as %f2 -
        (try wp_auto)
        zap_fields
        wp_apply hWarn _ _ _ $$ []
        · iframe #; ipureintro; exact Hlgnn
        (try wp_auto)
        ihave Hm := Hback $$ [Hid Hil]
        · iframe Hid Hil
        ihave Hown := Hclose $$ [Hm]
        · iunfold membership.ownMember; iexists id; iexact Hm
        rw [hs]
        wp_for_post
        iframe
        iexists n + W64 1, m0
        simp only [named]
        iframe
        ipureintro; constructor <;> word
  · (try wp_auto)
    iapply HΦ
    iexact Hlr

/-- If `ts.mem e = false`, none of the 10 `decide (e = ts.target)` tests can evaluate to `true`. -/
theorem AutoPromoteTargets.mem_not_eq_of_false [FfiSyntax] (ts : AutoPromoteTargets)
    (e : GoInterfaceOk) (hf : ts.mem e = false) :
    ¬(true = decide (e = ts.idNotFound)) ∧
    ¬(true = decide (e = ts.notLearner)) ∧
    ¬(true = decide (e = ts.canceled)) ∧
    ¬(true = decide (e = ts.stopped)) ∧
    ¬(true = decide (e = ts.timeoutWaitApplied)) ∧
    ¬(true = decide (e = ts.timeout)) ∧
    ¬(true = decide (e = ts.leaderChanged)) ∧
    ¬(true = decide (e = ts.notLeader)) ∧
    ¬(true = decide (e = ts.notEnoughStarted)) ∧
    ¬(true = decide (e = ts.learnerNotReady)) := by
  unfold AutoPromoteTargets.mem at hf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro h; have heq := of_decide_eq_true h.symm; subst heq; simp at hf)

/-- If `X` and `g` have `errVarCell`s with distinct messages `msg ≠ msgT`, their `GoInterfaceOk`
values `e` and `eT` are distinct (`e ≠ eT`). -/
theorem errVarCell_val_ne (X g msg msgT : GoString) (e eT : GoInterfaceOk) (hm : msg ≠ msgT) :
    globalAddr X ↦□ GoInterface.ok e ⊢
      globalAddr g ↦□ GoInterface.ok eT -∗
      errVarCell (GF := GF) X msg -∗
      errVarCell g msgT -∗
      ⌜e ≠ eT⌝ := by
  iintro #HX #Hg #HCX #HCg
  ihave #Hap := errVarApart_of X g msg msgT hm $$ HCX HCg
  iunfold errVarApart at Hap
  icases Hap with ⟨%e1, %e2, #HX', #Hg', %Hne⟩
  icombine HX HX' gives %h1
  icombine Hg Hg' gives %h2
  ipureintro
  injection h1 with h1'
  injection h2 with h2'
  subst h1' h2'
  exact Hne

/-- The `errVarCell`s of the 10 target error variables in `tryAutoPromoteLearners`'s `switch`. -/
def autoPromoteTargetCells : IProp GF :=
  iprop(errVarCell go_etcd_io.etcd.server.v3.etcdserver.api.membership.ErrIDNotFound
      go!"membership: member not found" ∗
    errVarCell go_etcd_io.etcd.server.v3.etcdserver.api.membership.ErrMemberNotLearner
      go!"membership: can only promote a learner member" ∗
    errVarCell go_etcd_io.etcd.server.v3.etcdserver.errors.ErrCanceled
      go!"etcdserver: request cancelled" ∗
    errVarCell go_etcd_io.etcd.server.v3.etcdserver.errors.ErrStopped
      go!"etcdserver: server stopped" ∗
    errVarCell go_etcd_io.etcd.server.v3.etcdserver.errors.ErrTimeoutWaitAppliedIndex
      go!"etcdserver: request timed out, waiting for the applied index took too long" ∗
    errVarCell go_etcd_io.etcd.server.v3.etcdserver.errors.ErrTimeout
      go!"etcdserver: request timed out" ∗
    errVarCell go_etcd_io.etcd.server.v3.etcdserver.errors.ErrLeaderChanged
      go!"etcdserver: leader changed" ∗
    errVarCell go_etcd_io.etcd.server.v3.etcdserver.errors.ErrNotLeader
      go!"etcdserver: not leader" ∗
    errVarCell go_etcd_io.etcd.server.v3.etcdserver.errors.ErrNotEnoughStartedMembers
      go!"etcdserver: re-configuration failed due to not enough started members" ∗
    errVarCell go_etcd_io.etcd.server.v3.etcdserver.errors.ErrLearnerNotReady
      go!"etcdserver: can only promote a learner member which is in sync with leader")

instance autoPromoteTargetCells_persistent :
    Persistent (autoPromoteTargetCells (GF := GF)) := by
  unfold autoPromoteTargetCells; infer_instance

/-- **Finding 2 (Iris `errVarCell` distinctness)**: any `errors.New(msg)` variable `X` whose message
`msg` is not in `autoPromoteTargetMsgs` holds a `GoInterfaceOk` value `e` satisfying
`ts.mem e = false` (so `tryAutoPromoteLearners`'s 10-way `switch` misses all 10 cases and enters
`default:`, incrementing `learnerPromoteFailed` and logging `Warn("auto-promote failed")`). -/
theorem autoPromoteTargetVars_mem_false_of_cell (ts : AutoPromoteTargets)
    (X msg : GoString) (e : GoInterfaceOk) (hmsg : msg ∉ autoPromoteTargetMsgs) :
    autoPromoteTargetVars (GF := GF) ts ⊢
      autoPromoteTargetCells -∗
      globalAddr X ↦□ GoInterface.ok e -∗
      errVarCell X msg -∗
      ⌜ts.mem e = false⌝ := by
  unfold autoPromoteTargetVars autoPromoteTargetCells
  iintro ⟨%-, #HT1, #HT2, #HT3, #HT4, #HT5, #HT6, #HT7, #HT8, #HT9, #HT10⟩
    ⟨#HC1, #HC2, #HC3, #HC4, #HC5, #HC6, #HC7, #HC8, #HC9, #HC10⟩ #HX #HCX
  have hm1 : msg ≠ go!"membership: member not found" := fun h => hmsg (by subst h; decide)
  have hm2 : msg ≠ go!"membership: can only promote a learner member" := fun h => hmsg (by subst h; decide)
  have hm3 : msg ≠ go!"etcdserver: request cancelled" := fun h => hmsg (by subst h; decide)
  have hm4 : msg ≠ go!"etcdserver: server stopped" := fun h => hmsg (by subst h; decide)
  have hm5 : msg ≠ go!"etcdserver: request timed out, waiting for the applied index took too long" :=
    fun h => hmsg (by subst h; decide)
  have hm6 : msg ≠ go!"etcdserver: request timed out" := fun h => hmsg (by subst h; decide)
  have hm7 : msg ≠ go!"etcdserver: leader changed" := fun h => hmsg (by subst h; decide)
  have hm8 : msg ≠ go!"etcdserver: not leader" := fun h => hmsg (by subst h; decide)
  have hm9 : msg ≠ go!"etcdserver: re-configuration failed due to not enough started members" :=
    fun h => hmsg (by subst h; decide)
  have hm10 : msg ≠ go!"etcdserver: can only promote a learner member which is in sync with leader" :=
    fun h => hmsg (by subst h; decide)
  ihave %hne1 := errVarCell_val_ne X _ msg _ e ts.idNotFound hm1 $$ HX HT1 HCX HC1
  ihave %hne2 := errVarCell_val_ne X _ msg _ e ts.notLearner hm2 $$ HX HT2 HCX HC2
  ihave %hne3 := errVarCell_val_ne X _ msg _ e ts.canceled hm3 $$ HX HT3 HCX HC3
  ihave %hne4 := errVarCell_val_ne X _ msg _ e ts.stopped hm4 $$ HX HT4 HCX HC4
  ihave %hne5 := errVarCell_val_ne X _ msg _ e ts.timeoutWaitApplied hm5 $$ HX HT5 HCX HC5
  ihave %hne6 := errVarCell_val_ne X _ msg _ e ts.timeout hm6 $$ HX HT6 HCX HC6
  ihave %hne7 := errVarCell_val_ne X _ msg _ e ts.leaderChanged hm7 $$ HX HT7 HCX HC7
  ihave %hne8 := errVarCell_val_ne X _ msg _ e ts.notLeader hm8 $$ HX HT8 HCX HC8
  ihave %hne9 := errVarCell_val_ne X _ msg _ e ts.notEnoughStarted hm9 $$ HX HT9 HCX HC9
  ihave %hne10 := errVarCell_val_ne X _ msg _ e ts.learnerNotReady hm10 $$ HX HT10 HCX HC10
  ipureintro
  exact AutoPromoteTargets.mem_eq_false_of_ne ts e hne1 hne2 hne3 hne4 hne5 hne6 hne7 hne8 hne9 hne10

/-- **Finding 2 corollary for `raft.ErrProposalDropped`**: `ts.mem e = false`. -/
theorem finding2_ErrProposalDropped_mem_false (ts : AutoPromoteTargets) (e : GoInterfaceOk) :
    autoPromoteTargetVars (GF := GF) ts ⊢
      autoPromoteTargetCells -∗
      globalAddr go_etcd_io.raft.v3.ErrProposalDropped ↦□ GoInterface.ok e -∗
      errVarCell go_etcd_io.raft.v3.ErrProposalDropped go!"raft proposal dropped" -∗
      ⌜ts.mem e = false⌝ :=
  autoPromoteTargetVars_mem_false_of_cell ts _ _ e finding2_transient_msgs_not_in_targets.1

/-- **Finding 2 corollary for `errors.ErrTimeoutDueToLeaderFail`**: `ts.mem e = false`. -/
theorem finding2_ErrTimeoutDueToLeaderFail_mem_false (ts : AutoPromoteTargets) (e : GoInterfaceOk) :
    autoPromoteTargetVars (GF := GF) ts ⊢
      autoPromoteTargetCells -∗
      globalAddr go_etcd_io.etcd.server.v3.etcdserver.errors.ErrTimeoutDueToLeaderFail ↦□ GoInterface.ok e -∗
      errVarCell go_etcd_io.etcd.server.v3.etcdserver.errors.ErrTimeoutDueToLeaderFail
        go!"etcdserver: request timed out, possibly due to previous leader failure" -∗
      ⌜ts.mem e = false⌝ :=
  autoPromoteTargetVars_mem_false_of_cell ts _ _ e finding2_transient_msgs_not_in_targets.2.1

/-- **Finding 2 corollary for `errors.ErrTimeoutDueToConnectionLost`**: `ts.mem e = false`. -/
theorem finding2_ErrTimeoutDueToConnectionLost_mem_false (ts : AutoPromoteTargets) (e : GoInterfaceOk) :
    autoPromoteTargetVars (GF := GF) ts ⊢
      autoPromoteTargetCells -∗
      globalAddr go_etcd_io.etcd.server.v3.etcdserver.errors.ErrTimeoutDueToConnectionLost ↦□ GoInterface.ok e -∗
      errVarCell go_etcd_io.etcd.server.v3.etcdserver.errors.ErrTimeoutDueToConnectionLost
        go!"etcdserver: request timed out, possibly due to connection lost" -∗
      ⌜ts.mem e = false⌝ :=
  autoPromoteTargetVars_mem_false_of_cell ts _ _ e finding2_transient_msgs_not_in_targets.2.2

/-- **Finding 1 (`parseProposeCtxErr` on a deadline-free `ctx`)**: when `ctx` has no deadline
(such as `ctx := s.authStore.WithRoot(s.ctx)` in `tryAutoPromoteLearners`), its only cancellation
error `err := ctx.Err()` is `context.Canceled`. On `context.Canceled`, `s.parseProposeCtxErr(err, start)`
always takes its first `switch` arm and returns `errors.ErrCanceled` (`eCan`), never reaching the
`context.DeadlineExceeded` arm that returns `errors.ErrTimeout` (`eCan ≠ ts.timeout`). Thus
`errors.ErrTimeout` in `tryAutoPromoteLearners`'s `switch` is unreachable from `s.configure(ctx, &cc)`. -/
theorem EtcdServer.parseProposeCtxErr.wp_canceled_ne_timeout
    (hIs : errors.IsCtxErr.spec (GF := GF) (hG := hG))
    (s : Loc) (err : GoInterface) (start : time.Time) (ts : AutoPromoteTargets)
    (Herr : context.isTypedErr err) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        globalAddr context.Canceled ↦□ err ∗
        autoPromoteTargetVars ts ∗ autoPromoteTargetCells }}
      (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"parseProposeCtxErr"))
        (Val #err)) (Val #start))
    {{ (e : GoInterface), RET #e;
        ∃ eCan : GoInterfaceOk, ⌜e = GoInterface.ok eCan ∧ eCan = ts.canceled ∧ eCan ≠ ts.timeout⌝ }} := by
  wp_start as ⟨#Herrv, #Hts, #Hcells⟩
  ihave #Perrors : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave Hci : (context.isInit : IProp GF) $$ []
  · iapply context.isInit_access $$ Pctx
  iNamed Hci
  icases HCanceled with ⟨%eC, #HeC, %-⟩
  iunfold autoPromoteTargetVars at Hts
  icases Hts with ⟨%-, #HT1, #HT2, #HT3, #HT4, #HT5, #HT6, -⟩
  iunfold autoPromoteTargetCells at Hcells
  icases Hcells with ⟨-, -, #HC3, -, -, #HC6, -⟩
  have hm : (go!"etcdserver: request cancelled" : GoString) ≠ go!"etcdserver: request timed out" := by decide
  ihave %Hne := errVarCell_val_ne _ _ _ _ ts.canceled ts.timeout hm $$ HT3 HT6 HC3 HC6
  wp_auto
  wp_apply hIs err eC Herr $$ [] as %b1 %Hb1
  · iframe #
  cases b1
  · iexfalso
    icombine Herrv HeC gives %h
    exact absurd (Hb1 h) (by simp)
  · rw [decide_eq_true rfl]
    (try wp_auto)
    iapply HΦ
    iexists ts.canceled
    ipureintro
    exact ⟨rfl, rfl, Hne⟩

set_option maxHeartbeats 1600000 in
/-- **Finding 2 Hoare triple (`wp_default_forced`)**: when `s.cluster.Members()` contains a learner
`m0` (`IsLearner = true`) and `s.promoteMember(ctx, m0.ID)` returns a leaf error `e` with
`ts.mem e = false` (such as `raft.ErrProposalDropped`, `errors.ErrTimeoutDueToLeaderFail`, or
`errors.ErrTimeoutDueToConnectionLost`), `s.tryAutoPromoteLearners()` cannot take the success branch
or any of the 10 `auto-promote skipped` `Debug` branches (notice `zap.Logger.Info.spec` and
`zap.Logger.Debug.spec` are not even assumed); it is forced into `default:`, calling
`learnerPromoteFailed.WithLabelValues(msg).Inc()` and `lg.Warn("auto-promote failed", ...)` to
transform the linear resource `P` into `Q`. -/
theorem EtcdServer.tryAutoPromoteLearners.wp_default_forced
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hIDSp : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hZS : zap.String.spec (GF := GF) (hG := hG))
    (hIs : errors.Is.spec (GF := GF) (hG := hG))
    (hZE : zap.Error.spec (GF := GF) (hG := hG))
    (hCV : prometheus.CounterVec.WithLabelValues.spec (GF := GF) (hG := hG))
    (s lg cl m0 cvFail : Loc) (id : w64) (sctx st rctx : GoInterface)
    (e : GoInterfaceOk) (msg : GoString) (ts : AutoPromoteTargets)
    (P Q : IProp GF)
    (Hlgnn : lg ≠ null)
    (hl : errLeaf e) (hutf : utf8Valid msg) (hf : ts.mem e = false)
    (HcvLbl : prometheus.vecLabels cvFail [go!"ReasonForFailure"])
    (hMem1 :
      {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership }}
        (App (Val (cl @!! go.GoType.PointerType
            go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"Members"))
          (Val #()))
      {{ (sl : GoSlice), RET #sl;
          sl ↦* [m0] ∗ membership.mIDAddr m0 ↦ id ∗ membership.mIsLearnerAddr m0 ↦ true }})
    (hProm1 :
      {{ (True : IProp GF) }}
        (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"promoteMember"))
          (Val #rctx)) (Val #id))
      {{ (sl_p : GoSlice), RET (PairV #sl_p #(GoInterface.ok e)); (True : IProp GF) }})
    (hErrMsg :
      {{ (True : IProp GF) }}
        (App (Val #(methods e.ty go!"Error" e.v)) (Val #()))
      {{ RET #msg; (True : IProp GF) }})
    (hWarnP : ∀ (fsl : GoSlice),
      {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap ∗ ⌜lg ≠ null⌝ ∗ P }}
        (App (App (Val (lg @!! go.GoType.PointerType go_uber_org.zap.Logger.ty @!! go!"Warn"))
          (Val #(go!"auto-promote failed"))) (Val #fsl))
      {{ RET #(); Q }}) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        srvLgAddr s ↦□ lg ∗ srvClusterAddr s ↦□ cl ∗
        structFieldRef EtcdServer go!"ctx" s ↦□ sctx ∗
        srvAuthStoreAddr s ↦□ st ∗ authWithRootOk st sctx rctx ∗
        globalAddr learnerPromoteFailed ↦□ cvFail ∗
        autoPromoteTargetVars ts ∗
        srvLgReader s ∗ P }}
      (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"tryAutoPromoteLearners")) (Val #()))
    {{ RET #(); srvLgReader s ∗ Q }} := by
  wp_start as ⟨#Hlgf, #Hclf, #Hctxf, #Hstf, #Hwr, #Hfailf, #Hts, Hlr, HP⟩
  iunfold authWithRootOk at Hwr
  icases Hwr with ⟨%ai, %Hai, #HWithRoot⟩
  subst Hai
  iunfold autoPromoteTargetVars at Hts
  icases Hts with ⟨%Hptr, #HT1, #HT2, #HT3, #HT4, #HT5, #HT6, #HT7, #HT8, #HT9, #HT10⟩
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10⟩ := Hptr
  obtain ⟨hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10⟩ :=
    AutoPromoteTargets.mem_not_eq_of_false ts e hf
  ihave #Pmem : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  ihave #Ptyp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Perr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Pprom : isPkgInit (PROP := IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus $$ []
  · iPkgInit
  wp_auto
  wp_apply (hLg s lg) $$ [Hlr] as ⟨%_, Hlr⟩
  · iframe #; iframe Hlr; ipureintro; exact Hlgnn
  wp_apply HWithRoot $$ []
  wp_apply hMem1 $$ [$Pmem] as %sl ⟨Hsl, Hid, Hil⟩
  ihave %Hsll := ownSlice_len $$ Hsl
  simp only [List.length_singleton] at Hsll
  ihave IH : iprop(∃ (n : w64) (x : Loc),
      "i" ∷ i_ptr ↦ n ∗ "m" ∷ m_ptr ↦ x ∗
      "s" ∷ s_ptr ↦ s ∗ "lg" ∷ lg_ptr ↦ lg ∗ "ctx" ∷ ctx_ptr ↦ rctx ∗
      "Hsl" ∷ sl ↦* [m0] ∗ "Hid" ∷ membership.mIDAddr m0 ↦ id ∗
      "Hil" ∷ membership.mIsLearnerAddr m0 ↦ true ∗
      "HPQ" ∷ (if sint.Z n = 0 then P else Q) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ 1⌝)
    $$ [i m s lg ctx Hsl Hid Hil HP]
  · iexists W64 0, zero_val Loc
    simp only [named, show sint.Z (W64 0) = 0 from rfl, ↓reduceIte]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have hn0 : sint.Z n = 0 := by word
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, Hif⟩
    rw [ite_eq_left Hbnd, ite_eq_left hn0]
    wp_apply wp_load_slice_index sl (sint.Z n) [m0] (DFrac.own 1) m0 Hn.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; rw [hn0]; rfl
    (try wp_auto)
    wp_apply hProm1 $$ [] as %sl_p -
    (try wp_auto)
    wp_apply (wp_Is_leaf hIs e ts.idNotFound hl hp1) $$ [$Perr]
    wp_if_destruct
    · exfalso; exact hn1 Hif
    wp_apply (wp_Is_leaf hIs e ts.notLearner hl hp2) $$ [$Perr]
    wp_if_destruct
    · exfalso; exact hn2 Hif
    wp_apply (wp_Is_leaf hIs e ts.canceled hl hp3) $$ [$Perr]
    wp_if_destruct
    · exfalso; exact hn3 Hif
    wp_apply (wp_Is_leaf hIs e ts.stopped hl hp4) $$ [$Perr]
    wp_if_destruct
    · exfalso; exact hn4 Hif
    wp_apply (wp_Is_leaf hIs e ts.timeoutWaitApplied hl hp5) $$ [$Perr]
    wp_if_destruct
    · exfalso; exact hn5 Hif
    wp_apply (wp_Is_leaf hIs e ts.timeout hl hp6) $$ [$Perr]
    wp_if_destruct
    · exfalso; exact hn6 Hif
    wp_apply (wp_Is_leaf hIs e ts.leaderChanged hl hp7) $$ [$Perr]
    wp_if_destruct
    · exfalso; exact hn7 Hif
    wp_apply (wp_Is_leaf hIs e ts.notLeader hl hp8) $$ [$Perr]
    wp_if_destruct
    · exfalso; exact hn8 Hif
    wp_apply (wp_Is_leaf hIs e ts.notEnoughStarted hl hp9) $$ [$Perr]
    wp_if_destruct
    · exfalso; exact hn9 Hif
    wp_apply (wp_Is_leaf hIs e ts.learnerNotReady hl hp10) $$ [$Perr]
    wp_if_destruct
    · exfalso; exact hn10 Hif
    (try wp_auto)
    wp_apply hErrMsg $$ []
    wp_apply wp_slice_literal (V := GoString) [msg]
    isplitr
    · ipureintro; rfl
    iintro %lvs ⟨Hlvs, -⟩
    (try wp_auto)
    wp_apply hCV cvFail _ [go!"ReasonForFailure"] _ _ $$ [Hlvs]
      as %c ⟨%ci, %Hci, #HciSpec, -⟩
    · iframe #; iframe Hlvs
      ipureintro
      exact ⟨HcvLbl, prometheus.labelValuesOk_one msg go!"ReasonForFailure" hutf⟩
    subst Hci
    (try wp_auto)
    iunfold prometheus.counterSpec at HciSpec
    wp_apply HciSpec $$ []
    (try wp_auto)
    wp_apply (hIDSp (membership.mIDAddr m0) (DFrac.own 1) id) $$ [Hid] as %lstr ⟨Hid, -⟩
    · iframe #; iframe Hid
    wp_apply hZS as %f1 -
    (try wp_auto)
    wp_apply hZE as %f2 -
    (try wp_auto)
    zap_fields
    wp_apply (hWarnP _) $$ [HPQ] as HQ
    · iframe #; iframe HPQ; ipureintro; exact Hlgnn
    (try wp_auto)
    wp_for_post
    iframe
    iexists n + W64 1, m0
    have hn1' : sint.Z (n + W64 1) ≠ 0 := by word
    simp only [named, hn1', ↓reduceIte]
    iframe
    ipureintro; constructor <;> word
  · have hn1' : sint.Z n ≠ 0 := by word
    rw [ite_eq_right hn1']
    (try wp_auto)
    iapply HΦ
    iframe Hlr HPQ

end proof

end EtcdGrove
end Perennial
