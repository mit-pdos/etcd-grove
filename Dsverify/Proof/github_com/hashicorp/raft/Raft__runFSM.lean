/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__runFSM.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).runFSM`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__runFSM
public import Dsverify.Spec.github_com.hashicorp.raft.deferError__respond
public import Dsverify.Proof.github_com.hashicorp.raft.DeferRespond
public import Dsverify.Proof.github_com.hashicorp.raft.FsmBase
public import Dsverify.Proof.github_com.hashicorp.raft.FutBase
public import Dsverify.Proof.github_com.hashicorp.raft.gprot.Snap
public import Dsverify.Proof.github_com.hashicorp.raft.InstallBase
public import Dsverify.Proof.github_com.hashicorp.raft.SnapFut
public import Dsverify.Spec.github_com.hashicorp.raft.fsmRestoreAndMeasure
public import Dsverify.Spec.github_com.hashicorp.raft.DecodeConfiguration

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft proto gprot github_com.hashicorp.raft.fsmProof

namespace github_com.hashicorp.raft.fsmProof

/-- The FSM goroutine's last applied command `k0` (`0`: none) has a (persistent) response fact. -/
def lastR (rc : RCtx GF) (k0 : Nat) : IProp GF :=
  iprop(⌜k0 = 0⌝ ∨ ∃ r : GoInterface, □ rc.respP k0 r)

instance lastR_persistent rc k0 : Persistent (lastR (GF := GF) rc k0) := by
  unfold lastR; infer_instance

/-- (stage 3) What the FSM goroutine's `lastIndex`/`lastTerm` mean: nothing applied yet, or the end of
an item it processed (`batchEnd`), a committed entry of that term, past the last command `k0`. -/
def lastF (γ : GNames) (rc : RCtx GF) (k0 : Nat) (li lt : w64) : IProp GF :=
  iprop(⌜li = W64 0⌝ ∨ (⌜k0 ≤ uint.nat li ∧ 1 ≤ uint.nat li⌝ ∗ (∃ m, batchEnd rc m (uint.nat li)) ∗
    ∃ e : Entry, CIdx γ (uint.nat li) e ∗ ⌜e.term = uint.nat lt⌝))

instance lastF_persistent γ rc k0 li lt : Persistent (lastF (GF := GF) γ rc k0 li lt) := by
  unfold lastF; infer_instance

theorem noCmdBetween_prefix (γ : GNames) (k0 a b : Nat) (h1 : k0 < b) (h : b ≤ a) :
    noCmdBetween (GF := GF) γ k0 a ⊢ noCmdBetween γ k0 b := by
  unfold noCmdBetween
  have : a - (k0 + 1) = (b - (k0 + 1)) + (a - b) := by omega
  rw [this, ← List.range'_append]
  iintro H
  ihave ⟨H1, -⟩ := BigSepL.bigSepL_append.1 $$ H
  iexact H1

theorem itemRes_CIdx (γ : GNames) (rc : RCtx GF) (i : SID) (it : BatchItem) :
    itemRes (GF := GF) γ rc i it ⊢ CIdx γ it.k it.e := by
  simp only [itemRes]
  iintro ⟨-, -, #HC, -⟩
  iexact HC

/-- `fsmAt` from the loop's last-command fact (`iface.fsmAt_intro`). -/
theorem fsmAt_of_lastR (γ : GNames) (rc : RCtx GF) (i : SID) (k0 s : Nat) (h : k0 ≤ s) :
    lastR rc k0 ∗ noCmdBetween γ k0 (s + 1) ∗ durLb γ i s ⊢ fsmAt γ rc.respP i s := by
  unfold lastR
  iintro ⟨#HR, #Hnc, #Hd⟩
  icases HR with (%H0 | ⟨%r, #Hr⟩)
  · iapply github_com.hashicorp.raft.fsmAt_intro γ rc.respP i k0 s interface.nil h
    iframe #
    ileft; ipureintro; exact H0
  · iapply github_com.hashicorp.raft.fsmAt_intro γ rc.respP i k0 s r h
    iframe #

instance barrierDisp_persistent γ i sc b e : Persistent (barrierDisp (GF := GF) γ i sc b e) := by
  unfold barrierDisp; infer_instance

instance verifyItem_persistent γ i sc a : Persistent (verifyItem (GF := GF) γ i sc a) := by
  unfold verifyItem; infer_instance

/-- The barrier bound at the FSM goroutine: the committed barrier `e` at `b` (dispatched after the
client's snapshot `sc`, `barrierDisp`) is above every voter's durable prefix at `sc`
(`gprot.barrier_bound`). -/
theorem barrier_voters (γ : GNames) (i : SID) (sc : Snap) (b : Nat) (e : Entry) :
    Inv (GF := GF) γ ∗ barrierDisp γ i sc b e ∗ CIdx γ b e ⊢ |={⊤}=>
      ⌜∀ i' ∈ γ.srvs, sc.dur i' < b⌝ := by
  unfold barrierDisp
  iintro ⟨#HInv, ⟨%n0, %st, -, -, -, #Hsc, %Hd⟩, #HC⟩
  iapply barrier_bound γ ⊤ (by simp) sc b e Hd.2.1 $$ [$HInv $Hsc $HC]

end github_com.hashicorp.raft.fsmProof

theorem github_com.hashicorp.raft.Raft.runFSM.wp_proof
    (wp_respond : github_com.hashicorp.raft.deferError.respond.spec (GF := GF) (hG := hG))
    (wp_fsmRestoreAndMeasure :
      github_com.hashicorp.raft.fsmRestoreAndMeasure.spec (GF := GF) (hG := hG))
    (wp_DecodeConfiguration : github_com.hashicorp.raft.DecodeConfiguration.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.runFSM.spec (GF := GF) (hG := hG) :=
  fun r γ rc i tid => by
  wp_start as ⟨#Hr, Hcons, Htok⟩
  ihave #Hfsm := isRaft_fsm r γ rc i $$ Hr
  icases Hfsm with ⟨%fx, #Hfx, #HisFSM, %Hnb⟩
  ihave #HF := HisFSM
  iunfold isFSM at HF
  icases HF with ⟨#HPers, -, #HApply, #HSnap, #HRestore, #HStore⟩
  ihave %Hcv := isRaft_cv r γ rc i $$ Hr
  wp_auto
  unfold fsmNotBatching at Hnb
  simp only [Hnb.1]
  wp_auto
  -- (stage 4) the FSM may be a `ConfigurationStore` (`cs`)
  generalize hcs : go.typeSetContains fx.ty ConfigurationStore.ty = cs at *
  rw [show (if cs = true then #(GoInterface.ok fx) else #GoInterface.nil : val) =
    #(if cs = true then GoInterface.ok fx else GoInterface.nil) by split <;> rfl]
  wp_auto_lc 2
  ipersist r
  ipersist configStoreEnabled
  ipersist configStore
  ihave #Hpv := isRaft_proto r γ rc i $$ Hr
  icases Hpv with ⟨#HInv, -⟩
  ihave ⟨%asf, applySingle, #HAS⟩ : (∃ fv : GoFunc, applySingle_ptr ↦ fv ∗
      □ (∀ (it : BatchItem) (k0 : Nat) (li lt : w64) (Ψ : val → IProp GF),
          ⌜k0 < it.k⌝ -∗ itemRes γ rc i it -∗ rc.fsmOwn k0 -∗ lastR rc k0 -∗ noCmdBetween γ k0 it.k -∗
          lastIndex_ptr ↦ li -∗ lastTerm_ptr ↦ lt -∗
          ▷ (∀ k0' : Nat, rc.fsmOwn k0' -∗ lastR rc k0' -∗ noCmdBetween γ k0' (it.k + 1) -∗ ⌜k0' ≤ it.k⌝ -∗
              ((⌜it.e.kind = kConfig ∧ k0' = k0 ∧ cs = false⌝ ∗ lastIndex_ptr ↦ li ∗ lastTerm_ptr ↦ lt) ∨
               (∃ wi wt : w64, lastIndex_ptr ↦ wi ∗ lastTerm_ptr ↦ wt ∗
                 ⌜uint.nat wi = it.k ∧ uint.nat wt = it.e.term⌝)) -∗ Ψ #()) -∗
          WP (App (Val #fv) (Val #it.tp)) {{ Ψ }}) : IProp GF) $$ [applySingle]
  · iexists _
    isplitl [applySingle]
    · iexact applySingle
    imodintro
    iintro %it %k0 %li %lt %Ψ %Hk0 Hit Hown #HR Hnc Hli Hlt HΨ
    simp only [itemRes]
    icases Hit with ⟨#Htp, #Hlp, #HC, #Hdl, %Hkind, Hfp⟩
    ihave #Hlp2 := Hlp
    iunfold logPtr at Hlp2
    icases Hlp2 with ⟨%lv, #Hlv, #Hlogis⟩
    iunfold logIs at Hlogis
    icases Hlogis with ⟨%Hlvs, #Hdata, #Hext⟩
    iStructNamed Htp
    iStructNamed Hlv
    wp_auto
    wp_apply wp_with_defer as %defer Hdefer
    have hT : (lv.Type' = W8 0 ∧ it.e.kind = kCommand) ∨ (lv.Type' = W8 5 ∧ it.e.kind = kConfig) ∨
        (lv.Type' = W8 4 ∧ it.e.kind = kBarrier) := by
      obtain ⟨-, -, h⟩ := Hlvs
      unfold kCommand kConfig kBarrier at Hkind ⊢
      rcases Hkind with h' | h' | h' <;> rw [h'] at h
      · left; exact ⟨by word, h'⟩
      · right; left; exact ⟨by word, h'⟩
      · right; right; exact ⟨by word, h'⟩
    rcases hT with ⟨hT, hk⟩ | ⟨hT, hk⟩ | ⟨hT, hk⟩ <;> simp only [hT]
    · -- a command: apply it
      wp_auto
      wp_apply HApply $$ %it.lp %k0 %it.k %it.e Hown Hlp [] HC Hdl Hnc as %resp Hown Hresp
      · ipureintro; exact ⟨Hk0, hk⟩
      ihave #Hresp := HPers $$ %it.k %resp Hresp
      ihave #HR' : lastR rc it.k $$ []
      · unfold lastR; iright; iexists resp; iexact Hresp
      ihave #Hself := noCmdBetween_self (GF := GF) γ it.k
      by_cases hfp : it.fp = null
      · simp only [hfp, _root_.decide_true, Bool.not_true]
        wp_auto
        iapply HΨ $$ Hown HR' Hself [] [Hli Hlt]
        · ipureintro; exact Nat.le_refl _
        · iright
          iexists _, _; iframe Hli Hlt; ipureintro; exact ⟨Hlvs.1, Hlvs.2.1⟩
      · icases Hfp with (%Hn | ⟨%Hlpf, Hfr⟩)
        · exact absurd Hn hfp
        iunfold futResp at Hfr
        icases Hfr with ⟨-, ⟨%v0, Hrv⟩, Hdr⟩
        icases Hdr with (⟨%Hkn, -⟩ | Hdr)
        · exfalso; rw [hk] at Hkn; exact absurd Hkn (by decide)
        icases Hdr with (⟨%d, %n, %Hdk, Hdr⟩ | ⟨%sc, %Hkb, -⟩ | ⟨%Hkc, -⟩)
        rotate_left
        · exfalso; rw [hk] at Hkb; exact absurd Hkb (by decide)
        · exfalso; rw [hk] at Hkc; exact absurd Hkc (by decide)
        simp only [decide_eq_false hfp, Bool.not_false]
        wp_auto
        wp_apply (deferError.respond_logFuture wp_respond) it.fp (futQ γ rc it.fp d n) interface.nil $$ [Hdr Hresp Hrv] as -
        · ileft
          iframe Hdr
          unfold futQ
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists it.k, it.e, resp
          iframe HC Hresp Hrv
          ipureintro; exact Hdk
        iapply HΨ $$ Hown HR' Hself [] [Hli Hlt]
        · ipureintro; exact Nat.le_refl _
        · iright
          iexists _, _; iframe Hli Hlt; ipureintro; exact ⟨Hlvs.1, Hlvs.2.1⟩
    · -- a configuration entry (stage 4): stored if the FSM is a `ConfigurationStore` (`cs`), else
      -- not applied (`lastIndex`/`lastTerm` unchanged); its future, if any, is answered `nil`
      ihave #Hnc' : noCmdBetween γ k0 (it.k + 1) $$ [Hnc]
      · iapply noCmdBetween_snoc γ k0 it.k Hk0
        iframe Hnc
        iexists it.e
        iframe HC
        ipureintro; rw [hk]; decide
      cases cs
      · wp_auto
        by_cases hfp : it.fp = null
        · simp only [hfp, _root_.decide_true, Bool.not_true]
          wp_auto
          iapply HΨ $$ Hown HR Hnc' [] [Hli Hlt]
          · ipureintro; omega
          · ileft; iframe Hli Hlt; ipureintro; exact ⟨hk, by trivial, by trivial⟩
        · icases Hfp with (%Hn | ⟨%Hlpf, Hfr⟩)
          · exact absurd Hn hfp
          iunfold futResp at Hfr
          icases Hfr with ⟨-, ⟨%v0, Hrv⟩, Hdr⟩
          icases Hdr with (⟨%Hkn, -⟩ | ⟨%d, %n, %Hdk, -⟩ | ⟨%sc, %Hkb, -⟩ | ⟨%Hkc, Hdr⟩)
          · exfalso; rw [hk] at Hkn; exact absurd Hkn (by decide)
          · exfalso; rw [hk] at Hdk; exact absurd Hdk.1 (by decide)
          · exfalso; rw [hk] at Hkb; exact absurd Hkb (by decide)
          simp only [decide_eq_false hfp, Bool.not_false]
          wp_auto
          wp_apply (deferError.respond_logFuture wp_respond) it.fp cfgChangeQ interface.nil $$ [Hdr] as -
          · ileft; iframe Hdr; unfold cfgChangeQ; ileft; ipureintro; rfl
          iapply HΨ $$ Hown HR Hnc' [] [Hli Hlt]
          · ipureintro; omega
          · ileft; iframe Hli Hlt; ipureintro; exact ⟨hk, by trivial, by trivial⟩
      · imod snapProof.CIdx_config γ ⊤ (by simp) it.k it.e Hcv $$ [$HInv $HC] with %Hcfg
        obtain ⟨ss, Hdat, Hss⟩ := Hcfg hk
        rw [Hdat]
        ihave HSt := HStore $$ []
        · ipureintro; rfl
        have hidx : lv.Index' = W64 (it.k : Int) := by rw [← Hlvs.1]; word
        wp_auto
        wp_apply wp_DecodeConfiguration $$ [$Hdata] as %c ⟨-, Hc⟩
        rw [hidx]
        wp_apply HSt $$ %k0 %it.k %it.e %c %ss Hown [] HC Hdl Hc as Hown
        · ipureintro; exact ⟨Hk0, hk, Hdat, Hss⟩
        by_cases hfp : it.fp = null
        · simp only [hfp, _root_.decide_true, Bool.not_true]
          wp_auto
          iapply HΨ $$ Hown HR Hnc' [] [Hli Hlt]
          · ipureintro; omega
          · iright
            iexists _, _; iframe Hli Hlt; ipureintro; exact ⟨by rw [← hidx]; exact Hlvs.1, Hlvs.2.1⟩
        · icases Hfp with (%Hn | ⟨%Hlpf, Hfr⟩)
          · exact absurd Hn hfp
          iunfold futResp at Hfr
          icases Hfr with ⟨-, ⟨%v0, Hrv⟩, Hdr⟩
          icases Hdr with (⟨%Hkn, -⟩ | ⟨%d, %n, %Hdk, -⟩ | ⟨%sc, %Hkb, -⟩ | ⟨%Hkc, Hdr⟩)
          · exfalso; rw [hk] at Hkn; exact absurd Hkn (by decide)
          · exfalso; rw [hk] at Hdk; exact absurd Hdk.1 (by decide)
          · exfalso; rw [hk] at Hkb; exact absurd Hkb (by decide)
          simp only [decide_eq_false hfp, Bool.not_false]
          wp_auto
          wp_apply (deferError.respond_logFuture wp_respond) it.fp cfgChangeQ interface.nil $$ [Hdr] as -
          · ileft; iframe Hdr; unfold cfgChangeQ; ileft; ipureintro; rfl
          iapply HΨ $$ Hown HR Hnc' [] [Hli Hlt]
          · ipureintro; omega
          · iright
            iexists _, _; iframe Hli Hlt; ipureintro; exact ⟨by rw [← hidx]; exact Hlvs.1, Hlvs.2.1⟩
    · -- a barrier: not applied; its future (a client's `Barrier`) is answered with `fsmAt`
      wp_auto
      ihave #Hnc' : noCmdBetween γ k0 (it.k + 1) $$ [Hnc]
      · iapply noCmdBetween_snoc γ k0 it.k Hk0
        iframe Hnc
        iexists it.e
        iframe HC
        ipureintro; rw [hk]; decide
      by_cases hfp : it.fp = null
      · simp only [hfp, _root_.decide_true, Bool.not_true]
        wp_auto
        iapply HΨ $$ Hown HR Hnc' [] [Hli Hlt]
        · ipureintro; omega
        · iright
          iexists _, _; iframe Hli Hlt; ipureintro; exact ⟨Hlvs.1, Hlvs.2.1⟩
      · icases Hfp with (%Hn | ⟨%Hlpf, Hfr⟩)
        · exact absurd Hn hfp
        iunfold futResp at Hfr
        icases Hfr with ⟨-, ⟨%v0, Hrv⟩, Hdr⟩
        icases Hdr with (⟨%Hkn, -⟩ | ⟨%d, %n, %Hdk, -⟩ | ⟨%sc, %Hkb, #Hdisp, Hdr⟩ | ⟨%Hkc, -⟩)
        · exfalso; rw [hk] at Hkn; exact absurd Hkn (by decide)
        · exfalso; rw [hk] at Hdk; exact absurd Hdk.1 (by decide)
        rotate_left
        · exfalso; rw [hk] at Hkc; exact absurd Hkc (by decide)
        simp only [decide_eq_false hfp, Bool.not_false]
        ihave #Hdisp2 := Hdisp
        imod barrier_voters γ i sc it.k it.e $$ [$HInv $Hdisp2 $HC] with %Hvb
        ihave Hfa := fsmAt_of_lastR γ rc i k0 it.k (by omega) $$ [$HR $Hnc' $Hdl]
        wp_auto
        wp_apply (deferError.respond_logFuture wp_respond) it.fp (barrierQ γ rc i sc) interface.nil $$ [Hdr Hfa] as -
        · ileft
          iframe Hdr
          unfold barrierQ
          iright
          isplitr
          · ipureintro; rfl
          iunfold barrierDisp at Hdisp
          icases Hdisp with ⟨%n0, %st, #Hl, #Hl0, #Hst, -, %Hd⟩
          unfold barrierOk
          iexists it.e.term, n0, it.k, it.k, st
          iframe #
          iframe Hfa
          ipureintro
          exact ⟨Hd.2.2.1, Hd.2.2.2, Hd.1, Nat.le_refl _, Hvb⟩
        iapply HΨ $$ Hown HR Hnc' [] [Hli Hlt]
        · ipureintro; omega
        · iright
          iexists _, _; iframe Hli Hlt; ipureintro; exact ⟨Hlvs.1, Hlvs.2.1⟩
  ihave #Hchans := isRaft_fsmCh r γ rc i $$ Hr
  icases Hchans with ⟨%fch, #Hfch, #Hspsc⟩
  ihave #Hsd := isRaft_shutdownCh r γ rc i $$ Hr
  unfold deadField deadChan
  icases Hsd with ⟨%sch, #Hsch, %γs, #Hsbag⟩
  ihave ⟨%snch, %γsn, #Hsnch, #Hsnbag⟩ := isRaft_fsmSnapshotCh r γ rc i $$ Hr
  unfold fsmCons
  icases Hcons with ⟨Hcons, Hown⟩
  ihave #Hself0 := noCmdBetween_self (GF := GF) γ 0
  ihave HI : (∃ (received : List GoInterface) (k0 eL : Nat),
      "Hcons" ∷ spscConsumer rc.names.fsmCh received ∗ "Hown" ∷ rc.fsmOwn k0 ∗
      "Hnc" ∷ noCmdBetween γ k0 (eL + 1) ∗ "%Hk0" ∷ ⌜k0 ≤ eL⌝ ∗ "HR" ∷ lastR rc k0 ∗
      "Hend" ∷ (⌜received = [] ∧ eL = 0⌝ ∨ ⌜received ≠ []⌝ ∗ batchEnd rc (received.length - 1) eL) ∗
      "Hli" ∷ (∃ li lt : w64, lastIndex_ptr ↦ li ∗ lastTerm_ptr ↦ lt ∗ lastF γ rc k0 li lt ∗
        ⌜uint.nat li ≤ eL⌝) ∗
      "Hlc1" ∷ £ 1 ∗ "Hlc2" ∷ £ 1 : IProp GF)
      $$ [Hcons Hown lastIndex lastTerm Hlc1 Hlc2]
  · iexists [], 0, 0
    iframe Hlc1 Hlc2
    iframe Hcons Hown Hself0
    isplitr
    · ipureintro; exact Nat.le_refl _
    isplitr
    · unfold lastR; ileft; ipureintro; rfl
    isplitr
    · ileft; ipureintro; exact ⟨rfl, rfl⟩
    iexists _, _
    iframe lastIndex lastTerm
    isplitr
    · unfold lastF; ileft; ipureintro; rfl
    ipureintro; exact Nat.le_of_eq (by rfl)
  wp_for HI
  icases HR with #HR
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- a batch from the main goroutine
    dsimp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, fch,
      rc.names.fsmCh.chanName
    isplitr
    · ipureintro; rfl
    ihave #Hch : isChan fch rc.names.fsmCh.chanName GoInterface $$ [Hspsc]
    · unfold isSpsc; icases Hspsc with ⟨$, -⟩
    iframe Hch
    iapply spsc_rcv_au $$ Hspsc [$Hlc1 $Hlc2] Hcons
    inext
    iintro %v %ok Hv
    cases ok
    · -- closed: never (the close predicate is `False`)
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hv with ⟨HF, -⟩
      iexfalso; iexact HF
    simp only [↓reduceIte]
    icases Hv with ⟨Hv, Hcons⟩
    unfold fsmP
    icases Hv with ⟨%kb, %k1, %-, Hst, #Hend1, Hb⟩
    simp only [Int.toNat_natCast]
    -- the batch starts where the previous one ended
    ihave %Hkb : ⌜kb = eL⌝ $$ [Hst Hend]
    · unfold batchStart
      icases Hst with (%Hs | ⟨%m, %Hm, #Hst⟩)
      · obtain ⟨Hs1, Hs2⟩ := Hs
        icases Hend with (%He | ⟨%Hne, -⟩)
        · ipureintro; omega
        · exfalso; exact Hne (List.length_eq_zero_iff.mp Hs1)
      · icases Hend with (%He | ⟨%Hne, #Hend⟩)
        · exfalso; rw [He.1] at Hm; simp at Hm
        · rw [show received.length - 1 = m by omega]
          iapply (batchEnd_agree rc m kb eL)
          iframe #
    subst Hkb
    icases Hb with (Hb | ⟨%Hk1, Hvf⟩ | Hrest)
    rotate_left
    rotate_left
    · -- a restore future (installSnapshot): open the install's snapshot, restore the FSM from it
      unfold fsmRestoreP
      icases Hrest with ⟨%f, %sid, %st, %Hv, #HID, ⟨%e, #HCe, %Hee⟩, Hpnd, Hdr⟩
      obtain ⟨Hv, Hks⟩ := Hv
      subst Hv
      wp_auto_lc 2
      wp_bind
      iapply wp_with_defer
      iintro %defer Hdefer
      icases Hli with ⟨%li, %lt, Hli, Hlt, -, -⟩
      ihave ⟨%ssx, %eof, #Hssf, #HSS, #Heof⟩ := isRaft_snapshotStore r γ rc i $$ Hr
      ihave #Hsc := isRaft_snapCell r γ rc i $$ Hr
      unfold isSnapStore
      icases HSS with ⟨-, -, #HOpen⟩
      wp_auto
      wp_bind
      iapply HOpen $$ %sid %tid %_ Htok
      iapply (snapProof.restore_open γ rc i fx k1 st sid eof _)
      iframe Hsc HisFSM Hpnd
      iintro %m %b %mp %rd %R %Hm Hmp #Hrc HRb HsPb Hpnd Htok
      obtain ⟨HmI, HmT, Hk11⟩ := Hm
      wp_auto
      wp_apply wp_fsmRestoreAndMeasure fx γ i rc.fsmOwn rc.respP rc.snapP k0 k1 rd R b eof m.Size'
        $$ [$HisFSM $Hown $Heof $Hrc $HRb $HsPb] as ⟨%k0', %r', Hown, %Hk0', #Hnc', Hr'⟩
      · ipureintro; omega
      wp_apply snapFut.wp_rf_respond wp_respond f (restoreQ rc k1 st sid) interface.nil
        $$ [Hdr Hpnd] as -
      · ileft; iframe Hdr; unfold restoreQ; iframe; ipureintro; rfl
      ihave #Hrc' := Hrc
      unfold readCloserOk
      icases Hrc' with ⟨-, #HClose⟩
      try wp_auto
      wp_apply HClose
      try wp_auto
      ihave #HR' : lastR rc k0' $$ [Hr']
      · unfold lastR
        icases Hr' with (%H | Hr')
        · ileft; ipureintro; exact H
        · iright; iexists r'; iapply HPers $$ %k0' %r' Hr'
      wp_for_post
      iframe
      iexists received ++ [interface.mkOk (go.GoType.PointerType restoreFuture.ty) #f], k0', k1
      iframe
      iframe #
      isplitr
      · ipureintro; exact Hk0'
      isplitr
      · iright
        simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
        iframe #
        ipureintro; simp
      iexists m.Index', m.Term'
      iframe Hli Hlt
      rw [HmI]
      isplitr
      · unfold lastF; iright
        rw [HmI]
        isplitr
        · ipureintro; exact ⟨Hk0', Hk11⟩
        isplitl
        · iexists received.length; iexact Hend1
        iexists e; iframe HCe; ipureintro; rw [HmT]; exact Hee
      ipureintro; exact Nat.le_refl _
    rotate_left
    · -- a verify future (fix `ea6e596`): sent after the batches up to `kb`, all processed; answered
      -- with `fsmAt` for what the main goroutine had handed to the FSM (`a ≥ kb`)
      unfold fsmVerifyP
      icases Hvf with ⟨%vf, %Hv, Hvf⟩
      subst Hv
      subst k1
      wp_auto_lc 2
      icases Hnc with #Hnc
      icases Hvf with (⟨%sc, %a, %Ha, #Hnca, #Hda, #Hvi, Hdr⟩ | Hdone)
      · ihave #Hnc2 := noCmdBetween_app γ k0 kb (a + 1) Hk0 (by omega) $$ [$Hnc $Hnca]
        ihave Hfa := fsmAt_of_lastR γ rc i k0 a (by omega) $$ [$HR $Hnc2 $Hda]
        wp_apply futProof.wp_vf_respond vf (verifyQ γ rc i sc) interface.nil $$ [Hdr Hfa] as -
        · ileft; iframe Hdr
          unfold verifyQ; iright; isplitr
          · ipureintro; rfl
          unfold verifyOk; iexists a; iframe #; iframe Hfa
        wp_for_post
        iframe
        iexists received ++ [interface.mkOk (go.GoType.PointerType verifyFuture.ty) #vf], k0, kb
        iframe
        iframe #
        isplitr
        · ipureintro; exact Hk0
        iright
        simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
        iframe #
        ipureintro; simp
      · wp_apply futProof.wp_vf_respond vf (fun _ => iprop(True)) interface.nil $$ [Hdone] as -
        · iright; iexact Hdone
        wp_for_post
        iframe
        iexists received ++ [interface.mkOk (go.GoType.PointerType verifyFuture.ty) #vf], k0, kb
        iframe
        iframe #
        isplitr
        · ipureintro; exact Hk0
        iright
        simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
        iframe #
        ipureintro; simp
    unfold fsmBatchP
    icases Hb with ⟨%sl, %items, %Hv, #Hsl, %Hitems, Hits, Hcov⟩
    subst Hv
    wp_auto_lc 2
    obtain ⟨Hne, Hpw, Hrng, Hlast⟩ := Hitems
    ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
    simp only [List.length_map] at Hlen
    have Hkb1 : kb ≤ k1 := by
      obtain ⟨it0, hit0⟩ := List.exists_mem_of_ne_nil items Hne
      have := Hrng it0 hit0; omega
    ihave HJ : (∃ (j : w64) (k0' p : Nat) (ctv : Loc),
        "i" ∷ i_ptr ↦ j ∗ "ct" ∷ ct_ptr ↦ ctv ∗ "Hown" ∷ rc.fsmOwn k0' ∗
        "Hnc" ∷ noCmdBetween γ k0' (p + 1) ∗ "HR" ∷ lastR rc k0' ∗
        "Hits" ∷ ([∗list] it ∈ items.drop (sint.nat j), itemRes γ rc i it) ∗
        "Hcov" ∷ coverRest γ p k1 (items.drop (sint.nat j)) ∗
        "Hli" ∷ (∃ li lt : w64, lastIndex_ptr ↦ li ∗ lastTerm_ptr ↦ lt ∗
          (⌜li = W64 0⌝ ∨ (⌜k0' ≤ uint.nat li ∧ 1 ≤ uint.nat li ∧ uint.nat li ≤ p⌝ ∗
            (∃ e : Entry, CIdx γ (uint.nat li) e ∗ ⌜e.term = uint.nat lt⌝) ∗
            (⌜uint.nat li = p⌝ ∨ ∃ m, batchEnd rc m (uint.nat li))))) ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len ∧ k0' ≤ p ∧ p ≤ k1 ∧
          (∀ it ∈ items.drop (sint.nat j), p < it.k) ∧
          ((items.take (sint.nat j)).getLast?.map BatchItem.k = some p ∨ (sint.nat j = 0 ∧ p = kb))⌝
        : IProp GF) $$ [i ct Hown Hnc Hits Hcov Hli]
    · icases Hli with ⟨%li, %lt, Hli, Hlt, #Hlf, %Hle⟩
      iexists W64 0, k0, kb, _
      iframe
      simp only [show sint.nat (W64 0) = 0 from rfl, List.drop_zero, List.take_zero]
      iframe
      unfold coverRest
      iframe
      iframe #
      isplitl [Hli Hlt]
      · iexists li, lt; iframe Hli Hlt
        unfold lastF
        icases Hlf with (%H0 | ⟨%Hlx, ⟨%m, #Hbm⟩, #HCl⟩)
        · ileft; ipureintro; exact H0
        · iright; isplitr
          · ipureintro; omega
          iframe HCl; iright; iexists m; iexact Hbm
      ipureintro
      refine ⟨by word, by word, Hk0, Hkb1, fun it h => (Hrng it h).1, Or.inr ⟨by simp, trivial⟩⟩
    wp_for HJ
    icases HR with #HR
    obtain ⟨Hj0, Hjl, Hkp, Hpk1, Hplt, Hpl⟩ := Hj
    wp_if_destruct
    · -- the next tuple
      have Hlt : sint.Z j < sint.Z sl.len := by revert Hif; simp
      simp only [Hj0, Hlt, _root_.and_self, ↓reduceIte]
      have hjn : sint.nat j < items.length := by rw [Hlen.1]; word
      obtain ⟨it, hit⟩ : ∃ it, items[sint.nat j]? = some it :=
        ⟨items[sint.nat j], List.getElem?_eq_getElem hjn⟩
      have hdrop : items.drop (sint.nat j) = it :: items.drop (sint.nat j + 1) := by
        rw [List.drop_eq_getElem_cons hjn]
        rw [List.getElem?_eq_getElem hjn] at hit
        injection hit with h; rw [h]
      wp_apply (wp_load_slice_index sl (sint.Z j) (items.map BatchItem.tp) DFrac.discard it.tp Hj0)
        $$ [Hsl] as Hsl'
      · iframe #
        ipureintro
        rw [List.getElem?_map]
        rw [show (sint.Z j).toNat = sint.nat j from rfl, hit]
        rfl
      have hitm : it ∈ items := List.mem_of_getElem? hit
      have hpit : p < it.k := Hplt it (by rw [hdrop]; exact List.mem_cons_self)
      have hitk1 : it.k ≤ k1 := (Hrng it hitm).2
      have hr := pairwise_drop_head items (sint.nat j) it _ Hpw hdrop
      rw [hdrop]
      icases BigSepL.bigSepL_cons.1 $$ Hits with ⟨Hit, Hits⟩
      icases coverRest_step γ p k1 it _ hpit hitk1 hr $$ Hcov with ⟨Hnc2, Hcov⟩
      ihave Hnc := noCmdBetween_app γ k0' p it.k Hkp hpit $$ [$Hnc $Hnc2]
      icases Hli with ⟨%li, %lt, Hli, Hlt, #Hlf⟩
      ihave #HCit := itemRes_CIdx γ rc i it $$ Hit
      wp_apply HAS $$ %it %k0' %li %lt [] Hit Hown HR Hnc Hli Hlt as %k0'' Hown #HR Hnc %Hk0'' Hres
      · ipureintro; omega
      wp_for_post
      iframe
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      iexists j + W64 1, k0'', it.k, it.tp
      rw [hj1]
      iframe
      iframe #
      isplitl [Hres]
      · icases Hres with (⟨%Hc, Hli, Hlt⟩ | ⟨%wi, %wt, Hli, Hlt, %Hw⟩)
        · obtain ⟨-, Hk00, Hcf⟩ := Hc
          iexists li, lt; iframe Hli Hlt
          icases Hlf with (%H0 | ⟨%Hlx, #HCl, (%Hlp | ⟨%m, #Hbm⟩)⟩)
          · ileft; ipureintro; exact H0
          · -- (REPL4-1) the FSM is a `ConfigurationStore` (`fsmNotBatching`): never left unchanged
            exfalso; rw [Hnb.2] at Hcf; exact absurd Hcf (by decide)
          · iright
            isplitr
            · ipureintro; omega
            iframe HCl; iright; iexists m; iexact Hbm
        · iexists wi, wt; iframe Hli Hlt
          iright
          rw [Hw.1]
          isplitr
          · ipureintro; omega
          isplitl
          · iexists it.e; iframe HCit; ipureintro; exact Hw.2.symm
          ileft; ipureintro; rfl
      ipureintro
      refine ⟨by word, by word, Hk0'', hitk1, hr, Or.inl ?_⟩
      rw [List.take_add_one, hit]
      simp
    · -- the batch is applied
      have Hge : ¬ sint.Z j < sint.Z sl.len := by revert Hif; simp
      have hjl : sint.nat j = items.length := by rw [Hlen.1]; word
      have hp : p = k1 := by
        rcases Hpl with h | ⟨h1, -⟩
        · rw [hjl, List.take_length] at h
          rw [Hlast] at h; injection h with h; omega
        · rw [h1] at hjl; exact absurd (List.length_eq_zero_iff.mp hjl.symm) Hne
      subst hp
      icases Hli with ⟨%li, %lt, Hli, Hlt, #Hlf⟩
      wp_for_post
      iframe
      iexists received ++ [batchV sl], k0', p
      iframe
      isplitr
      · ipureintro; exact Hkp
      isplitr
      · iexact HR
      isplitr
      · iright
        simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
        iframe #
        ipureintro; simp
      iexists li, lt
      iframe Hli Hlt
      unfold lastF
      icases Hlf with (%H0 | ⟨%Hlx, #HCl, (%Hlp | ⟨%m, #Hbm⟩)⟩)
      · isplitr
        · ileft; ipureintro; exact H0
        ipureintro; rw [H0]; simp
      · isplitr
        · iright; isplitr
          · ipureintro; exact ⟨Hlx.1, Hlx.2.1⟩
          isplitl
          · iexists received.length; rw [Hlp]; iexact Hend1
          iexact HCl
        ipureintro; omega
      · isplitr
        · iright; isplitr
          · ipureintro; exact ⟨Hlx.1, Hlx.2.1⟩
          isplitl
          · iexists m; iexact Hbm
          iexact HCl
        ipureintro; omega
  iapply BigAndL.bigAndL_cons.2
  isplit
  · dsimp only [chan.blockingClausePre]
    iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, snch, γsn
    isplitr
    · ipureintro; rfl
    ihave #Hsc := is_bag_is_chan _ _ _ $$ Hsnbag
    iframe Hsc
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hsnbag
    inext
    iintro %f Hf
    unfold snapReqP
    icases Hf with ⟨⟨%x0, %tx0, %sn0, index, term, snapshot⟩, Hdr⟩
    icases Hli with ⟨%li, %lt, Hli, Hlt, #Hlf, %Hle⟩
    wp_auto_lc 2
    unfold lastF
    icases Hlf with (%H0 | ⟨%Hlx, ⟨%m, #Hbm⟩, ⟨%e, #HCl, %Hel⟩⟩)
    · -- nothing applied yet
      subst H0
      wp_auto
      ihave #HnnE := isRaftErr_of_init RaftErr.nothingNewToSnapshot $$ Hpkg
      icases HnnE with ⟨%eNN, #HeNN⟩
      ihave #HgNN := isRaftErr_global RaftErr.nothingNewToSnapshot eNN $$ HeNN
      dsimp only [RaftErr.var]
      wp_auto
      wp_apply snapFut.wp_sf_respond wp_respond f (snapReqQ γ rc f) eNN $$ [Hdr index term snapshot] as -
      · ileft; iframe Hdr
        unfold snapReqQ; iright; iframe HeNN; iexists _, _, _; iframe
      wp_for_post
      iframe
      iexists received, k0, eL
      iframe
      iframe #
      isplitr
      · ipureintro; exact Hk0
      iexists (W64 0), lt; iframe Hli Hlt
      isplitr
      · ileft; ipureintro; rfl
      ipureintro; exact Hle
    · -- the FSM's state at `lastIndex`
      have hli0 : li ≠ W64 0 := by intro h; rw [h] at Hlx; simp at Hlx
      rw [decide_eq_false hli0]
      wp_auto
      ihave #Hnc2 := noCmdBetween_prefix γ k0 (eL + 1) (uint.nat li + 1) (by omega) (by omega) $$ Hnc
      ihave ⟨%r0, #Hr0⟩ : (∃ r0 : GoInterface, ⌜k0 = 0⌝ ∨ □ rc.respP k0 r0) $$ []
      · iunfold lastR at HR
        icases HR with (%H | ⟨%r0, #Hr0⟩)
        · iexists interface.nil; ileft; ipureintro; exact H
        · iexists r0; iright; iexact Hr0
      wp_bind
      iapply HSnap $$ %k0 %(uint.nat li) %r0 %_ Hown [] Hnc2 []
      · ipureintro; exact Hlx.1
      · icases Hr0 with (%H | #H)
        · ileft; ipureintro; exact H
        · iright; iexact H
      iintro %snap Hown #HsOk
      wp_auto
      have hliw : li = W64 (uint.nat li) := by word
      have hltw : lt = W64 (uint.nat lt) := by word
      wp_apply snapFut.wp_sf_respond wp_respond f (snapReqQ γ rc f) interface.nil
        $$ [Hdr index term snapshot] as -
      · ileft; iframe Hdr
        unfold snapReqQ; ileft; isplitr
        · ipureintro; rfl
        iexists (uint.nat li), (uint.nat lt), m, snap
        rw [← hliw, ← hltw]
        iframe
        iframe #
        isplitr
        · ipureintro; exact Hlx.2
        first | (iexists e; iframe HCl; ipureintro; exact Hel) | (ipureintro; exact Hel)
      wp_for_post
      iframe
      iexists received, k0, eL
      iframe
      iframe #
      isplitr
      · ipureintro; exact Hk0
      iexists li, lt; iframe Hli Hlt
      isplitr
      · iright; isplitr
        · ipureintro; exact Hlx
        isplitl
        · iexists m; iexact Hbm
        iexists e; iframe HCl; ipureintro; exact Hel
      ipureintro; exact Hle
  iapply BigAndL.bigAndL_cons.2
  isplit
  · dsimp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sch, γs
    isplitr
    · ipureintro; rfl
    ihave #Hsc := is_bag_is_chan _ _ _ $$ Hsbag
    iframe Hsc
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hsbag
    inext
    iintro %v HF
    iexfalso; iexact HF
  · iapply BigAndL.bigAndL_nil.2
    itrivial

end proof

end Perennial
