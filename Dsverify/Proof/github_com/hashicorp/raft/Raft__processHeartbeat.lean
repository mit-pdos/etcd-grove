/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__processHeartbeat.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).processHeartbeat` (fix `ae71703`): on a transport goroutine,
concurrently with the main loop. It reads the term cell (with a snapshot witness,
`gprot.termCouple_now`, later than the request's snapshot), `lastLock` and the state cell, and
changes no protocol state: a heartbeat of the current term to a follower is answered with success
(the witness is the responder's `respWit`; a heartbeat acknowledges nothing), a stale one with the
term read, any other is refused with an error.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__processHeartbeat
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__getRPCHeader
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastIndex
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getState
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setLeader
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setLastContact
public import Dsverify.Spec.github_com.hashicorp.raft.RPC__Respond
public import Dsverify.Proof.github_com.hashicorp.raft.handlers.Base
public import Dsverify.Proof.github_com.hashicorp.raft.core.Helpers
public import Dsverify.Proof.github_com.hashicorp.raft.gprot.Snap
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Spec.errors.New
public import Perennial.Spec.fmt.Errorf

@[expose] public section

set_option linter.deprecated false

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

open github_com.hashicorp.raft proto gprot

/-- **A term read with a snapshot witness** (any goroutine): `getCurrentTerm` returns `t`, an
existing term, and a snapshot later than `s0` in which `i`'s term is `t` (`termCouple_now` at the
atomic load). -/
theorem github_com.hashicorp.raft.wp_getCurrentTerm_wit (r : Loc) (γ : GNames) (i : SID)
    (s0 : Snap) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ Inv γ ∗ termCell r γ i ∗
        isSrv γ i ∗ histLb γ s0 }}
      (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"getCurrentTerm")) (Val #()))
    {{ (t : w64), RET #t; termOk γ (uint.nat t) ∗
        ∃ s', histLb γ s' ∗ ⌜snapLe s0 s' ∧ s'.term i = uint.nat t⌝ }} := by
  wp_start as ⟨#HInv, #Hcell, #Hv, #Hs0⟩
  wp_method_call; wp_call
  wp_auto
  wp_apply_core sync.atomic.wp_LoadUint64 _ (DFrac.own 1) $$ [] [-]
  · iPkgInit
  unfold termCell
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hcell with ⟨Hi, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  icases Hi with ⟨%t, Hpt, Hc⟩
  iexists t
  iframe Hpt
  iintro Hpt
  imod Hmask with -
  imod termCouple_now γ (⊤ \ ↑termN) gprotN_diff_termN i _ s0 $$ [$HInv $Hv $Hc $Hs0]
    with ⟨Hc, %s', #Hs', %Hs'⟩
  ihave ⟨Hc, #Hlb⟩ := termCouple_get_lb γ i _ $$ Hc
  imod Hclose $$ [Hpt Hc] with -
  · inext; iexists t; iframe
  imodintro
  wp_auto
  iapply HΦ
  isplitr
  · iapply termOk_of_termLb γ i _ (uint.nat t) (Nat.le_refl _) $$ [$Hv $Hlb]
  iexists s'
  iframe Hs'
  ipureintro; exact Hs'

/-- A receive clause of a nonblocking select on a dead channel. -/
theorem github_com.hashicorp.raft.dead_nb_clause_hb {V : Type} [Pos.Countable V] [ZeroVal V]
    [TypedPointsto (GF := GF) V] {t : go.GoType} [IntoValTyped (GF := GF) V t]
    (γc : ChanNames) (ch : Loc) (body : Expr) (Φ : val → IProp GF) :
    ⊢ isChanBag (V := V) γc ch (fun _ => iprop(False)) -∗
      chan.nonblockingClausePre (.CommClause (.RecvCase t (Val #ch)) body) Φ := by
  iintro #Hb
  simp only [chan.nonblockingClausePre]
  iexists V, inferInstance, inferInstance, inferInstance, inferInstance, ch, γc
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply is_bag_is_chan γc ch _ $$ Hb
  unfold nonblockingRecvAu
  isplit
  · rw [isChanBag_unseal]; unfold isChanBagDef nonblockingRecvAuInner
    icases Hb with ⟨#Hch, #Hinv⟩
    iapply ncfupd_of_fupd  -- (port) channel AUs are `|NC=…` now
    iinv Hinv with Hi Hclose
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    unfold chanBagInv
    icases Hi with ⟨%s, Hoc0, Hi⟩
    iexists s
    iframe Hoc0
    rcases s with (_ | ⟨v0, buff'⟩) | _ | v | _ | _ | _ | _
    all_goals dsimp only
    all_goals first | itrivial | (iexfalso; iexact Hi) | skip
    all_goals first | (icases BigSepL.bigSepL_cons.1 $$ Hi with ⟨HP, -⟩; iexfalso; iexact HP) | skip
  · itrivial

/-- `errors.New(msg)`'s result is an error with a callable `Error()`. -/
theorem github_com.hashicorp.raft.errOk_of_New (msg : GoString) (err : GoInterfaceOk) :
    (□ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
      WP (App (Val #(methods err.ty go!"Error" err.v)) (Val #())) {{ Φ }}) ⊢
    errOk (GoInterface.ok err) := by
  iintro #Herr
  unfold errOk
  iexists err
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %Φ HΦ
  iapply Herr
  inext
  iapply HΦ

theorem github_com.hashicorp.raft.Raft.processHeartbeat.wp_proof
    (wp_getRPCHeader : github_com.hashicorp.raft.Raft.getRPCHeader.spec (GF := GF) (hG := hG))
    (wp_getLastIndex : github_com.hashicorp.raft.raftState.getLastIndex.spec (GF := GF) (hG := hG))
    (wp_getState : github_com.hashicorp.raft.raftState.getState.spec (GF := GF) (hG := hG))
    (wp_setLeader : github_com.hashicorp.raft.Raft.setLeader.spec (GF := GF) (hG := hG))
    (wp_setLastContact : github_com.hashicorp.raft.Raft.setLastContact.spec (GF := GF) (hG := hG))
    (wp_Respond : github_com.hashicorp.raft.RPC.Respond.spec (GF := GF) (hG := hG))
    (wp_New : errors.New.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.processHeartbeat.spec (GF := GF) (hG := hG) :=
  fun r γ rc i rpc tid => by
  wp_start as ⟨#Hr, Hrpc, Htok⟩
  unfold hbRpcP
  icases Hrpc with ⟨%Hrd, %p, %rq, %snd, %T, %pt, %lci, %ss, %γc, %Hc, Hp, Hreq, %Hlci, #Hbag⟩
  unfold aeReq
  icases Hreq with ⟨%Hnums, #Hhdr, #Hlead, -, -, #Hss⟩
  obtain ⟨HTe, -, -, -⟩ := Hnums
  ihave ⟨#HI, #Hvi⟩ := isRaft_proto r γ rc i $$ Hr
  ihave #Htc := isRaft_termCell r γ rc i $$ Hr
  ihave #Hsc := isRaft_stateCell r γ rc i $$ Hr
  ihave #Hsd := isRaft_shutdownCh r γ rc i $$ Hr
  unfold deadField deadChan
  icases Hsd with ⟨%sch, #Hsch, %γsd, #Hsdb⟩
  wp_auto
  wp_apply_core chan.wp_select_nonblocking_nil
  isplit
  · iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      iapply dead_nb_clause_hb γsd sch _ _ $$ Hsdb
    iapply BigAndL.bigAndL_nil.2
    itrivial
  wp_auto
  rw [Hc]
  wp_auto
  wp_apply wp_getRPCHeader r γ rc i $$ [$Hr] as %h0 #Hh0
  wp_apply wp_getCurrentTerm_wit r γ i ss $$ [$HI $Htc $Hvi $Hss] as %t ⟨#Htok_t, %s', #Hs', %Hs'⟩
  wp_apply wp_getLastIndex.2 r γ rc i $$ [$Hr] as %li -
  ipersist Hp
  iStructNamed Hp
  ipersist cmd
  ipersist r
  wp_if_destruct
  · -- a newer term: refused
    wp_apply wp_New as %err ⟨-, #Herr⟩
    wp_apply wp_Respond rpc_ptr rpc γc _ _ _ $$ [$rpc $Hbag] as rpc
    · unfold rpcRespP; ileft
      iapply errOk_of_New $$ Herr
    wp_end
  wp_if_destruct
  · -- the current term: refused unless a follower
    wp_apply wp_getState.2 r rc $$ [$Hsc] as %st %Hst
    wp_if_destruct
    · -- a follower: success
      iStructNamed RPCHeader
      ihave ⟨%xtr, %rpcCh, #Htr, #Hrpcf, #Htrans⟩ := isRaft_transport r γ rc i $$ Hr
      unfold isTransport
      icases Htrans with ⟨-, -, -, -, #Hdec, -⟩
      unfold hdrOk
      icases Hhdr with ⟨%Hpv, #Hid, #Haddr⟩
      wp_auto
      wp_join with [Htok]
      · wp_apply Hdec $$ Haddr
        iintro Haddr'
        wp_auto
        wp_apply wp_bytes_to_string $$ Hid as Hid'
        wp_apply wp_setLeader r γ rc i _ _ $$ [$Hr $Htok] as Htok
        wp_join_done
      · wp_apply Hdec $$ Hlead
        iintro Hlead'
        wp_auto
        wp_apply wp_bytes_to_string $$ Hid as Hid'
        wp_apply wp_setLeader r γ rc i _ _ $$ [$Hr $Htok] as Htok
        wp_join_done
      wp_apply wp_setLastContact r γ rc i $$ [$Hr]
      wp_apply wp_Respond rpc_ptr rpc γc _ _ _ $$ [$rpc $Hbag «$r0»] as rpc
      · iapply aeRespP_intro $$ [$«$r0»]
        unfold hdrOk
        iframe Htok_t Hh0
        iright
        isplitr
        · ileft; ipureintro; exact ⟨rfl, rfl, Hlci⟩
        unfold respWit
        iexists s'
        iframe Hs'
        ipureintro; rw [← HTe]; exact Hs'
      wp_end
    · wp_apply wp_New as %err ⟨-, #Herr⟩
      wp_apply wp_Respond rpc_ptr rpc γc _ _ _ $$ [$rpc $Hbag] as rpc
      · unfold rpcRespP; ileft
        iapply errOk_of_New $$ Herr
      wp_end
  · -- a stale term: answered with the current term
    wp_if_destruct
    · exfalso; contradiction
    wp_apply wp_Respond rpc_ptr rpc γc _ _ _ $$ [$rpc $Hbag «$r0»] as rpc
    · iapply aeRespP_intro $$ [$«$r0»]
      iframe Htok_t Hh0
      ileft; ipureintro; rfl
    wp_end

end proof

end Perennial
