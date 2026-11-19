/-
The proofs of the rpc client's specs (`ClientDefs.lean`). The helpers `errAny_newVar`,
`errAny_ok` give an `errors.New` error's (or a decoding error's) `errAny`; `callPost_done`
turns what a call's `done` channel carries into `Call`'s postcondition.
-/
module

public import Harness.Proof.net.rpc.ClientGhost
public import Perennial.Proof.errors.New
public import Perennial.Proof.errors.NewVar
public import Harness.Proof.net.TCPConn__Write

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn

namespace net.rpc

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions] [net.rpc.Assumptions]
variable [RpcKit] [RpcCodec GF]

set_option goose.wp.extras true



theorem net_init_of_rpc :
    isPkgInit (PROP := IProp GF) pkg_id.net.rpc ⊢ isPkgInit (PROP := IProp GF) pkg_id.net := by
  refine (isPkgInit_unfold_deps (PROP := IProp GF) pkg_id.net.rpc).trans ?_
  show iprop(isPkgInit pkg_id.errors ∗ isPkgInit pkg_id.net ∗ isPkgInit pkg_id.sync ∗
    isPkgInit pkg_id.net.http ∗ True) ⊢ _
  iintro ⟨-, H, -, -, -⟩
  iexact H

theorem sync_init_of_rpc :
    isPkgInit (PROP := IProp GF) pkg_id.net.rpc ⊢ isPkgInit (PROP := IProp GF) pkg_id.sync := by
  refine (isPkgInit_unfold_deps (PROP := IProp GF) pkg_id.net.rpc).trans ?_
  show iprop(isPkgInit pkg_id.errors ∗ isPkgInit pkg_id.net ∗ isPkgInit pkg_id.sync ∗
    isPkgInit pkg_id.net.http ∗ True) ⊢ _
  iintro ⟨-, -, H, -, -⟩
  iexact H

theorem errAny_newVar (x : Loc) (msg : GoString) :
    (□ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
      WP (App (Val #(methods (go.GoType.PointerType errors.errorString.ty) go!"Error" #x))
        (Val #())) {{ Φ }}) ⊢
      errAny (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x) := by
  iintro #H
  iapply errMsg_errAny _ msg
  unfold errMsg
  iexists ⟨go.GoType.PointerType errors.errorString.ty, #x⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact errorString_isError
  iexact H

theorem errAny_ok (e : GoInterfaceOk) (msg : GoString)
    (ht : go.typeSetContains e.ty go.error = true) :
    (□ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
      WP (App (Val #(methods e.ty go!"Error" e.v)) (Val #())) {{ Φ }}) ⊢
      errAny (interface.ok e) := by
  iintro #H
  iapply errMsg_errAny _ msg
  unfold errMsg
  iexists e
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact ht
  iexact H

theorem callPost_done (Φ : List w8 → GoString → IProp GF) (Θ : List w8 → Bool → IProp GF)
    (D Rargs E : IProp GF) (err : GoInterface) :
    callPost Φ Θ D err ∗ Rargs ⊢
      (⌜err = interface.nil⌝ ∗ Rargs ∗ ∃ rep, Φ rep [] ∗ Θ rep true) ∨
      (∃ msg : GoString, ⌜msg ≠ [] ∧ err = serverErr msg⌝ ∗ errMsg err msg ∗ Rargs ∗
        (∃ rep, Φ rep msg) ∗ D) ∨
      (⌜err ≠ interface.nil ∧ notServerErr err⌝ ∗ errAny err ∗
        ((Rargs ∗ (D ∨ ∃ rep, Θ rep false)) ∨ E)) := by
  unfold callPost
  iintro ⟨(⟨%h, H⟩ | ⟨%msg, %h, #He, H1, HD⟩ | ⟨%h, #He, H⟩), HR⟩
  · ileft
    isplitr
    · ipureintro; exact h
    iframe
  · iright; ileft
    iexists msg
    isplitr
    · ipureintro; exact h
    isplitr
    · iexact He
    iframe
  · iright; iright
    isplitr
    · ipureintro; exact h
    isplitr
    · iexact He
    ileft
    iframe

theorem Client.Close.wp_proof : Client.Close.spec (GF := GF) (hG := hG) := by
  intro c W a
  wp_start as #Hcl
  unfold isClient isClientN
  icases Hcl with ⟨%cv, %cid, %γn, #Hconn, #Hci, #Hrpc, #Hsend, #Hmu, #Hinv⟩
  ihave #Hnet := net_init_of_rpc $$ Hpkg
  ihave #Hsync := sync_init_of_rpc $$ Hpkg
  wp_auto
  wp_apply sync.Mutex.Lock.wp_proof _ _ $$ [$Hsync $Hmu] as ⟨Hlk, HR⟩
  iunfold muInv at HR
  icases HR with ⟨%sq, %mp, %m, %sd, %cls, Hseq, Hpend, Hm, Hsd, Hcls, Hsdl, Hal⟩
  ihave #Hinit := net.rpc.isInit_access $$ Hpkg
  icases Hinit with ⟨#HeS, -⟩
  unfold errors.newVar
  icases HeS with ⟨%xS, #HeS, #HeSm⟩
  cases cls
  · wp_auto
    wp_apply sync.Mutex.Unlock.wp_proof _ (muInv γn c) $$ [$Hsync $Hmu $Hlk Hseq Hpend Hm Hsd Hcls Hsdl Hal]
    · unfold muInv; iexists sq, mp, m, sd, true; iframe
    unfold connIface
    icases Hci with ⟨%cc, %Hcv, #Hcc⟩
    subst Hcv
    wp_auto
    wp_apply net.TCPConn.Close.wp_proof cc cid false $$ [$Hnet $Hcc] as %err ⟨%code, -, #Herr⟩
    iapply HΦ
    icases connErr_errAny _ _ _ $$ [$Hnet $Herr] with (%h | ⟨#H, -⟩)
    · ileft; ipureintro; exact h
    · iright; iexact H
  · wp_auto
    wp_apply sync.Mutex.Unlock.wp_proof _ (muInv γn c) $$ [$Hsync $Hmu $Hlk Hseq Hpend Hm Hsd Hcls Hsdl Hal]
    · unfold muInv; iexists sq, mp, m, sd, true; iframe
    iapply HΦ; iright; iapply errAny_newVar xS _ $$ HeSm

theorem Client.Call.wp_proof (wp_getCodec : getCodec.clientSpec (GF := GF) (hG := hG))
    (wp_writeFrame : writeFrame.spec (GF := GF) (hG := hG))
    (wp_encodeMsg : encodeMsg.spec (GF := GF) (hG := hG)) :
    Client.Call.spec (GF := GF) (hG := hG) := by
  intro c W a sm svc M S args reply Ψ Rargs D Θ
  wp_start as ⟨#Hcs, #Hko, #Hcl, %HS, Henc, HD, #HDw⟩
  unfold isClient isClientN
  icases Hcl with ⟨%cv, %cid, %γn, #Hconn, #Hci, #Hrpc, #Hsend, #Hmu, #Hinv⟩
  ihave #Hnet := net_init_of_rpc $$ Hpkg
  ihave #Hsync := sync_init_of_rpc $$ Hpkg
  ihave #Hinit := net.rpc.isInit_access $$ Hpkg
  icases Hinit with ⟨#HeS, -⟩
  unfold errors.newVar
  icases HeS with ⟨%xS, #HeS, #HeSm⟩
  wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (t := go.error) (W64 1)) as %ch %γc ⟨#Hch, %Hcap, Hoc⟩
  · ipureintro; decide
  imod start_future ch γc _ (Or.inr rfl) $$ Hch Hoc with ⟨%γf, #Hfut, Haw⟩
  imod future_alloc_promise γf ch (callPost Ψ Θ D) [] $$ Hfut Haw with ⟨Hful, Haw⟩
  irename «$r0» => Hpcs
  generalize «$r0_ptr» = pcl at *
  iStructNamed Hpcs
  ipersist reply
  ipersist done
  wp_apply sync.Mutex.Lock.wp_proof _ _ $$ [$Hsync $Hsend] as ⟨Hlks, HS⟩
  wp_apply sync.Mutex.Lock.wp_proof _ _ $$ [$Hsync $Hmu] as ⟨Hlkm, HR⟩
  iunfold muInv at HR
  icases HR with ⟨%sq, %mp, %m, %sd, %cls, Hseq, Hpend, Hm, Hsd, Hcls, Hsdl, Hal⟩
  iunfold sendInv at HS
  icases HS with ⟨%L, %Wb, Hstok, Hcl, %HLb, HSr⟩
  cases sd <;> cases cls
  rotate_left
  · wp_auto
    wp_apply sync.Mutex.Unlock.wp_proof _ (muInv γn c) $$ [$Hsync $Hmu $Hlkm Hseq Hpend Hm Hsd Hcls Hsdl Hal]
    · unfold muInv; iexists _, _, _, _, _; iframe
    wp_apply sync.Mutex.Unlock.wp_proof _ (sendInv γn cid W a) $$ [$Hsync $Hsend $Hlks Hstok Hcl HSr]
    · unfold sendInv; iexists _, _; iframe; ipureintro; exact HLb
    iapply HΦ
    iright; iright
    isplitr
    · ipureintro; exact ⟨by simp [interface.mkOk], notServerErr_ptr _ _⟩
    isplitr
    · iapply errAny_newVar xS _ $$ HeSm
    iright
    iframe
  · wp_auto
    wp_apply sync.Mutex.Unlock.wp_proof _ (muInv γn c) $$ [$Hsync $Hmu $Hlkm Hseq Hpend Hm Hsd Hcls Hsdl Hal]
    · unfold muInv; iexists _, _, _, _, _; iframe
    wp_apply sync.Mutex.Unlock.wp_proof _ (sendInv γn cid W a) $$ [$Hsync $Hsend $Hlks Hstok Hcl HSr]
    · unfold sendInv; iexists _, _; iframe; ipureintro; exact HLb
    iapply HΦ
    iright; iright
    isplitr
    · ipureintro; exact ⟨by simp [interface.mkOk], notServerErr_ptr _ _⟩
    isplitr
    · iapply errAny_newVar xS _ $$ HeSm
    iright
    iframe
  · wp_auto
    wp_apply sync.Mutex.Unlock.wp_proof _ (muInv γn c) $$ [$Hsync $Hmu $Hlkm Hseq Hpend Hm Hsd Hcls Hsdl Hal]
    · unfold muInv; iexists _, _, _, _, _; iframe
    wp_apply sync.Mutex.Unlock.wp_proof _ (sendInv γn cid W a) $$ [$Hsync $Hsend $Hlks Hstok Hcl HSr]
    · unfold sendInv; iexists _, _; iframe; ipureintro; exact HLb
    iapply HΦ
    iright; iright
    isplitr
    · ipureintro; exact ⟨by simp [interface.mkOk], notServerErr_ptr _ _⟩
    isplitr
    · iapply errAny_newVar xS _ $$ HeSm
    iright
    iframe
  wp_auto
  wp_apply (wp_map_lookup2 go.uint64 (go.GoType.PointerType pendingCall.ty) mp m sq) $$ [$Hm] as Hm
  cases hms : m !! sq with
  | some pco =>
    simp only [Option.isSome_some, _root_.decide_true]
    wp_auto
    wp_apply sync.Mutex.Unlock.wp_proof _ (muInv γn c) $$ [$Hsync $Hmu $Hlkm Hseq Hpend Hm Hsd Hcls Hsdl Hal]
    · unfold muInv; iexists _, _, _, _, _; iframe
    wp_apply sync.Mutex.Unlock.wp_proof _ (sendInv γn cid W a) $$ [$Hsync $Hsend $Hlks Hstok Hcl HSr]
    · unfold sendInv; iexists _, _; iframe; ipureintro; exact HLb
    iapply HΦ
    iright; iright
    isplitr
    · ipureintro; exact ⟨by simp [interface.mkOk], notServerErr_ptr _ _⟩
    isplitr
    · iapply errAny_newVar xS _ $$ HeSm
    iright
    iframe
  | none =>
    simp only [Option.isSome_none]
    icases Hal with (Hal | ⟨-, %Hf⟩)
    rotate_left
    · exact absurd Hf.2 (by decide)
    icases HSr with (⟨%HWb, %lst0, Hlast⟩ | #Hsh)
    rotate_left
    · unfold shutLb
      ihave %Hc := mono_list_auth_lb_valid _ _ _ _ $$ Hsdl Hsh
      exfalso; simp at Hc
    imod saved_pred_alloc (fun p : List w8 × GoString => Ψ p.1 p.2) DFrac.discard DFrac.valid_discard with #Hpost
    icases Hpost with ⟨%post, #Hpost⟩
    imod token_alloc with Hcol
    icases Hcol with ⟨%col, Hcol⟩
    imod saved_prop_alloc D DFrac.discard DFrac.valid_discard with #Hret
    icases Hret with ⟨%ret, #Hret⟩
    imod client_insert γn m sq (pcl, post, col, ret) lst0 hms $$ Hinv Hal Hlast
      [Hful Hcol HD] with ⟨Hal, Hlast, He⟩
    · unfold callRes
      iexists ch, reply, γf, Ψ, Θ, D
      iframe
      iframe #
    wp_auto
    wp_apply (wp_mapInsert go.uint64 mp m sq pcl) $$ [$Hm] as Hm
    wp_apply sync.Mutex.Unlock.wp_proof _ (muInv γn c) $$ [$Hsync $Hmu $Hlkm Hseq Hpend Hm Hsd Hcls Hsdl Hal]
    · unfold muInv; iexists _, _, _, false, false; iframe
    wp_apply wp_getCodec $$ [$Hpkg $Hcs] as %cod #Hcf
    unfold codecFns
    icases Hcf with ⟨#HfE, #HfD, -, -, -⟩
    unfold kitCodecOk encOk
    icases Hko with ⟨#HencOk, #HdecOk, -, -⟩
    wp_auto
    wp_apply HencOk $$ Henc as %sl %bs Hsl ⟨HSdep, HRargs⟩
    wp_apply wp_encodeMsg $$ [$Hpkg $Hsl] as %rs ⟨Hrs, Hsl⟩
    ihave %Hrsl := ownSlice_len _ _ _ $$ Hrs
    imod client_append W a cid γn L (sq, sm, bs, post, col) $$ Hinv Hrpc Hcl [He] [HSdep]
      with ⟨Hcl, #Hlb⟩
    · unfold storeRes; iexists pcl, ret; iexact He
    · unfold reqDeposit; iexists svc, M, S, Ψ; iframe #; iframe; ipureintro; exact HS
    have HLb' : ∀ q ∈ (L ++ [(sq, sm, bs, post, col)]).map reqMsg, q.length < 2 ^ 63 := by
      intro q hq
      simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
        List.mem_singleton] at hq
      rcases hq with hq | rfl
      · exact HLb q hq
      · show (msgOf sq sm bs).length < 2 ^ 63
        rw [Hrsl.1]; exact sint_nat_lt _
    ihave #Hpr : (□ reqProto W a cid (Wb ++ frameOf (msgOf sq sm bs)) : IProp GF) $$ []
    · iintro !>
      unfold reqProto net.http.httpReqP
      iright
      iexists framesOf ((L ++ [(sq, sm, bs, post, col)]).map reqMsg)
      isplitr
      · ipureintro
        rw [HWb, List.map_append, framesOf_append, List.map_singleton, framesOf_singleton]
        simp [rpcHead, reqMsg]
      unfold reqBodyProto
      iexists γn.conn, L ++ [(sq, sm, bs, post, col)]
      iframe #
      ipureintro
      exact ⟨HLb', List.prefix_refl _⟩
    wp_apply wp_writeFrame $$ [$Hnet $Hci $Hstok $Hpr $Hrs] as %err ⟨%k, %Hk, #Herr, Hstok, Hrs⟩
    rcases err with ei | _
    · unfold connIface
      icases Hci with ⟨%cc, %Hcv, #Hcc⟩
      subst Hcv
      dsimp only
      wp_auto_lc 1
      wp_apply net.TCPConn.Close.wp_proof cc cid false $$ [$Hnet $Hcc] as %err2 -
      wp_apply sync.Mutex.Lock.wp_proof _ _ $$ [$Hsync $Hmu] as ⟨Hlkm, HR⟩
      iunfold muInv at HR
      icases HR with ⟨%sq2, %mp2, %m2, %sd2, %cls2, Hseq, Hpend, Hm, Hsd, Hcls, Hsdl, Hal⟩
      wp_auto
      ihave Hal : (pendAlive γn m2 true ∨ (token γn.dead ∗ ⌜m2 = ∅ ∧ true = true⌝)) $$ [Hal]
      · icases Hal with (Hal | ⟨Ht, %Hd⟩)
        · ileft; iapply pendAlive_shut $$ Hal
        · iright; iframe; ipureintro; exact ⟨Hd.1, rfl⟩
      imod (show ⊢ monoListAuthOwn (GF := GF) γn.sdl 1 (if sd2 = true then [()] else []) ==∗
          monoListAuthOwn γn.sdl 1 [()] ∗ monoListLbOwn γn.sdl [()] by
        cases sd2 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> iintro H
        · iapply monoListAuthOwn_update [()] (by simp) $$ H
        · ihave #Hl := monoListLbOwn_get _ _ _ $$ H
          imodintro; iframe; iframe #) $$ Hsdl with ⟨Hsdl, #Hsh⟩
      wp_apply sync.Mutex.Unlock.wp_proof _ (muInv γn c) $$ [$Hsync $Hmu $Hlkm Hseq Hpend Hm Hsd Hcls Hsdl Hal]
      · unfold muInv; iexists _, _, _, true, _; iframe
      wp_apply sync.Mutex.Unlock.wp_proof _ (sendInv γn cid W a) $$ [$Hsync $Hsend $Hlks Hstok Hcl]
      · unfold sendInv; iexists _, _; iframe
        isplitr
        · ipureintro; exact HLb'
        iright; unfold shutLb; iexact Hsh
      wp_apply sync.Mutex.Lock.wp_proof _ _ $$ [$Hsync $Hmu] as ⟨Hlkm, HR⟩
      iunfold muInv at HR
      icases HR with ⟨%sq3, %mp3, %m3, %sd3, %cls3, Hseq, Hpend, Hm, Hsd, Hcls, Hsdl, Hal⟩
      ihave %Hc := mono_list_auth_lb_valid _ _ _ _ $$ Hsdl Hsh
      cases sd3
      · exfalso; simp at Hc
      wp_auto
      wp_apply (wp_map_lookup2 go.uint64 (go.GoType.PointerType pendingCall.ty) mp3 m3 sq) $$ [$Hm] as Hm
      cases hms : m3 !! sq with
      | some pco =>
        simp only [Option.isSome_some, _root_.decide_true]
        wp_apply (wp_mapDelete mp3 m3 sq go.uint64 (go.GoType.PointerType pendingCall.ty)) $$ [$Hm] as Hm
        icases Hal with (Hal | ⟨-, %Hd⟩)
        rotate_left
        · rw [Hd.1] at hms; simp at hms
        ihave ⟨Hal, -, HD⟩ := client_withdraw γn m3 sq pco (pcl, post, col, ret) D hms $$ Hal Hlast Hret
        imod lc_fupd_elim_later $$ Hlc1 HD with HD
        wp_apply sync.Mutex.Unlock.wp_proof _ (muInv γn c) $$ [$Hsync $Hmu $Hlkm Hseq Hpend Hm Hsd Hcls Hsdl Hal]
        · unfold muInv; iexists _, _, _, true, _; iframe
        iapply HΦ
        iright; iright
        isplitr
        · ipureintro; exact ⟨by simp, Hk.2.2⟩
        isplitr
        · icases Herr with (%h | #H)
          · simp at h
          · iexact H
        ileft
        iframe
      | none =>
        simp only [Option.isSome_none]
        wp_apply (wp_mapDelete mp3 m3 sq go.uint64 (go.GoType.PointerType pendingCall.ty)) $$ [$Hm] as Hm
        rw [GMap.delete_notin m3 sq hms]
        wp_apply sync.Mutex.Unlock.wp_proof _ (muInv γn c) $$ [$Hsync $Hmu $Hlkm Hseq Hpend Hm Hsd Hcls Hsdl Hal]
        · unfold muInv; iexists _, _, _, true, _; iframe
          icases Hal with (H | ⟨Ht, %Hd⟩)
          · ileft; iexact H
          · iright; iframe; ipureintro; exact ⟨Hd.1, rfl⟩
        wp_apply (wp_future_await (t := go.error) γf ch ([] ++ [callPost Ψ Θ D])) $$ [$Hfut $Haw]
          as %v %P %pre %post' ⟨%Hsp, HP, -⟩
        have hP : P = callPost Ψ Θ D := by
          cases pre with
          | nil => simp at Hsp; first | exact Hsp.1.symm | exact Hsp.symm | skip
          | cons x xs => simp at Hsp
        subst hP
        iapply HΦ
        iapply callPost_done $$ [$HP $HRargs]
    · have hk : k = (frameOf (msgOf sq sm bs)).length := Hk.2.1 rfl
      subst hk
      rw [List.take_length]
      wp_auto
      wp_apply sync.Mutex.Unlock.wp_proof _ (sendInv γn cid W a) $$ [$Hsync $Hsend $Hlks Hstok Hcl Hlast]
      · unfold sendInv; iexists _, _; iframe
        isplitr
        · ipureintro; exact HLb'
        ileft
        isplitr
        · ipureintro
          rw [HWb, List.map_append, framesOf_append, List.map_singleton, framesOf_singleton]
          simp [reqMsg]
        iexists _; iexact Hlast
      wp_apply (wp_future_await (t := go.error) γf ch ([] ++ [callPost Ψ Θ D])) $$ [$Hfut $Haw]
        as %v %P %pre %post ⟨%Hsp, HP, -⟩
      have hP : P = callPost Ψ Θ D := by
        cases pre with
        | nil => simp at Hsp; first | exact Hsp.1.symm | exact Hsp.symm | skip
        | cons x xs => simp at Hsp
      subst hP
      iapply HΦ
      iapply callPost_done $$ [$HP $HRargs]

theorem Client.input.wp_proof (wp_getCodec : getCodec.clientSpec (GF := GF) (hG := hG))
    (wp_readFrame : readFrame.spec (GF := GF) (hG := hG))
    (wp_decodeMsg : decodeMsg.spec (GF := GF) (hG := hG)) :
    Client.input.spec (GF := GF) (hG := hG) := by
  intro c W a cv cid γn
  wp_start as ⟨#Hcl, Hown⟩
  unfold isClientN
  icases Hcl with ⟨#Hconn, #Hci, #Hrpc, #Hsend, #Hmu, #Hinv⟩
  ihave #Hnet := net_init_of_rpc $$ Hpkg
  ihave #Hsync := sync_init_of_rpc $$ Hpkg
  ihave #Hinit := net.rpc.isInit_access $$ Hpkg
  icases Hinit with ⟨#HeS, -, #HeF, -⟩
  unfold errors.newVar
  icases HeS with ⟨%xS, #HeS, #HeSm⟩
  icases HeF with ⟨%xF, #HeF, #HeFm⟩
  wp_auto
  wp_for
  iunfold readerOwn at Hown
  icases Hown with ⟨%C, %Lr, Hrt, Hcons, Hdead, #HLr, #HCa, %HC⟩
  wp_apply wp_readFrame $$ [$Hnet $Hpkg $Hci $Hrt] as %p %rerr ⟨%data, Hrt, Hr⟩
  icases Hr with (⟨%Hrerr, %pl, %Hpl, Hp⟩ | ⟨%Hrerr, #Hea⟩)
  rotate_left
  rcases rerr with ei | _
  rotate_left
  · exact absurd rfl Hrerr.1
  rotate_left
  dsimp only
  wp_auto
  wp_for_post
  have hne : GoInterface.ok ei ≠ GoInterface.nil := by simp
  have hns : notServerErr (GoInterface.ok ei) := Hrerr.2
  clear Hrerr
  generalize GoInterface.ok ei = e at hne hns ⊢
  rotate_left
  -- MAIN
  subst Hrerr
  wp_auto
  wp_apply (lc := 2) wp_decodeMsg $$ [$Hpkg $Hp] as %seq %msg %body %ok Hd
  cases ok
  wp_auto
  wp_for_post
  have hne : interface.mkOk errors.errorString.ty.PointerType #xF ≠ GoInterface.nil := by
    simp [interface.mkOk]
  have hns : notServerErr (interface.mkOk errors.errorString.ty.PointerType #xF) :=
    notServerErr_ptr _ _
  ihave #Hea := errAny_newVar xF _ $$ HeFm
  iclear HeF
  generalize interface.mkOk errors.errorString.ty.PointerType #xF = e at hne hns ⊢
  rotate_left
  simp only [↓reduceIte]
  icases Hd with ⟨%b, ⟨%Hplb, %Hmsgl⟩, Hbody⟩
  icases recvTok_proto _ _ _ _ $$ Hrt with ⟨Hrt, Hpp⟩
  unfold protoPrefix
  icases Hpp with (%Hnil | ⟨%ext, %Hext, #HP⟩)
  · exfalso; simp [connectedBytes] at Hnil
  wp_auto
  wp_apply sync.Mutex.Lock.wp_proof _ _ $$ [$Hsync $Hmu] as ⟨Hlkm, HR⟩
  iunfold muInv at HR
  icases HR with ⟨%sq, %mp, %m, %sd, %cls, Hseq, Hpend, Hm, Hsd, Hcls, Hsdl, Hal⟩
  icases alive_of_dead γn m sd $$ Hal Hdead with ⟨Hal, Hdead⟩
  have hext : connectedBytes ++ framesOf (C.map (respMsg Lr)) ++ frameOf pl <+: ext := by
    rw [← Hpl.1]; exact Hext
  imod client_consume W a cid γn C Lr ext pl seq msg b Hplb Hpl.2 HC.1 HC.2.1 HC.2.2 hext
    $$ Hinv Hrpc HP Hcons HLr HCa with ⟨%i, %Lr', %r, %Hr, Hcons, #HLr', #HCa', Hsr⟩
  unfold storeRes
  icases Hsr with ⟨%pc, %ret, Hel⟩
  rw [Hr.1] at *
  ihave Hown : readerOwn γn cid W a $$ [Hrt Hcons Hdead]
  · unfold readerOwn
    iexists C ++ [(i, msg, b)], Lr'
    rw [Hr.2.2.2.2.2, Hpl.1, List.append_assoc]
    iframe
    iframe #
    ipureintro; exact ⟨Hr.2.2.1, Hr.2.2.2.1, Hr.2.2.2.2.1⟩
  imod client_take γn m sd seq (pc, r.post, r.col, ret) $$ Hinv Hal Hel
    with (⟨%Hms, Hal⟩ | ⟨%Hms, Hal, Hres⟩)
  · wp_auto
    wp_apply (wp_map_lookup2 go.uint64 (go.GoType.PointerType pendingCall.ty) mp m seq) $$ [$Hm] as Hm
    simp only [Hms.1, Option.isSome_none, Option.getD_none]
    wp_apply (wp_mapDelete mp m seq go.uint64 (go.GoType.PointerType pendingCall.ty)) $$ [$Hm] as Hm
    rw [GMap.delete_notin m seq Hms.1]
    wp_apply sync.Mutex.Unlock.wp_proof _ (muInv γn c) $$ [$Hsync $Hmu $Hlkm Hseq Hpend Hm Hsd Hcls Hsdl Hal]
    · unfold muInv; iexists _, _, _, _, _; iframe
    wp_for_post
    iframe
  wp_auto
  wp_apply (wp_map_lookup2 go.uint64 (go.GoType.PointerType pendingCall.ty) mp m seq) $$ [$Hm] as Hm
  simp only [Hms, Option.isSome_some, _root_.decide_true, Option.getD_some]
  wp_apply (wp_mapDelete mp m seq go.uint64 (go.GoType.PointerType pendingCall.ty)) $$ [$Hm] as Hm
  wp_apply sync.Mutex.Unlock.wp_proof _ (muInv γn c) $$ [$Hsync $Hmu $Hlkm Hseq Hpend Hm Hsd Hcls Hsdl Hal]
  · unfold muInv; iexists _, _, _, _, _; iframe Hseq Hpend Hm Hsd Hcls Hsdl; ileft; iexact Hal
  unfold callRes
  icases Hres with ⟨%ch, %reply, %γf, %Φ', %Θ', %D', #Hrep, #Hdone, #Hfut, Hful, #Hpost, Hcol,
    #Hret, HD', #HDw', -, #Hcs, #Hko⟩
  ihave #Hai := BigSepL.bigSepL_mem (show (i, msg, b) ∈ C ++ [(i, msg, b)] by simp)
    $$ HCa'
  imod client_collect W a cid γn.conn Lr' i r msg b Φ' Hr.2.1 $$ Hrpc HLr' Hai Hcol Hpost Hlc1
    Hlc2 with HΦr
  by_cases hm : msg ≠ []
  · rw [decide_eq_false hm]
    wp_auto
    wp_apply (wp_future_fulfill (t := go.error) γf ch (interface.mkOk ServerError.ty #msg))
      $$ [$Hfut Hful HD' HΦr]
    · unfold Fulfilled; iexists _; iframe; unfold callPost; iright; ileft
      iexists msg
      isplitr
      · ipureintro; exact ⟨hm, rfl⟩
      isplitr
      · iapply (show ⊢ errMsg (GF := GF) (interface.mkOk ServerError.ty #msg) msg from
          errMsg_serverErr msg)
      isplitl [HΦr]
      · iexists b; iexact HΦr
      iexact HD'
    wp_for_post
    iframe
  have hm' : msg = [] := Classical.byContradiction hm
  subst hm'
  simp only [_root_.decide_true]
  wp_auto
  wp_apply wp_getCodec $$ [$Hpkg $Hcs] as %cod #Hcf
  unfold codecFns
  icases Hcf with ⟨#HfE, #HfD, -, -, -⟩
  unfold kitCodecOk decOk
  icases Hko with ⟨-, #HdecOk, -, -⟩
  wp_auto
  ihave Hdec := HDw' $$ HD' %b
  wp_apply HdecOk $$ Hbody Hdec as %derr %dok Hbody %Hdok %Hdns HΘ Hem
  cases dok
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold errMsg
  icases Hem with ⟨%emsg, %e0, %Hd0, %Ht0, #HErr⟩
  subst Hd0
  ihave #Hea := errAny_ok e0 emsg Ht0 $$ HErr
  dsimp only
  wp_auto
  wp_apply HErr
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xn #HnE
  wp_apply (wp_future_fulfill (t := go.error) γf ch
    (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #xn)) $$ [$Hfut Hful HΘ]
  · unfold Fulfilled; iexists _; iframe; unfold callPost; iright; iright
    isplitr
    · ipureintro; exact ⟨by simp [interface.mkOk], notServerErr_ptr _ _⟩
    isplitr
    · iapply errAny_newVar xn _ $$ HnE
    iright; iexists b; iexact HΘ
  wp_for_post
  have hne : GoInterface.ok e0 ≠ GoInterface.nil := by simp
  have hns : notServerErr (GoInterface.ok e0) := Hdns
  clear Hdns
  generalize GoInterface.ok e0 = e at hne hns ⊢
  iunfold readerOwn at Hown
  icases Hown with ⟨%C2, %Lr2, -, -, Hdead, -⟩
  rotate_left
  have hd : derr = GoInterface.nil := Hdok.2 rfl
  subst hd
  dsimp only
  wp_auto
  wp_apply (wp_future_fulfill (t := go.error) γf ch GoInterface.nil) $$ [$Hfut Hful HΘ HΦr]
  · unfold Fulfilled; iexists _; iframe; unfold callPost; ileft
    isplitr
    · ipureintro; rfl
    iexists b; iframe
  wp_for_post
  iframe
  all_goals
    wp_apply sync.Mutex.Lock.wp_proof _ _ $$ [$Hsync $Hsend] as ⟨Hlks, HS⟩
    wp_apply sync.Mutex.Lock.wp_proof _ _ $$ [$Hsync $Hmu] as ⟨Hlkm, HR⟩
    iunfold muInv at HR
    icases HR with ⟨%sq, %mp, %m, %sd, %cls, Hseq, Hpend, Hm, Hsd, Hcls, Hsdl, Hal⟩
    icases Hal with (Hal | ⟨Hd2, -⟩)
    rotate_left
    · iexfalso; iapply token_exclusive $$ Hdead Hd2
    imod (show ⊢ monoListAuthOwn (GF := GF) γn.sdl 1 (if sd = true then [()] else []) ==∗
        monoListAuthOwn γn.sdl 1 [()] ∗ monoListLbOwn γn.sdl [()] by
      cases sd <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> iintro H
      · iapply monoListAuthOwn_update [()] (by simp) $$ H
      · ihave #Hl := monoListLbOwn_get _ _ _ $$ H
        imodintro; iframe; iframe #) $$ Hsdl with ⟨Hsdl, -⟩
    unfold pendAlive
    icases Hal with ⟨%P, %lst, -, -, -, Hms⟩
    have hS : interface.mkOk errors.errorString.ty.PointerType #xS ≠ GoInterface.nil := by
      simp [interface.mkOk]
    cases cls <;> wp_auto
    rotate_left
    iclear Hea
    clear hne hns
    clear e
    have hS2 : notServerErr (interface.mkOk errors.errorString.ty.PointerType #xS) :=
      notServerErr_ptr _ _
    ihave #Hea := errAny_newVar xS _ $$ HeSm
    generalize interface.mkOk errors.errorString.ty.PointerType #xS = e at hS hS2 ⊢
    have hne := hS
    have hns := hS2
    clear hS hS2
    all_goals
      wp_func_lits
      wp_bind (App (App (Val (map.forRange _ _)) _) _)
      iapply (wp_map_for_range (K := w64) (V := Loc) (fun keys (i : Int) => iprop(⌜0 ≤ i⌝ ∗
          (∃ r : GMap w64 Loc, ⌜∀ (j : Nat) (k : w64), i ≤ (j : Int) → keys[j]? = some k →
              r !! k = m !! k⌝ ∗
            [∗map] s ↦ pc ∈ r, ∃ e' : PEntry, ⌜e'.1 = pc⌝ ∗ callRes e') ∗
          err_ptr ↦ e ∗ ∃ pv : Loc, pc_ptr ↦ pv))) $$ Hm
      iintro %keys %hkeys
      isplitl [Hms err pc]
      · isplitr
        · ipureintro; omega
        isplitl [Hms]
        · iexists m
          isplitr
          · ipureintro; intro j k _ _; rfl
          iapply BigSepM.bigSepM_mono (fun {s pc} _ => ?_) $$ Hms
          iintro ⟨%e', %he', -, Hr⟩
          iexists e'; iframe; ipureintro; exact he'.2
        iframe
      isplitl []
      · imodintro
        iintro %i %key %v ⟨%hk1, %hk2⟩ ⟨%hi, ⟨%r, %hr, Hr⟩, Herr, %pv, Hpc⟩
        have hrk : r !! key = some v := by rw [hr i.toNat key (by omega) hk1]; exact hk2
        icases (BigSepM.bigSepM_delete (show get? r key = some v from hrk)).1 $$ Hr
          with ⟨⟨%e', %he', Hres⟩, Hr⟩
        unfold callRes
        icases Hres with ⟨%ch, %reply, %γf, %Φ', %Θ', %D', #Hrep, #Hdone, #Hfut, Hful, -, -, -,
          HD', -⟩
        subst he'
        wp_auto
        wp_apply (wp_future_fulfill (t := go.error) γf ch e) $$ [$Hfut Hful HD']
        · unfold Fulfilled; iexists _; iframe; unfold callPost; iright; iright
          isplitr
          · ipureintro; exact ⟨hne, hns⟩
          isplitr
          · iexact Hea
          ileft; iexact HD'
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        isplitr
        · ipureintro; omega
        isplitl [Hr]
        · iexists GMap.delete key r
          iframe
          ipureintro
          intro j k hj hjk
          have hne' : key ≠ k := by
            intro hkk
            subst hkk
            obtain ⟨h1, h1'⟩ := List.getElem?_eq_some_iff.1 hk1
            obtain ⟨h2, h2'⟩ := List.getElem?_eq_some_iff.1 hjk
            have := (hkeys.2.2.getElem_inj).1 (h1'.trans h2'.symm)
            omega
          rw [GMap.lookup_delete_ne _ hne']; exact hr j k (by omega) hjk
        isplitl [Herr]
        · iexact Herr
        iexists _; iexact Hpc
      iintro ⟨%hi, -, Herr, %pv, Hpc⟩ Hm
      wp_auto
      wp_apply (wp_map_make1 (K := w64) (V := Loc) go.uint64 (go.GoType.PointerType pendingCall.ty))
        as %mp' Hm'
      wp_apply sync.Mutex.Unlock.wp_proof _ (muInv γn c) $$ [$Hsync $Hmu $Hlkm Hseq Hpend Hm' Hsd Hcls Hsdl Hdead]
      · unfold muInv; iexists _, _, _, true, _; iframe; iright; iframe; ipureintro; exact ⟨rfl, rfl⟩
      wp_apply sync.Mutex.Unlock.wp_proof _ (sendInv γn cid W a) $$ [$Hsync $Hsend $Hlks $HS]
      iapply HΦ; itrivial

theorem newClient.wp_proof (wp_input : Client.input.spec (GF := GF) (hG := hG)) :
    newClient.spec (GF := GF) (hG := hG) := by
  intro W a cv cid γ
  wp_start as ⟨#Hci, #Hrpc, Hreqs, Hstok, Hrtok⟩
  ihave #Hsync := sync_init_of_rpc $$ Hpkg
  ihave #Hlb0 := monoListLbOwn_get _ _ _ $$ Hreqs
  imod client_alloc γ $$ Hreqs with ⟨%γn, %Hγ, #Hinv, Hcl, Hlast, Hal, Hsdl, Hcons, Hdead⟩
  subst Hγ
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Loc) go.uint64 (go.GoType.PointerType pendingCall.ty))
    as %mp Hm
  iStructNamed «$r0»
  generalize «$r0_ptr» = cl at *
  ipersist conn
  imod sync.init_Mutex (sendInv γn cid W a) ⊤ _ $$ sending [Hstok Hcl Hlast] with #Hsend
  · inext
    unfold sendInv
    iexists [], rpcHead
    iframe
    isplitr
    · ipureintro; simp
    ileft
    isplitr
    · ipureintro; simp [framesOf]
    iexists _; iexact Hlast
  imod sync.init_Mutex (muInv γn cl) ⊤ _ $$ mu [seq pending Hm shutdown closing Hsdl Hal] with #Hmu
  · inext
    unfold muInv
    iexists _, _, _, false, false
    iframe
  ihave #Hcn : isClientN cl W a cv cid γn $$ []
  · unfold isClientN; iframe #
  wp_apply wp_fork $$ [Hrtok Hcons Hdead]
  · wp_apply wp_input $$ [$Hpkg $Hcn Hrtok Hcons Hdead]
    · unfold readerOwn
      iexists [], []
      simp only [List.map_nil, framesOf_nil, List.append_nil]
      iframe
      iframe #
      isplitr
      · iapply BigSepL.bigSepL_nil.2; itrivial
      ipureintro; simp
    itrivial
  iapply HΦ
  unfold isClient
  iexists cv, cid, γn
  iexact Hcn

theorem DialHTTPPath.wp_proof (wp_readFull : readFull.spec (GF := GF) (hG := hG))
    (wp_newClient : newClient.spec (GF := GF) (hG := hG)) :
    DialHTTPPath.spec (GF := GF) (hG := hG) := by
  intro W a
  wp_start as Haddr
  unfold rpcAddr
  icases Haddr with ⟨#Hap, #Hreg⟩
  ihave #Hnet := net_init_of_rpc $$ Hpkg
  wp_auto
  wp_apply net.Dial.wp_proof a (reqProto W a) (respProto W a) $$ [$Hnet $Hap] as %cv %err Hres
  unfold net.newConnResult
  icases Hres with (⟨%cc, %cid, ⟨%Hcv, %Herr⟩, #Hcc, ⟨Hstok, Hrtok⟩, Hfr⟩ | ⟨%i, ⟨%Hcv, %Herr⟩, %code, -, #Hoe⟩)
  rotate_left
  · ihave ⟨#He, -⟩ := opErr_errAny _ _ _ $$ Hoe
    subst Hcv Herr
    wp_auto
    iapply HΦ; iright
    isplitr
    · ipureintro; simp
    iexact He
  subst Hcv Herr
  wp_auto
  wp_apply wp_string_to_bytes as %sb ⟨Hsb, -⟩
  ihave #Hp0 : (□ reqProto W a cid ([] ++ rpcHead) : IProp GF) $$ []
  · iintro !>
    unfold reqProto net.http.httpReqP
    ileft; ipureintro; simp [rpcHead]
  ihave Hsb : (sb ↦* rpcHead : IProp GF) $$ [Hsb]
  · unfold rpcHead net.http.connectHead; iexact Hsb
  wp_apply net.TCPConn.Write.wp_proof cc cid false sb rpcHead _ (reqProto W a) [] $$ [$Hnet $Hcc $Hstok $Hp0 $Hsb]
    as %n %err2 ⟨%k, %code, %Hk, Hsb, Hstok, #Hce⟩
  rcases err2 with ei | _
  · icases connErr_errAny _ _ _ $$ [$Hnet $Hce] with (%h | ⟨#He, -⟩)
    · simp at h
    dsimp only
    wp_auto
    wp_apply net.TCPConn.Close.wp_proof cc cid false $$ [$Hnet $Hcc] as %e2 -
    iapply HΦ; iright
    isplitr
    · ipureintro; simp
    iexact He
  have hk : k = rpcHead.length := Hk.2.2.2 rfl
  subst hk
  rw [List.take_length, List.nil_append]
  dsimp only
  wp_auto
  ihave #Hci : connIface (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #cc) cid false $$ []
  · unfold connIface; iexists cc; iframe #; ipureintro; rfl
  wp_apply wp_readFull _ cid false (respProto W a) [] (W64 34) $$ [$Hnet $Hci $Hrtok]
    as %resp %err3 ⟨%data, Hrtok, Hr⟩
  · ipureintro; decide
  icases Hr with (⟨⟨%He3, %Hlen⟩, Hresp⟩ | ⟨%He3, #He⟩)
  rotate_left
  · rcases err3 with ei | _
    · dsimp only
      wp_auto
      wp_apply net.TCPConn.Close.wp_proof cc cid false $$ [$Hnet $Hcc] as %e2 -
      iapply HΦ; iright
      isplitr
      · ipureintro; simp
      iexact He
    · exact absurd rfl He3.1
  subst He3
  dsimp only
  wp_auto
  wp_apply wp_bytes_to_string $$ [$Hresp] as Hresp
  by_cases hd : data ≠ connectedBytes
  · unfold connectedBytes at hd
    rw [decide_eq_false hd]
    ihave #Hinit := net.rpc.isInit_access $$ Hpkg
    icases Hinit with ⟨-, #HeH, -⟩
    unfold errors.newVar
    icases HeH with ⟨%xH, #HeH, #HeHm⟩
    wp_auto
    wp_apply net.TCPConn.Close.wp_proof cc cid false $$ [$Hnet $Hcc] as %e2 -
    iapply HΦ; iright
    isplitr
    · ipureintro; simp [interface.mkOk]
    iapply errAny_newVar xH _ $$ HeHm
  have hd' : data = connectedBytes := Classical.byContradiction hd
  subst hd'
  unfold connectedBytes
  rw [decide_eq_true rfl]
  wp_auto
  ihave Hrtok : recvTok cid false (respProto W a) connectedBytes $$ [Hrtok]
  · unfold connectedBytes; rw [List.nil_append]; iexact Hrtok
  imod conn_register W a cid $$ Hreg Hfr with ⟨%γ, #Hrpc, Hreqs⟩
  wp_apply wp_newClient W a _ cid γ $$ [$Hpkg $Hci $Hrpc $Hreqs $Hstok $Hrtok] as %cl #Hcl
  iapply HΦ; ileft
  isplitr
  · ipureintro; rfl
  iexact Hcl

theorem DialHTTP.wp_proof (wp_path : DialHTTPPath.spec (GF := GF) (hG := hG)) :
    DialHTTP.spec (GF := GF) (hG := hG) := by
  intro W a
  wp_start as Haddr
  wp_auto
  rw [show (DefaultRPCPath : val) = #rpcPath from rfl]
  wp_apply wp_path W a $$ [$Hpkg $Haddr] as %cl %err Hr
  iapply HΦ $$ Hr

end proofs

end net.rpc

end Perennial
