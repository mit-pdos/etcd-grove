/-
The proofs of the grpc model's client specs (`ClientDefs.lean`).

An answer's code is a `codes.Code` (`answerRes` records that its 64 bits are below `2 ^ 32`
unless `0`), which the reader learns with the answer (`collect`), so `Invoke`'s conversion to
`codes.Code` keeps an error answer an error.
-/
module

public import Harness.Proof.grpc.ClientGhost
public import Harness.Proof.grpc.Status
public import Harness.Proof.net.TCPConn__Write

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn
open google_golang_org.protobuf.proto (PbCodec PbKit codecSet kitCodecOk)
open net.rpc (connIface errAny framesOf frameOf)

namespace google_golang_org.grpc

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions] [google_golang_org.grpc.Assumptions]
variable [google_golang_org.protobuf.reflect.protoreflect.Assumptions]
variable [google_golang_org.protobuf.proto.Assumptions]
variable [google_golang_org.grpc.codes.Assumptions] [google_golang_org.grpc.status.Assumptions]
variable [context.Assumptions] [fmt.Assumptions]
variable [PbKit] [PbCodec GF]

set_option goose.wp.extras true

/-- The packages the `grpc` model imports are initialized. -/
theorem client_deps :
    isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ⊢
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ isPkgInit (PROP := IProp GF) pkg_id.errors ∗
      isPkgInit (PROP := IProp GF) pkg_id.net ∗ isPkgInit (PROP := IProp GF) pkg_id.sync ∗
      isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.codes ∗
      isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗
      isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto := by
  refine (isPkgInit_unfold_deps (PROP := IProp GF) pkg_id.google_golang_org.grpc).trans ?_
  show iprop(isPkgInit (PROP := IProp GF) pkg_id.context ∗ isPkgInit (PROP := IProp GF) pkg_id.errors ∗
    isPkgInit (PROP := IProp GF) pkg_id.net ∗ isPkgInit (PROP := IProp GF) pkg_id.sync ∗
    isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.codes ∗
    isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗
    isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗
    isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.credentials ∗
    isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.primitive ∗ True) ⊢ _
  iintro ⟨H1, H2, H3, H4, H5, H6, H7, -, -, -⟩
  iframe

theorem transport.isShutdown.wp_proof : transport.isShutdown.spec (GF := GF) (hG := hG) := by
  intro t W a
  wp_start as #Ht
  ihave ⟨-, -, -, #Hsync, -, -, -⟩ := client_deps $$ Hpkg
  unfold isTransport isTransportN
  icases Ht with ⟨%cv, %cid, %γn, #Hconn, #Hci, #Hc, #Hsend, #Hmu, #Hti⟩
  wp_auto
  wp_apply sync.Mutex.Lock.wp_proof _ _ $$ [$Hsync $Hmu] as ⟨Hlk, HR⟩
  iunfold muInv at HR
  icases HR with ⟨%mp, %m, %sd, Hpend, Hm, Hsd, Hsdl, Hal⟩
  wp_auto
  wp_apply sync.Mutex.Unlock.wp_proof _ (muInv γn t) $$ [$Hsync $Hmu $Hlk Hpend Hm Hsd Hsdl Hal]
  · unfold muInv; iexists _, _, _; iframe
  iapply HΦ; itrivial

theorem ctxErr.wp_proof : ctxErr.spec (GF := GF) (hG := hG) := by
  intro ctx cd
  wp_start as #Hctx
  ihave ⟨#Hcx, -, -, -, -, #Hst, -⟩ := client_deps $$ Hpkg
  ihave #Hci := context.isInit_access $$ Hcx
  icases Hci with ⟨-, -, -, -, -, ⟨%x, #HC, #Hxs⟩, #HD, -⟩
  unfold context.isContext context.isContextDef
  icases Hctx with ⟨-, -, HErr, -⟩
  ihave #HE := HErr $$ %Broadcast.Unknown
  wp_auto
  wp_apply HE as %e He Hce
  rcases e with i | _
  · simp only [reduceCtorEq, ↓reduceIte]
    unfold context.isCtxErr
    icases Hce with (⟨-, %x', %hx, -⟩ | ⟨-, %hd⟩)
    · simp only [interface.mkOk, GoInterface.ok.injEq] at hx
      subst hx
      have hne : go.GoType.PointerType errors.errorString.ty ≠ context.deadlineExceededError.ty := by
        unfold context.deadlineExceededError.ty; simp
      simp only [interface.mkOk, hne, ↓reduceIte]
      wp_auto
      wp_apply status.Error.wp_proof $$ [$Hst] as %err Herr
      iapply HΦ
      unfold status.errPost
      icases Herr with (%h | #H)
      · exfalso; revert h; simp
      · iexists _, _; iexact H
    · simp only [interface.mkOk, GoInterface.ok.injEq] at hd
      subst hd
      simp only [interface.mkOk]
      wp_auto
      wp_apply status.Error.wp_proof $$ [$Hst] as %err Herr
      iapply HΦ
      unfold status.errPost
      icases Herr with (%h | #H)
      · exfalso; revert h; simp
      · iexists _, _; iexact H
  · simp only [interface.mkOk]
    wp_auto
    wp_apply status.Error.wp_proof $$ [$Hst] as %err Herr
    iapply HΦ
    unfold status.errPost
    icases Herr with (%h | #H)
    · exfalso; revert h; simp
    · iexists _, _; iexact H

theorem newTransport.wp_proof (wp_input : transport.input.spec (GF := GF) (hG := hG)) :
    newTransport.spec (GF := GF) (hG := hG) := by
  intro W a cv cid γ
  wp_start as ⟨#Hci, #Hc, Hreqs, Hstok, Hrtok⟩
  ihave ⟨-, -, -, #Hsync, -, -, -⟩ := client_deps $$ Hpkg
  imod transport_alloc γ $$ Hreqs with ⟨%γn, %Hγ, #Hti, Hcl, Hsdl, Hdead⟩
  subst Hγ
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Loc) go.uint64 (go.GoType.PointerType pendingCall.ty))
    as %mp Hm
  iStructNamed «$r0»
  generalize «$r0_ptr» = t at *
  ipersist conn
  imod sync.init_Mutex (sendInv γn t cid W a) ⊤ _ $$ sending [seq Hstok Hcl] with #Hsend
  · inext
    unfold sendInv
    iexists [], _, []
    iframe
    isplitr
    · ipureintro; simp [cmsgs]
    ileft
    ipureintro; simp [cmsgs, net.rpc.framesOf]
  imod sync.init_Mutex (muInv γn t) ⊤ _ $$ mu [pending Hm shutdown Hsdl] with #Hmu
  · inext
    unfold muInv
    iexists _, _, false
    iframe
    ileft
    unfold pendAlive
    iapply BigSepM.bigSepM_empty.2
    itrivial
  ihave #Htn : isTransportN t W a cv cid γn $$ []
  · unfold isTransportN; iframe #
  wp_apply wp_fork $$ [Hrtok Hdead]
  · wp_apply wp_input $$ [$Hpkg $Htn Hrtok Hdead]
    · unfold readerOwn
      iexists []
      simp only [net.rpc.framesOf_nil]
      iframe
      ipureintro; simp
    itrivial
  iapply HΦ
  unfold isTransport
  iexists cv, cid, γn
  iexact Htn

theorem transport.send.wp_proof : transport.send.spec (GF := GF) (hG := hG) := by
  intro t W a fm req bs S Ψ
  wp_start as ⟨#Ht, Hreq, %HS, HSd⟩
  ihave ⟨-, -, #Hnet, #Hsync, -, -, -⟩ := client_deps $$ Hpkg
  unfold isTransport isTransportN
  icases Ht with ⟨%cv, %cid, %γn, #Hconn, #Hci, #Hc, #Hsend, #Hmu, #Hti⟩
  wp_auto
  wp_apply (chan.wp_make2 (V := Loc) (t := go.GoType.PointerType response.ty) (W64 1))
    as %ch %γc ⟨#Hch, %Hcap, Hoc⟩
  · ipureintro; decide
  imod start_future ch γc _ (Or.inr rfl) $$ Hch Hoc with ⟨%γf, #Hfut, Haw⟩
  imod future_alloc_promise γf ch (callDone Ψ) [] $$ Hfut Haw with ⟨Hful, Haw⟩
  irename «$r0» => Hpcs
  generalize «$r0_ptr» = pcl at *
  iStructNamed Hpcs
  ipersist done
  wp_apply sync.Mutex.Lock.wp_proof _ _ $$ [$Hsync $Hsend] as ⟨Hlks, HSi⟩
  wp_apply sync.Mutex.Lock.wp_proof _ _ $$ [$Hsync $Hmu] as ⟨Hlkm, HR⟩
  iunfold muInv at HR
  icases HR with ⟨%mp, %m, %sd, Hpend, Hm, Hsd, Hsdl, Hal⟩
  iunfold sendInv at HSi
  icases HSi with ⟨%L, %sq, %Wb, Hseq, Hstok, Hcl, %HLb, HSr⟩
  imod (show ⊢ monoListAuthOwn (GF := GF) γn.sdl 1 (if sd = true then [()] else []) ==∗
      monoListAuthOwn γn.sdl 1 (if sd = true then [()] else []) ∗
      (monoListAuthOwn γn.sdl 1 (if sd = true then [()] else []) ==∗
        monoListAuthOwn γn.sdl 1 [()] ∗ shutLb γn) by
    iintro H
    imodintro
    iframe
    iintro H
    cases sd <;> simp only [Bool.false_eq_true, ↓reduceIte] at *
    · imod monoListAuthOwn_update [()] (by simp) $$ H with ⟨H, #Hl⟩
      imodintro; iframe; unfold shutLb; iexact Hl
    · ihave #Hl := monoListLbOwn_get _ _ _ $$ H
      imodintro; iframe; unfold shutLb; iexact Hl) $$ Hsdl with ⟨Hsdl, Hshut⟩
  cases sd
  rotate_left
  · wp_auto
    imod Hshut $$ Hsdl with ⟨Hsdl, #Hsh⟩
    wp_apply sync.Mutex.Unlock.wp_proof _ (muInv γn t)
      $$ [$Hsync $Hmu $Hlkm Hpend Hm Hsd Hsdl Hal]
    · unfold muInv; iexists _, _, true; simp only [↓reduceIte]; iframe Hpend Hm Hsd Hsdl
      icases Hal with (H | ⟨Hd, %h⟩)
      · ileft; iexact H
      · iright; iframe; ipureintro; exact ⟨h.1, trivial⟩
    wp_apply sync.Mutex.Unlock.wp_proof _ (sendInv γn t cid W a)
      $$ [$Hsync $Hsend $Hlks Hseq Hstok Hcl]
    · unfold sendInv; iexists _, _, _; iframe; isplitr
      · ipureintro; exact HLb
      iright; iexact Hsh
    iapply HΦ; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  simp only [Bool.false_eq_true, ↓reduceIte]
  wp_auto
  wp_if_destruct
  · imod Hshut $$ Hsdl with ⟨Hsdl, #Hsh⟩
    wp_apply sync.Mutex.Unlock.wp_proof _ (muInv γn t)
      $$ [$Hsync $Hmu $Hlkm Hpend Hm Hsd Hsdl Hal]
    · unfold muInv; iexists _, _, true; simp only [↓reduceIte]; iframe Hpend Hm Hsd Hsdl
      icases Hal with (H | ⟨Hd, %h⟩)
      · ileft; iexact H
      · iright; iframe; ipureintro; exact ⟨h.1, trivial⟩
    wp_apply sync.Mutex.Unlock.wp_proof _ (sendInv γn t cid W a)
      $$ [$Hsync $Hsend $Hlks Hseq Hstok Hcl]
    · unfold sendInv; iexists _, _, _; iframe; isplitr
      · ipureintro; exact HLb
      iright; iexact Hsh
    iapply HΦ; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  -- up, and fewer than maxSeq frames
  icases HSr with (%HSr | #Hsh)
  rotate_left
  · unfold shutLb
    ihave %Hc := mono_list_auth_lb_valid _ _ _ _ $$ Hsdl Hsh
    exfalso; simp at Hc
  obtain ⟨rfl, rfl⟩ := HSr
  icases Hal with (Hal | ⟨-, %Hf⟩)
  rotate_left
  · exact absurd Hf.2 (by decide)
  imod saved_pred_alloc Ψ DFrac.discard DFrac.valid_discard with #Hpost
  icases Hpost with ⟨%post, #Hpost⟩
  imod token_alloc with Hcol
  icases Hcol with ⟨%col, Hcol⟩
  imod append_frame W a cid γn L (.call fm bs post col) Hif $$ Hti Hc Hcl [HSd]
    with ⟨%HLl, Hcl, #Hlb⟩
  · unfold frameDeposit; iexists S, Ψ; iframe #; iframe; ipureintro; exact HS
  have hidx : uint.nat (W64 (L.length : Int)) = L.length := by
    have : (L.length : Int) < 2 ^ 64 := by omega
    word
  wp_apply (wp_mapInsert go.uint64 mp m (W64 L.length) pcl) $$ [$Hm] as Hm
  wp_apply sync.Mutex.Unlock.wp_proof _ (muInv γn t)
    $$ [$Hsync $Hmu $Hlkm Hpend Hm Hsd Hsdl Hal Hful Hcol]
  · unfold muInv; iexists _, _, false; simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hpend Hm Hsd Hsdl
    ileft
    unfold pendAlive
    iapply BigSepM.bigSepM_insert_elim $$ [Hful Hcol] Hal
    unfold callRes
    iexists L ++ [.call fm bs post col], fm, bs, post, col, ch, γf, Ψ
    iframe #; iframe
    ipureintro; rw [hidx]; simp
  rw [show (tagCall : val) = #(W64 0) from rfl]
  wp_apply encodeMsg.wp_proof $$ [$Hpkg $Hreq] as %rs ⟨Hrs, Hreq⟩
  ihave %Hrsl := ownSlice_len _ _ _ $$ Hrs
  have hml : (msgOf (W64 0) (W64 L.length) fm bs).length < 2 ^ 63 := by
    rw [Hrsl.1]; exact sint_nat_lt _
  have HLb' : ∀ q ∈ cmsgs (L ++ [.call fm bs post col]), q.length < 2 ^ 63 := by
    intro q hq
    rw [cmsgs_snoc] at hq
    rcases List.mem_append.1 hq with hq | hq
    · exact HLb q hq
    · simp only [List.mem_singleton] at hq; subst hq; exact hml
  have hfr : framesOf (cmsgs L) ++ frameOf (msgOf (W64 0) (W64 L.length) fm bs) =
      framesOf (cmsgs (L ++ [.call fm bs post col])) := by
    rw [cmsgs_snoc, net.rpc.framesOf_concat]; rfl
  ihave #Hpr : (□ reqProto W a cid (framesOf (cmsgs L) ++
      frameOf (msgOf (W64 0) (W64 L.length) fm bs)) : IProp GF) $$ []
  · iintro !>
    unfold reqProto
    iexists γn.conn, L ++ [.call fm bs post col]
    iframe #
    ipureintro
    rw [hfr]
    exact ⟨HLb', List.prefix_refl _⟩
  wp_apply writeFrame.wp_proof $$ [$Hnet $Hci $Hstok $Hpr $Hrs] as %err ⟨%k, %Hk, #Herr, Hstok, Hrs⟩
  rcases err with ei | _
  · unfold connIface
    icases Hci with ⟨%cc, %Hcv, #Hcc⟩
    subst Hcv
    dsimp only
    wp_auto
    wp_apply net.TCPConn.Close.wp_proof cc cid false $$ [$Hnet $Hcc] as %err2 -
    wp_apply sync.Mutex.Lock.wp_proof _ _ $$ [$Hsync $Hmu] as ⟨Hlkm, HR⟩
    iunfold muInv at HR
    icases HR with ⟨%mp2, %m2, %sd2, Hpend, Hm, Hsd, Hsdl, Hal⟩
    wp_auto
    imod sdl_shut γn sd2 $$ Hsdl with ⟨Hsdl, #Hsh⟩
    wp_apply sync.Mutex.Unlock.wp_proof _ (muInv γn t)
      $$ [$Hsync $Hmu $Hlkm Hpend Hm Hsd Hsdl Hal]
    · unfold muInv; iexists _, _, true; simp only [↓reduceIte]; iframe Hpend Hm Hsd Hsdl
      icases Hal with (H | ⟨Hd, %h⟩)
      · ileft; iexact H
      · iright; iframe; ipureintro; exact ⟨h.1, trivial⟩
    wp_apply sync.Mutex.Unlock.wp_proof _ (sendInv γn t cid W a)
      $$ [$Hsync $Hsend $Hlks Hseq Hstok Hcl]
    · unfold sendInv; iexists _, _, _; iframe; isplitr
      · ipureintro; exact HLb'
      iright; iexact Hsh
    wp_apply sync.Mutex.Lock.wp_proof _ _ $$ [$Hsync $Hmu] as ⟨Hlkm, HR⟩
    iunfold muInv at HR
    icases HR with ⟨%mp3, %m3, %sd3, Hpend, Hm, Hsd, Hsdl, Hal⟩
    wp_auto
    wp_apply (wp_map_lookup2 go.uint64 (go.GoType.PointerType pendingCall.ty) mp3 m3
      (W64 L.length)) $$ [$Hm] as Hm
    wp_apply (wp_mapDelete mp3 m3 (W64 L.length) go.uint64
      (go.GoType.PointerType pendingCall.ty)) $$ [$Hm] as Hm
    ihave Hal := pend_delete γn m3 sd3 (W64 L.length) $$ Hal
    wp_apply sync.Mutex.Unlock.wp_proof _ (muInv γn t)
      $$ [$Hsync $Hmu $Hlkm Hpend Hm Hsd Hsdl Hal]
    · unfold muInv; iexists _, _, _; iframe
    cases (m3 !! W64 L.length).isSome
    · wp_auto
      iapply HΦ
      simp only [↓reduceIte]
      unfold sentCall
      iexists ch, γf
      iframe #; iframe
    · wp_auto
      iapply HΦ; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  · have hk : k = (frameOf (msgOf (W64 0) (W64 L.length) fm bs)).length := Hk.2.1 rfl
    subst hk
    rw [List.take_length]
    dsimp only
    wp_auto
    wp_apply sync.Mutex.Unlock.wp_proof _ (sendInv γn t cid W a)
      $$ [$Hsync $Hsend $Hlks Hseq Hstok Hcl]
    · unfold sendInv; iexists _, _, _; iframe; isplitr
      · ipureintro; exact HLb'
      ileft; ipureintro
      refine ⟨?_, hfr⟩
      simp only [List.length_append, List.length_singleton]
      push_cast; word
    iapply HΦ
    simp only [↓reduceIte]
    unfold sentCall
    iexists ch, γf
    iframe #; iframe

theorem transport.cancel.wp_proof : transport.cancel.spec (GF := GF) (hG := hG) := by
  intro t W a target
  wp_start as #Ht
  ihave ⟨-, -, #Hnet, #Hsync, -, -, -⟩ := client_deps $$ Hpkg
  unfold isTransport isTransportN
  icases Ht with ⟨%cv, %cid, %γn, #Hconn, #Hci, #Hc, #Hsend, #Hmu, #Hti⟩
  wp_auto
  wp_apply sync.Mutex.Lock.wp_proof _ _ $$ [$Hsync $Hsend] as ⟨Hlks, HSi⟩
  wp_apply sync.Mutex.Lock.wp_proof _ _ $$ [$Hsync $Hmu] as ⟨Hlkm, HR⟩
  iunfold muInv at HR
  icases HR with ⟨%mp, %m, %sd, Hpend, Hm, Hsd, Hsdl, Hal⟩
  iunfold sendInv at HSi
  icases HSi with ⟨%L, %sq, %Wb, Hseq, Hstok, Hcl, %HLb, HSr⟩
  cases sd
  rotate_left
  · wp_auto
    imod sdl_shut γn true $$ Hsdl with ⟨Hsdl, #Hsh⟩
    wp_apply sync.Mutex.Unlock.wp_proof _ (muInv γn t)
      $$ [$Hsync $Hmu $Hlkm Hpend Hm Hsd Hsdl Hal]
    · unfold muInv; iexists _, _, true; simp only [↓reduceIte]; iframe
    wp_apply sync.Mutex.Unlock.wp_proof _ (sendInv γn t cid W a)
      $$ [$Hsync $Hsend $Hlks Hseq Hstok Hcl]
    · unfold sendInv; iexists _, _, _; iframe; isplitr
      · ipureintro; exact HLb
      iright; iexact Hsh
    iapply HΦ; itrivial
  simp only [Bool.false_eq_true, ↓reduceIte]
  wp_auto
  wp_if_destruct
  · imod sdl_shut0 γn $$ Hsdl with ⟨Hsdl, #Hsh⟩
    wp_apply sync.Mutex.Unlock.wp_proof _ (muInv γn t)
      $$ [$Hsync $Hmu $Hlkm Hpend Hm Hsd Hsdl Hal]
    · unfold muInv; iexists _, _, true; simp only [↓reduceIte]; iframe Hpend Hm Hsd Hsdl
      icases Hal with (H | ⟨Hd, %h⟩)
      · ileft; iexact H
      · iright; iframe; ipureintro; exact ⟨h.1, trivial⟩
    wp_apply sync.Mutex.Unlock.wp_proof _ (sendInv γn t cid W a)
      $$ [$Hsync $Hsend $Hlks Hseq Hstok Hcl]
    · unfold sendInv; iexists _, _, _; iframe; isplitr
      · ipureintro; exact HLb
      iright; iexact Hsh
    iapply HΦ; itrivial
  icases HSr with (%HSr | #Hsh)
  rotate_left
  · unfold shutLb
    ihave %Hc := mono_list_auth_lb_valid _ _ _ _ $$ Hsdl Hsh
    exfalso; simp at Hc
  obtain ⟨rfl, rfl⟩ := HSr
  wp_apply sync.Mutex.Unlock.wp_proof _ (muInv γn t)
    $$ [$Hsync $Hmu $Hlkm Hpend Hm Hsd Hsdl Hal]
  · unfold muInv; iexists _, _, false; simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hpend Hm Hsd Hsdl
    icases Hal with (H | ⟨-, %h⟩)
    · ileft; iexact H
    · exfalso; exact h.2
  imod append_frame W a cid γn L (.cancel target) Hif $$ Hti Hc Hcl [] with ⟨%HLl, Hcl, #Hlb⟩
  · unfold frameDeposit; itrivial
  rw [show (tagCancel : val) = #(W64 1) from rfl]
  ihave Hnil := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
  wp_apply encodeMsg.wp_proof (W64 1) target [] slice.nil (DFrac.own 1) [] $$ [$Hpkg $Hnil]
    as %rs ⟨Hrs, -⟩
  ihave %Hrsl := ownSlice_len _ _ _ $$ Hrs
  have hml : (msgOf (W64 1) target [] []).length < 2 ^ 63 := by
    rw [Hrsl.1]; exact sint_nat_lt _
  have HLb' : ∀ q ∈ cmsgs (L ++ [.cancel target]), q.length < 2 ^ 63 := by
    intro q hq
    rw [cmsgs_snoc] at hq
    rcases List.mem_append.1 hq with hq | hq
    · exact HLb q hq
    · simp only [List.mem_singleton] at hq; subst hq; exact hml
  have hfr : framesOf (cmsgs L) ++ frameOf (msgOf (W64 1) target [] []) =
      framesOf (cmsgs (L ++ [.cancel target])) := by
    rw [cmsgs_snoc, net.rpc.framesOf_concat]; rfl
  ihave #Hpr : (□ reqProto W a cid (framesOf (cmsgs L) ++
      frameOf (msgOf (W64 1) target [] [])) : IProp GF) $$ []
  · iintro !>
    unfold reqProto
    iexists γn.conn, L ++ [.cancel target]
    iframe #
    ipureintro
    rw [hfr]
    exact ⟨HLb', List.prefix_refl _⟩
  wp_apply writeFrame.wp_proof $$ [$Hnet $Hci $Hstok $Hpr $Hrs] as %err ⟨%k, %Hk, #Herr, Hstok, Hrs⟩
  rcases err with ei | _
  · unfold connIface
    icases Hci with ⟨%cc, %Hcv, #Hcc⟩
    subst Hcv
    dsimp only
    wp_auto
    wp_apply net.TCPConn.Close.wp_proof cc cid false $$ [$Hnet $Hcc] as %err2 -
    wp_apply sync.Mutex.Lock.wp_proof _ _ $$ [$Hsync $Hmu] as ⟨Hlkm, HR⟩
    iunfold muInv at HR
    icases HR with ⟨%mp2, %m2, %sd2, Hpend, Hm, Hsd, Hsdl, Hal⟩
    wp_auto
    imod sdl_shut γn sd2 $$ Hsdl with ⟨Hsdl, #Hsh⟩
    wp_apply sync.Mutex.Unlock.wp_proof _ (muInv γn t)
      $$ [$Hsync $Hmu $Hlkm Hpend Hm Hsd Hsdl Hal]
    · unfold muInv; iexists _, _, true; simp only [↓reduceIte]; iframe Hpend Hm Hsd Hsdl
      icases Hal with (H | ⟨Hd, %h⟩)
      · ileft; iexact H
      · iright; iframe; ipureintro; exact ⟨h.1, trivial⟩
    wp_apply sync.Mutex.Unlock.wp_proof _ (sendInv γn t cid W a)
      $$ [$Hsync $Hsend $Hlks Hseq Hstok Hcl]
    · unfold sendInv; iexists _, _, _; iframe; isplitr
      · ipureintro; exact HLb'
      iright; iexact Hsh
    iapply HΦ; itrivial
  · have hk : k = (frameOf (msgOf (W64 1) target [] [])).length := Hk.2.1 rfl
    subst hk
    rw [List.take_length]
    dsimp only
    wp_auto
    wp_apply sync.Mutex.Unlock.wp_proof _ (sendInv γn t cid W a)
      $$ [$Hsync $Hsend $Hlks Hseq Hstok Hcl]
    · unfold sendInv; iexists _, _, _; iframe; isplitr
      · ipureintro; exact HLb'
      ileft; ipureintro
      refine ⟨?_, hfr⟩
      simp only [List.length_append, List.length_singleton]
      push_cast; word
    iapply HΦ; itrivial

theorem transport.input.wp_proof : transport.input.spec (GF := GF) (hG := hG) := by
  intro t W a cv cid γn
  wp_start as ⟨#Ht, Hown⟩
  ihave ⟨-, -, #Hnet, #Hsync, -, -, -⟩ := client_deps $$ Hpkg
  unfold isTransportN
  icases Ht with ⟨#Hconn, #Hci, #Hc, #Hsend, #Hmu, #Hti⟩
  wp_auto
  wp_for
  iunfold readerOwn at Hown
  icases Hown with ⟨%Q, Hrt, Hdead, %HQ⟩
  wp_apply readFrame.wp_proof $$ [$Hnet $Hpkg $Hci $Hrt] as %p %rerr ⟨%data, Hrt, Hr⟩
  icases Hr with (⟨%Hrerr, %pl, %Hpl, Hp⟩ | ⟨%Hrerr, -⟩)
  rotate_left
  · rcases rerr with ei | _
    · wp_auto
      wp_for_post
      iclear Hrt
      unfold connIface
      icases Hci with ⟨%cc, %Hcv, #Hcc⟩
      subst Hcv
      wp_auto
      wp_apply net.TCPConn.Close.wp_proof cc cid false $$ [$Hnet $Hcc] as %err2 -
      wp_apply sync.Mutex.Lock.wp_proof _ _ $$ [$Hsync $Hsend] as ⟨Hlks, HS⟩
      wp_apply sync.Mutex.Lock.wp_proof _ _ $$ [$Hsync $Hmu] as ⟨Hlkm, HR⟩
      iunfold muInv at HR
      icases HR with ⟨%mp, %m, %sd, Hpend, Hm, Hsd, Hsdl, Hal⟩
      icases Hal with (Hal | ⟨Hd2, -⟩)
      rotate_left
      · iexfalso; iapply token_exclusive $$ Hdead Hd2
      imod sdl_shut γn sd $$ Hsdl with ⟨Hsdl, -⟩
      unfold pendAlive
      wp_auto
      wp_func_lits
      wp_bind (App (App (Val (map.forRange _ _)) _) _)
      iapply (wp_map_for_range (K := w64) (V := Loc) (fun keys (i : Int) => iprop(⌜0 ≤ i⌝ ∗
          (∃ r : GMap w64 Loc, ⌜∀ (j : Nat) (k : w64), i ≤ (j : Int) → keys[j]? = some k →
              r !! k = m !! k⌝ ∗ [∗map] s ↦ pc ∈ r, callRes γn s pc) ∗
          ∃ pv : Loc, pc_ptr ↦ pv))) $$ Hm
      iintro %keys %hkeys
      isplitl [Hal pc]
      · isplitr
        · ipureintro; omega
        isplitl [Hal]
        · iexists m
          isplitr
          · ipureintro; intro j k _ _; rfl
          iexact Hal
        iexists _; iexact pc
      isplitl []
      · imodintro
        iintro %i %key %v ⟨%hk1, %hk2⟩ ⟨%hi, ⟨%r, %hr, Hr⟩, %pv, Hpc⟩
        have hrk : r !! key = some v := by rw [hr i.toNat key (by omega) hk1]; exact hk2
        icases (BigSepM.bigSepM_delete (show get? r key = some v from hrk)).1 $$ Hr
          with ⟨Hres, Hr⟩
        unfold callRes
        icases Hres with ⟨%L, %fm, %b', %post, %col, %ch, %γf, %Ψ, -, -, #Hdone, #Hfut, Hful, -, -⟩
        wp_auto
        wp_apply (wp_future_fulfill (t := go.GoType.PointerType response.ty) γf ch null)
          $$ [$Hfut Hful]
        · unfold Fulfilled; iexists _; iframe; unfold callDone; ileft; ipureintro; rfl
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
        iexists _; iexact Hpc
      iintro ⟨%hi, -, %pv, Hpc⟩ Hm
      wp_auto
      wp_apply (wp_map_make1 (K := w64) (V := Loc) go.uint64 (go.GoType.PointerType pendingCall.ty))
        as %mp' Hm'
      wp_apply sync.Mutex.Unlock.wp_proof _ (muInv γn t)
        $$ [$Hsync $Hmu $Hlkm Hpend Hm' Hsd Hsdl Hdead]
      · unfold muInv; iexists _, _, true; simp only [↓reduceIte]; iframe
        iright; iframe; ipureintro; exact ⟨rfl, trivial⟩
      wp_apply sync.Mutex.Unlock.wp_proof _ (sendInv γn t cid W a) $$ [$Hsync $Hsend $Hlks $HS]
      iapply HΦ; itrivial
    · exact absurd rfl Hrerr.1
  subst Hrerr
  wp_auto
  wp_apply (lc := 2) decodeMsg.wp_proof $$ [$Hpkg $Hp] as %code %seq %msg %body %ok Hd
  cases ok
  · wp_auto
    wp_for_post
    iclear Hrt
    unfold connIface
    icases Hci with ⟨%cc, %Hcv, #Hcc⟩
    subst Hcv
    wp_auto
    wp_apply net.TCPConn.Close.wp_proof cc cid false $$ [$Hnet $Hcc] as %err2 -
    wp_apply sync.Mutex.Lock.wp_proof _ _ $$ [$Hsync $Hsend] as ⟨Hlks, HS⟩
    wp_apply sync.Mutex.Lock.wp_proof _ _ $$ [$Hsync $Hmu] as ⟨Hlkm, HR⟩
    iunfold muInv at HR
    icases HR with ⟨%mp, %m, %sd, Hpend, Hm, Hsd, Hsdl, Hal⟩
    icases Hal with (Hal | ⟨Hd2, -⟩)
    rotate_left
    · iexfalso; iapply token_exclusive $$ Hdead Hd2
    imod sdl_shut γn sd $$ Hsdl with ⟨Hsdl, -⟩
    unfold pendAlive
    wp_auto
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply (wp_map_for_range (K := w64) (V := Loc) (fun keys (i : Int) => iprop(⌜0 ≤ i⌝ ∗
        (∃ r : GMap w64 Loc, ⌜∀ (j : Nat) (k : w64), i ≤ (j : Int) → keys[j]? = some k →
            r !! k = m !! k⌝ ∗ [∗map] s ↦ pc ∈ r, callRes γn s pc) ∗
        ∃ pv : Loc, pc_ptr ↦ pv))) $$ Hm
    iintro %keys %hkeys
    isplitl [Hal pc]
    · isplitr
      · ipureintro; omega
      isplitl [Hal]
      · iexists m
        isplitr
        · ipureintro; intro j k _ _; rfl
        iexact Hal
      iexists _; iexact pc
    isplitl []
    · imodintro
      iintro %i %key %v ⟨%hk1, %hk2⟩ ⟨%hi, ⟨%r, %hr, Hr⟩, %pv, Hpc⟩
      have hrk : r !! key = some v := by rw [hr i.toNat key (by omega) hk1]; exact hk2
      icases (BigSepM.bigSepM_delete (show get? r key = some v from hrk)).1 $$ Hr
        with ⟨Hres, Hr⟩
      unfold callRes
      icases Hres with ⟨%L, %fm, %b', %post, %col, %ch, %γf, %Ψ, -, -, #Hdone, #Hfut, Hful, -, -⟩
      wp_auto
      wp_apply (wp_future_fulfill (t := go.GoType.PointerType response.ty) γf ch null)
        $$ [$Hfut Hful]
      · unfold Fulfilled; iexists _; iframe; unfold callDone; ileft; ipureintro; rfl
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
      iexists _; iexact Hpc
    iintro ⟨%hi, -, %pv, Hpc⟩ Hm
    wp_auto
    wp_apply (wp_map_make1 (K := w64) (V := Loc) go.uint64 (go.GoType.PointerType pendingCall.ty))
      as %mp' Hm'
    wp_apply sync.Mutex.Unlock.wp_proof _ (muInv γn t)
      $$ [$Hsync $Hmu $Hlkm Hpend Hm' Hsd Hsdl Hdead]
    · unfold muInv; iexists _, _, true; simp only [↓reduceIte]; iframe
      iright; iframe; ipureintro; exact ⟨rfl, trivial⟩
    wp_apply sync.Mutex.Unlock.wp_proof _ (sendInv γn t cid W a) $$ [$Hsync $Hsend $Hlks $HS]
    iapply HΦ; itrivial
  simp only [↓reduceIte]
  icases Hd with ⟨%b, ⟨%Hplb, %Hmsgl⟩, Hbody⟩
  obtain ⟨hdata, hpll⟩ := Hpl
  subst hdata
  ihave ⟨Hrt, %γ, %x, #Hc', #Hx, %Hxp⟩ := resp_parse W a cid Q pl HQ hpll $$ Hrt
  ihave %Hγ := cl_isGConn_agree W a cid γn.conn γ $$ Hc Hc'
  subst Hγ
  imod ans_bound W a cid γn x.1 x.2 $$ Hti Hc Hx with %Hx1
  have hlx : (respMsg x).length < 2 ^ 63 := by rw [Hxp]; exact hpll
  obtain ⟨i, xc, xm, xb⟩ := x
  simp only [respMsg] at Hxp hlx
  rw [msgOf_length] at hlx
  rw [Hplb] at Hxp
  obtain ⟨hcode, hseq, hmsg, hb⟩ := msgOf_inj (by omega) Hmsgl Hxp
  subst hcode hmsg hb hseq
  have hidx : uint.nat (W64 (i : Int)) = i := by
    have : (i : Int) < 2 ^ 64 := by omega
    word
  have hQ' : ∀ q ∈ Q ++ [pl], q.length < 2 ^ 63 := by
    intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact HQ q hq
    · simp only [List.mem_singleton] at hq; subst hq; exact hpll
  ihave Hrt : recvTok cid false (respProto W a) (framesOf (Q ++ [pl])) $$ [Hrt]
  · rw [net.rpc.framesOf_concat]; iexact Hrt
  wp_auto
  wp_apply sync.Mutex.Lock.wp_proof _ _ $$ [$Hsync $Hmu] as ⟨Hlkm, HR⟩
  iunfold muInv at HR
  icases HR with ⟨%mp, %m, %sd, Hpend, Hm, Hsd, Hsdl, Hal⟩
  icases Hal with (Hal | ⟨Hd2, -⟩)
  rotate_left
  · iexfalso; iapply token_exclusive $$ Hdead Hd2
  wp_auto
  wp_apply (wp_map_lookup2 go.uint64 (go.GoType.PointerType pendingCall.ty) mp m
    (W64 (i : Int))) $$ [$Hm] as Hm
  wp_apply (wp_mapDelete mp m (W64 (i : Int)) go.uint64
    (go.GoType.PointerType pendingCall.ty)) $$ [$Hm] as Hm
  unfold pendAlive
  cases hm : m !! W64 (i : Int) with
  | none =>
    rw [GMap.delete_notin m _ hm]
    wp_apply sync.Mutex.Unlock.wp_proof _ (muInv γn t)
      $$ [$Hsync $Hmu $Hlkm Hpend Hm Hsd Hsdl Hal]
    · unfold muInv; iexists _, _, _; iframe; ileft; unfold pendAlive; iexact Hal
    wp_for_post
    iframe
    unfold readerOwn
    iexists Q ++ [pl]
    iframe
    ipureintro; exact hQ'
  | some pc =>
    icases (BigSepM.bigSepM_delete (show get? m (W64 (i : Int)) = some pc from hm)).1 $$ Hal
      with ⟨Hres, Hal⟩
    wp_apply sync.Mutex.Unlock.wp_proof _ (muInv γn t)
      $$ [$Hsync $Hmu $Hlkm Hpend Hm Hsd Hsdl Hal]
    · unfold muInv; iexists _, _, _; iframe; ileft; unfold pendAlive; iexact Hal
    unfold callRes
    icases Hres with ⟨%L, %fm, %b', %post, %col, %ch, %γf, %Ψ, #Hlb, %HL, #Hdone, #Hfut, Hful,
      #Hpost, Hcol⟩
    rw [hidx] at HL
    imod collect W a cid γn.conn L i fm b' post col xc xm xb Ψ HL $$ Hc Hlb Hx Hcol Hpost Hlc1
      Hlc2 with ⟨HΨ, %Hcb⟩
    simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
    wp_auto
    irename «$v» => Hr
    generalize «$v_ptr» = r at *
    iStructNamed Hr
    wp_apply (wp_future_fulfill (t := go.GoType.PointerType response.ty) γf ch r)
      $$ [$Hfut Hful HΨ code msg body Hbody]
    · unfold Fulfilled; iexists _; iframe Hful
      unfold callDone; iright
      iexists xc, xm, body, xb
      iframe
      ipureintro; exact Hcb
    wp_for_post
    iframe
    unfold readerOwn
    iexists Q ++ [pl]
    iframe
    ipureintro; exact hQ'

theorem statusErrOf_ne (err : GoInterface) (c : w32) (msg : GoString) :
    status.statusErrOf (GF := GF) err c msg ⊢ ⌜err ≠ interface.nil⌝ := by
  unfold status.statusErrOf
  iintro ⟨%e, %st, ⟨%h, -⟩, -⟩
  ipureintro; subst h; simp [interface.mkOk]

/-- `status.Error(c, msg)` for a code that is not `OK`. -/
theorem wp_statusError (c : w32) (msg : GoString) (hc : c ≠ W32 0) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status }}
      (App (App (Val (@! google_golang_org.grpc.status.Error)) (Val #c)) (Val #msg))
    {{ (err : GoInterface), RET #err; ⌜err ≠ interface.nil⌝ ∗ status.statusErrOf err c msg }} := by
  iintro %Φ #Hpkg HΦ
  wp_apply status.Error.wp_proof $$ [$Hpkg] as %err Herr
  unfold status.errPost
  icases Herr with (%h | #H)
  · exact absurd h.1 hc
  · ihave %Hne := statusErrOf_ne _ _ _ $$ H
    iapply HΦ; iframe H; ipureintro; exact Hne

theorem ClientConn.getTransport.wp_proof : ClientConn.getTransport.spec (GF := GF) (hG := hG) := by
  intro cc W a
  wp_start as #Hcc
  ihave ⟨-, -, #Hnet, #Hsync, -, #Hst, -⟩ := client_deps $$ Hpkg
  unfold isClientConn
  icases Hcc with ⟨#Htg, #Hmu, #Ha⟩
  wp_auto
  wp_apply sync.Mutex.Lock.wp_proof _ _ $$ [$Hsync $Hmu] as ⟨Hlk, HR⟩
  iunfold ccInv at HR
  icases HR with ⟨%t, %cl, Ht, Hcl, Hto⟩
  cases cl
  rotate_left
  · wp_auto
    wp_apply sync.Mutex.Unlock.wp_proof _ (ccInv cc W a) $$ [$Hsync $Hmu $Hlk Ht Hcl Hto]
    · unfold ccInv; iexists _, _; iframe
    wp_apply wp_statusError _ _ (by decide) $$ [$Hst] as %err ⟨%Hne, #H⟩
    iapply HΦ; iright
    isplitr
    · ipureintro; exact Hne
    iexists _, _; iexact H
  unfold grpcAddr
  icases Ha with ⟨#Hap, #Hreg⟩
  wp_auto
  by_cases htn : t = null
  · subst htn
    wp_auto
    wp_apply net.Dial.wp_proof a (reqProto W a) (respProto W a) $$ [$Hnet $Hap] as %cv %err Hres
    unfold net.newConnResult
    icases Hres with (⟨%c, %cid, ⟨%Hcv, %Herr⟩, #Hc, ⟨Hstok, Hrtok⟩, Hfr⟩ |
      ⟨%i, ⟨%Hcv, %Herr⟩, %code, -, #Hoe⟩)
    rotate_left
    · subst Hcv Herr
      wp_auto
      wp_apply sync.Mutex.Unlock.wp_proof _ (ccInv cc W a) $$ [$Hsync $Hmu $Hlk Ht Hcl]
      · unfold ccInv; iexists _, _; iframe; first | (ileft; ipureintro; rfl) | (iright; iexact Htr)
      wp_apply wp_statusError _ _ (by decide) $$ [$Hst] as %err ⟨%Hne, #H⟩
      iapply HΦ; iright
      isplitr
      · ipureintro; exact Hne
      iexists _, _; iexact H
    subst Hcv Herr
    wp_auto
    imod conn_register W a cid $$ Hreg Hfr with ⟨%γ, #Hgc, Hreqs⟩
    ihave #Hci : connIface (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c) cid false $$ []
    · unfold connIface; iexists c; iframe #; ipureintro; rfl
    wp_apply newTransport.wp_proof transport.input.wp_proof W a _ cid γ
      $$ [$Hpkg $Hci $Hgc $Hreqs $Hstok $Hrtok] as %t2 #Ht2
    wp_apply sync.Mutex.Unlock.wp_proof _ (ccInv cc W a) $$ [$Hsync $Hmu $Hlk Ht Hcl]
    · unfold ccInv; iexists _, _; iframe; iright; iexact Ht2
    iapply HΦ; ileft; iframe Ht2; ipureintro; rfl
  · icases Hto with (%h | #Htr)
    · exact absurd h htn
    rw [decide_eq_false htn]
    wp_auto
    wp_apply transport.isShutdown.wp_proof $$ [$Hpkg $Htr] as %b -
    cases b
    · wp_auto
      wp_apply sync.Mutex.Unlock.wp_proof _ (ccInv cc W a) $$ [$Hsync $Hmu $Hlk Ht Hcl]
      · unfold ccInv; iexists _, _; iframe; iright; iexact Htr
      iapply HΦ; ileft; iframe Htr; ipureintro; rfl
    · wp_auto
      wp_apply net.Dial.wp_proof a (reqProto W a) (respProto W a) $$ [$Hnet $Hap] as %cv %err Hres
      unfold net.newConnResult
      icases Hres with (⟨%c, %cid, ⟨%Hcv, %Herr⟩, #Hc, ⟨Hstok, Hrtok⟩, Hfr⟩ |
        ⟨%i, ⟨%Hcv, %Herr⟩, %code, -, #Hoe⟩)
      rotate_left
      · subst Hcv Herr
        wp_auto
        wp_apply sync.Mutex.Unlock.wp_proof _ (ccInv cc W a) $$ [$Hsync $Hmu $Hlk Ht Hcl]
        · unfold ccInv; iexists _, _; iframe; first | (ileft; ipureintro; rfl) | (iright; iexact Htr)
        wp_apply wp_statusError _ _ (by decide) $$ [$Hst] as %err ⟨%Hne, #H⟩
        iapply HΦ; iright
        isplitr
        · ipureintro; exact Hne
        iexists _, _; iexact H
      subst Hcv Herr
      wp_auto
      imod conn_register W a cid $$ Hreg Hfr with ⟨%γ, #Hgc, Hreqs⟩
      ihave #Hci : connIface (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c) cid false $$ []
      · unfold connIface; iexists c; iframe #; ipureintro; rfl
      wp_apply newTransport.wp_proof transport.input.wp_proof W a _ cid γ
        $$ [$Hpkg $Hci $Hgc $Hreqs $Hstok $Hrtok] as %t2 #Ht2
      wp_apply sync.Mutex.Unlock.wp_proof _ (ccInv cc W a) $$ [$Hsync $Hmu $Hlk Ht Hcl]
      · unfold ccInv; iexists _, _; iframe; iright; iexact Ht2
      iapply HΦ; ileft; iframe Ht2; ipureintro; rfl

theorem ClientConn.Close.wp_proof : ClientConn.Close.spec (GF := GF) (hG := hG) := by
  intro cc W a
  wp_start as #Hcc
  ihave ⟨-, -, #Hnet, #Hsync, -, #Hst, -⟩ := client_deps $$ Hpkg
  unfold isClientConn
  icases Hcc with ⟨#Htg, #Hmu, #Ha⟩
  wp_auto
  wp_apply sync.Mutex.Lock.wp_proof _ _ $$ [$Hsync $Hmu] as ⟨Hlk, HR⟩
  iunfold ccInv at HR
  icases HR with ⟨%t, %cl, Ht, Hcl, Hto⟩
  cases cl
  rotate_left
  · wp_auto
    wp_apply sync.Mutex.Unlock.wp_proof _ (ccInv cc W a) $$ [$Hsync $Hmu $Hlk Ht Hcl Hto]
    · unfold ccInv; iexists _, _; iframe
    wp_apply wp_statusError _ _ (by decide) $$ [$Hst] as %err ⟨%Hne, #H⟩
    iapply HΦ; iright; iexists _, _; iexact H
  wp_auto
  wp_apply sync.Mutex.Unlock.wp_proof _ (ccInv cc W a) $$ [$Hsync $Hmu $Hlk Ht Hcl]
  · unfold ccInv; iexists _, _; iframe; ileft; ipureintro; rfl
  by_cases htn : t = null
  · subst htn
    wp_auto
    iapply HΦ; ileft; ipureintro; rfl
  · icases Hto with (%h | #Htr)
    · exact absurd h htn
    rw [decide_eq_false htn]
    unfold isTransport isTransportN
    icases Htr with ⟨%cv, %cid, %γn, #Hconn, #Hci, -⟩
    unfold connIface
    icases Hci with ⟨%c, %Hcv, #Hc⟩
    subst Hcv
    wp_auto
    wp_apply net.TCPConn.Close.wp_proof c cid false $$ [$Hnet $Hc] as %err2 -
    iapply HΦ; ileft; ipureintro; rfl

theorem newClientConn.wp_proof : newClientConn.spec (GF := GF) (hG := hG) := by
  intro W a opts dq os
  wp_start as ⟨#Ha, Hos⟩
  ihave ⟨-, -, -, #Hsync, -, -, -⟩ := client_deps $$ Hpkg
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hos
  ihave IH : (∃ (n : w64) (cr : Bool) (ov : DialOption),
      "i" ∷ i_ptr ↦ n ∗ "o" ∷ o_ptr ↦ ov ∗ "creds" ∷ creds_ptr ↦ cr ∗ "Hos" ∷ opts ↦*{dq} os ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (os.length : Int) ∧
        (cr = true ↔ ∃ j < (sint.Z n).toNat, ∃ d, os[j]? = some d ∧ d.creds' = true)⌝
      : IProp GF) $$ [i o creds Hos]
  · iexists _, false, _
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    simp
  wp_for IH
  wp_if_destruct
  · have Hlt : (sint.Z n).toNat < os.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, os[(sint.Z n).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z opts.len from ⟨Hn.1, Hif⟩]
    wp_apply wp_load_slice_index opts (sint.Z n) os dq x Hn.1 $$ [Hos] as Hos
    · iframe; ipureintro; exact Hx
    have hstep : (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 := by
      have : sint.Z (n + W64 1) = sint.Z n + 1 := by word
      omega
    cases hc : x.creds'
    · wp_auto
      wp_for_post
      iframe
      iexists _, cr, x
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [Hn.2.2, hstep]
      constructor
      · rintro ⟨j, hj, d, hd, hdc⟩; exact ⟨j, by omega, d, hd, hdc⟩
      · rintro ⟨j, hj, d, hd, hdc⟩
        refine ⟨j, ?_, d, hd, hdc⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
        · exact h
        · subst h; rw [Hx] at hd; cases hd; rw [hc] at hdc; cases hdc
    · wp_auto
      wp_for_post
      iframe
      iexists _, true, x
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      simp only [true_iff]
      exact ⟨(sint.Z n).toNat, by omega, x, Hx, hc⟩
  · have hall : (sint.Z n).toNat = os.length := by word
    rw [hall] at Hn
    cases cr
    · wp_auto
      ihave #Hi := isInit_access $$ Hpkg
      icases Hi with ⟨-, #HeT, -⟩
      icases net.rpc.newVar_errMsg' _ _ $$ HeT with ⟨%eT, #HeTp, #HeTm, -⟩
      ihave %HeTne := net.rpc.errMsg_ne_nil _ _ $$ HeTm
      wp_auto
      iapply HΦ
      iframe Hos
      unfold dialPost
      iright
      isplitr
      · ipureintro
        refine ⟨HeTne, rfl, fun o ho => ?_⟩
        cases hoc : o.creds'
        · rfl
        · exfalso
          obtain ⟨j, hjl, hj⟩ := List.getElem_of_mem ho
          have := (Hn.2.2).2 ⟨j, hjl, o, by rw [List.getElem?_eq_getElem hjl, hj], hoc⟩
          cases this
      iapply net.rpc.errMsg_errAny; iexact HeTm
    · iapply wp_fupd
      wp_auto
      irename «$r0» => Hcs
      generalize «$r0_ptr» = cc at *
      iStructNamed Hcs
      ipersist target
      imod sync.init_Mutex (ccInv cc W a) ⊤ _ $$ mu [t closed] with #Hmu
      · inext; unfold ccInv; iexists _, _; iframe; ileft; ipureintro; rfl
      imodintro
      iapply HΦ
      iframe Hos
      unfold dialPost
      ileft
      isplitr
      · ipureintro
        obtain ⟨j, hj, d, hd, hdc⟩ := (Hn.2.2).1 rfl
        exact ⟨rfl, d, List.mem_of_getElem? hd, hdc⟩
      unfold isClientConn
      iframe #

theorem Dial.wp_proof : Dial.spec (GF := GF) (hG := hG) := by
  intro W a opts dq os
  wp_start as ⟨#Ha, Hos⟩
  wp_auto
  wp_apply newClientConn.wp_proof $$ [$Hpkg $Ha $Hos] as %cc %err ⟨Hos, Hr⟩
  iapply HΦ; iframe

theorem NewClient.wp_proof : NewClient.spec (GF := GF) (hG := hG) := by
  intro W a opts dq os
  wp_start as ⟨#Ha, Hos⟩
  wp_auto
  wp_apply newClientConn.wp_proof $$ [$Hpkg $Ha $Hos] as %cc %err ⟨Hos, Hr⟩
  iapply HΦ; iframe

theorem DialContext.wp_proof : DialContext.spec (GF := GF) (hG := hG) := by
  intro W a ctx opts dq os
  wp_start as ⟨#Ha, Hos⟩
  wp_auto
  wp_apply newClientConn.wp_proof $$ [$Hpkg $Ha $Hos] as %cc %err ⟨Hos, Hr⟩
  iapply HΦ; iframe

/-- `encode(args)` with the encoding premise: the encoded deposit (and `R`), or a status error
with `R`. -/
theorem wp_encode (args : GoInterface) (S : UnarySpec GF) (Ψ : List w8 → IProp GF)
    (R : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ codecSet (GF := GF) ∗
        kitCodecOk (GF := GF) ∗ encPre args S Ψ R }}
      (App (Val (@! google_golang_org.grpc.encode)) (Val #args))
    {{ (s : GoSlice) (err : GoInterface), RET (PairV #s #err);
        (⌜err = interface.nil⌝ ∗ ∃ bs, s ↦* bs ∗ S bs Ψ ∗ R) ∨
        (⌜err ≠ interface.nil⌝ ∗ (∃ c msg, status.statusErrOf err c msg) ∗ R) }} := by
  wp_start as ⟨#Hcs, #Hko, Henc⟩
  ihave ⟨-, -, -, -, -, #Hst, #Hpb⟩ := client_deps $$ Hpkg
  unfold encPre
  icases Henc with (⟨%Hnil, HS, HR⟩ | ⟨%Hnn, Hm⟩)
  · subst Hnil
    wp_auto
    iapply HΦ; ileft; isplitr
    · ipureintro; rfl
    iexists []; iframe
    iapply ownSlice_nil
  · rcases args with i | _
    · wp_auto
      wp_apply google_golang_org.protobuf.proto.MarshalValue.wp_proof $$ [$Hpb $Hcs $Hko $Hm]
        as %sl %err Hr
      unfold google_golang_org.protobuf.proto.marshalPost
      icases Hr with (⟨%He, %bs, Hsl, HS, HR⟩ | ⟨%He, -, HR⟩)
      · subst He
        wp_auto
        iapply HΦ; ileft; isplitr
        · ipureintro; rfl
        iexists bs; iframe
      · rcases err with ei | _
        · wp_auto
          wp_apply wp_statusError _ _ (by decide) $$ [$Hst] as %err2 ⟨%Hne, #H⟩
          iapply HΦ; iright
          isplitr
          · ipureintro; exact Hne
          iframe HR; iexists _, _; iexact H
        · exact absurd rfl He
    · exact absurd rfl Hnn

theorem ClientConn.Invoke.wp_proof : ClientConn.Invoke.spec (GF := GF) (hG := hG) := by
  intro cc W a ctx cd fm S args reply opts Ψ R D Θ
  wp_start as ⟨#Hcs, #Hko, #Hcc, #Hctx, %HS, Henc, HD, #HDw⟩
  ihave ⟨#Hcx, -, #Hnet, #Hsync, -, #Hst, #Hpb⟩ := client_deps $$ Hpkg
  ihave #Hctx' : context.isContextDef ctx cd $$ [Hctx]
  · iexact Hctx
  unfold context.isContextDef
  icases Hctx' with ⟨-, #HDone, HErr, -⟩
  ihave #HE := HErr $$ %Broadcast.Unknown
  wp_auto
  wp_apply HE as %e - -
  by_cases he : e = interface.nil
  · subst he
    wp_auto
    wp_apply wp_encode args S Ψ R $$ [$Hpkg $Hcs $Hko $Henc] as %req %merr Hr
    icases Hr with (⟨%Hm, %bs, Hreq, HSd, HR⟩ | ⟨%Hm, ⟨%c, %msg, #H⟩, HR⟩)
    rotate_left
    · rcases merr with ei | _
      · wp_auto
        iapply HΦ; iright
        isplitr
        · ipureintro; exact Hm
        isplitr
        · iexists _, _; iexact H
        iframe
      · exact absurd rfl Hm
    subst Hm
    wp_auto
    wp_if_destruct
    · wp_apply wp_statusError _ _ (by decide) $$ [$Hst] as %err ⟨%Hne, #H⟩
      iapply HΦ; iright
      isplitr
      · ipureintro; exact Hne
      isplitr
      · iexists _, _; iexact H
      iframe
    wp_apply ClientConn.getTransport.wp_proof $$ [$Hpkg $Hcc] as %t %terr Htr
    icases Htr with (⟨%Hte, #Ht⟩ | ⟨%Hte, %c, %msg, #H⟩)
    rotate_left
    · rcases terr with ei | _
      · wp_auto
        have Hne := Hte
        iapply HΦ; iright
        isplitr
        · ipureintro; exact Hne
        isplitr
        · iexists _, _; iexact H
        iframe
      · exact absurd rfl Hte
    subst Hte
    wp_auto
    wp_apply transport.send.wp_proof t W a fm req bs S Ψ $$ [$Hpkg $Ht $Hreq $HSd]
      as %pc %seq %ok Hsc
    · ipureintro; exact HS
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte]
      wp_auto
      wp_apply wp_statusError _ _ (by decide) $$ [$Hst] as %err ⟨%Hne, #H⟩
      iapply HΦ; iright
      isplitr
      · ipureintro; exact Hne
      isplitr
      · iexists _, _; iexact H
      iframe
    simp only [↓reduceIte]
    unfold sentCall
    icases Hsc with ⟨%ch, %γf, #Hdone, #Hfut, Haw⟩
    wp_auto_lc 3
    wp_apply HDone as %ch2 %γch #Hcd
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · dsimp only [chan.blockingClausePre]
      ihave #Hch : isChan ch γf.chanName Loc $$ []
      · ihave #Hf := Hfut
        unfold isFuture
        icases Hf with ⟨#H, -⟩
        iexact H
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, ch, γf.chanName
      isplitr
      · ipureintro; rfl
      iframe Hch
      iapply future_await_au γf ch _ _ $$ Hfut [$Hlc1 $Hlc2 $Hlc3 $Haw]
      inext
      iintro %v %P %pre %post %Hsplit HP -
      have hP : P = callDone Ψ := by
        cases pre with
        | nil => simp at Hsplit; exact Hsplit.1.symm
        | cons x xs => simp at Hsplit
      subst hP
      wp_auto
      by_cases hv : v = null
      · subst hv
        wp_auto
        wp_apply wp_statusError _ _ (by decide) $$ [$Hst] as %err ⟨%Hne, #H⟩
        iapply HΦ; iright
        isplitr
        · ipureintro; exact Hne
        isplitr
        · iexists _, _; iexact H
        iframe
      unfold callDone
      icases HP with (%Hnull | ⟨%code, %msg, %body, %b, Hc, Hm, Hb, Hbody, %Hcb, HΨ⟩)
      · exact absurd Hnull hv
      rw [decide_eq_false hv]
      wp_auto
      have h0 : (W64 (uint.Z (W32 0)) : w64) = W64 0 := by decide
      rw [h0]
      by_cases hc : code = W64 0
      · subst hc
        simp only [↓reduceIte, _root_.decide_true, Bool.not_true]
        wp_auto
        wp_if_destruct
        · wp_apply wp_statusError _ _ (by decide) $$ [$Hst] as %err ⟨%Hne, #H⟩
          iapply HΦ; iright
          isplitr
          · ipureintro; exact Hne
          isplitr
          · iexists _, _; iexact H
          iframe
        ihave Hdec := HDw $$ HD %b
        wp_apply google_golang_org.protobuf.proto.UnmarshalValue.wp_proof body (DFrac.own 1) b
          reply (Θ b) $$ [$Hpb $Hcs $Hko $Hbody $Hdec] as %uerr ⟨%ok, Hbody, %Hiff, HΘ, Herr⟩
        cases ok
        · have hne : uerr ≠ interface.nil := fun h => by simp_all
          rcases uerr with ei | _
          · wp_auto
            wp_apply wp_statusError _ _ (by decide) $$ [$Hst] as %err ⟨%Hne, #H⟩
            iapply HΦ; iright
            isplitr
            · ipureintro; exact Hne
            isplitr
            · iexists _, _; iexact H
            iframe HR
            iright; iexists b; iexact HΘ
          · exact absurd rfl hne
        · have he : uerr = interface.nil := Hiff.2 rfl
          subst he
          wp_auto
          iapply HΦ; ileft
          isplitr
          · ipureintro; rfl
          iframe HR
          iexists b; iframe
      · rw [decide_eq_false hc]
        simp only [hc, ↓reduceIte, Bool.not_false]
        wp_auto
        have hc0 : (W32 (uint.Z code) : w32) ≠ W32 0 := by
          rcases Hcb with h | h
          · exact absurd h hc
          · have hz : uint.Z code ≠ 0 := by intro h0; apply hc; word
            intro heq
            apply hz
            have := congrArg (fun x : w32 => uint.Z x) heq
            rw [show uint.Z (W32 (uint.Z code)) = uint.Z code by word] at this
            rw [this]; rfl
        wp_apply wp_statusError _ _ hc0 $$ [$Hst] as %err ⟨%Hne, #H⟩
        iapply HΦ; iright
        isplitr
        · ipureintro; exact Hne
        isplitr
        · iexists _, _; iexact H
        iframe
    iapply BigAndL.bigAndL_cons.2
    isplit
    · dsimp only [chan.blockingClausePre]
      ihave #Hch2 := context.isContextDone_is_chan _ _ _ $$ Hcd
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch2, γch
      isplitr
      · ipureintro; rfl
      iframe Hch2
      iapply context.isContextDone_receive _ _ _ _ $$ Hcd
      iintro -
      wp_auto
      wp_apply transport.cancel.wp_proof $$ [$Hpkg $Ht]
      wp_apply ctxErr.wp_proof $$ [$Hpkg $Hctx] as %err ⟨%c, %msg, #H⟩
      ihave %Hne := statusErrOf_ne _ _ _ $$ H
      iapply HΦ; iright
      isplitr
      · ipureintro; exact Hne
      isplitr
      · iexists _, _; iexact H
      iframe
    · iapply BigAndL.bigAndL_nil.2
      itrivial
  · rcases e with i | _
    · wp_auto
      wp_apply ctxErr.wp_proof $$ [$Hpkg $Hctx] as %err ⟨%c, %msg, #H⟩
      ihave %Hne := statusErrOf_ne _ _ _ $$ H
      iapply HΦ; iright
      isplitr
      · ipureintro; exact Hne
      isplitr
      · iexists _, _; iexact H
      iframe
    · exact absurd rfl he

end proofs

end google_golang_org.grpc

end Perennial
