/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/N/ClientConn.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit N: an accepted client connection (`clientListener`, `WaitForClientConnections`)

What the acceptor of a replica's port `a0` learns from the first 4 bytes of a connection (the
dialer's handshake `hs`, `hs < peerMark`): the dialer is client `hs` on this connection
(`clientConnAt`), and the rest of its stream is whole requests (`clientReqsOk`); and what it may
write back (whole replies to `hs`: `gryffWireQ`). These build `clientConnIn`'s body for
`serveClient`.

Port (`Net/`): the listener is `Net/`'s (`listenerOwn`: `isListener`, its state `netLis`, owned,
at the wildcard `lisAddrOf a0`, with `a0`'s protocols `lisProto`); `Accept` with `accept_lis_au`
(a connection accepted at any address the wildcard takes, `a0`'s protocols); the reader is
dsv-bufio's over `net.conn_readerOk`, the writer contract `net.conn_streamWriterOk`; the
handshake's facts from the reader (`ownReader_protoNow`, `ownReader_sentLb`, `N/ConnLaws`); the
`net` specs through `netN.NetSpecs`.
-/
module

public import Dsverify.Proof.gryff.N.Serve
public import Dsverify.Proof.gryff.N.PeerMark
public import Proof.internal.poll.PkgInit
public import Perennial.Proof.encoding.binary.Results
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open wire Perennial.gryff.netN

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- A handshake below `peerMark` (`hs & PeerHandshake == 0`). -/
theorem lt_peerMark_of_and {hs : w32} (h : hs &&& W32 (2 ^ 31) = 0) : hs < peerMark := by
  unfold peerMark
  rw [BitVec.lt_def]
  have : (W32 (2 ^ 31)).toNat = 2 ^ 31 := by decide
  rw [this]
  have hb : hs.getLsbD 31 = false := by
    have := congrArg (fun x : w32 => x.getLsbD 31) h
    simpa using this
  apply Nat.lt_of_not_le
  intro hc
  have hlt : hs.toNat < 2 ^ 32 := hs.isLt
  have e31 : (2 : Nat) ^ 31 = 2147483648 := rfl
  have e32 : (2 : Nat) ^ 32 = 4294967296 := rfl
  rw [e31] at hc
  rw [e32] at hlt
  have hd : hs.toNat / 2147483648 = 1 := by omega
  have ht : hs.toNat.testBit 31 = true := by
    rw [Nat.testBit_eq_decide_div_mod_eq, e31, hd]; rfl
  rw [BitVec.getLsbD, ht] at hb
  exact Bool.noConfusion hb

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [wire.BinaryVarintHyps GF] [net.Assumptions] [net.FieldAssumptions] [netN.NetSpecs GF]
variable [io.Assumptions]

theorem logArg_int (n : w64) : ⊢ (logArg (interface.mkOk go.int #n) : IProp GF) := by
  apply logArg_wf
  intro ii h
  exact fmt.ArgsWf.cons_int _ _ [] (.int n) fmt.ArgsWf.nil ii
    (List.mem_singleton.2 (by rw [← h]))

theorem logArg_uint32 (n : w32) : ⊢ (logArg (interface.mkOk go.uint32 #n) : IProp GF) := by
  apply logArg_wf
  intro ii h
  exact fmt.ArgsWf.cons_int _ _ [] (.uint32 n) fmt.ArgsWf.nil ii
    (List.mem_singleton.2 (by rw [← h]))

/-- `nil` may be logged (`log.Printf`'s `%v` of a `nil` error). -/
theorem logArg_nil : ⊢ (logArg interface.nil : IProp GF) := by
  apply logArg_wf
  intro ii h; cases h

/-- `poll.ErrDeadlineExceeded`'s value, from `internal/poll`'s initialization. -/
theorem ed_of_poll_cc :
    isPkgInit (PROP := IProp GF) pkg_id.internal.poll ⊢
      ∃ ed : GoInterface, globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed := by
  refine (isPkgInit_access (PROP := IProp GF) pkg_id.internal.poll).trans ?_
  show iprop((∃ e : GoInterface, typedPointsto (globalAddr internal.poll.ErrNoDeadline) e DFrac.discard) ∗
    (∃ e : GoInterface, typedPointsto (globalAddr internal.poll.ErrDeadlineExceeded) e DFrac.discard) ∗
    (∃ x : Loc, typedPointsto (globalAddr internal.poll.ErrFileClosing)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard)) ⊢ _
  iintro ⟨-, ⟨%ed, #Hd⟩, -⟩
  iexists ed
  iexact Hd

/-- `io.EOF`'s value, from `io`'s initialization. -/
theorem eof_of_io :
    isPkgInit (PROP := IProp GF) pkg_id.io ⊢
      ∃ eof : GoInterface, globalAddr _root_.Perennial.io.EOF ↦□ eof := by
  iintro #Hio
  ihave #Heof := _root_.Perennial.io.eof_of_init $$ Hio
  iunfold errors.newVar at Heof
  icases Heof with ⟨%x, #Hx, -⟩
  iexists _
  iexact Hx

/-- A failure's `resErr` (an `*OpError`) is `errAny`. -/
theorem resErr_errAny' (k : NetErr) (op : GoString) (src addr : GoInterface)
    (ed : Option GoInterface) (nm : GoString → Prop) (err : GoInterface) :
    Perennial.net.resErr (GF := GF) (some k) op src addr ed nm err ⊢ models_lab.errAny err := by
  unfold Perennial.net.resErr Perennial.net.opErr
  iintro ⟨%e, ⟨%pe, %nw, ⟨%Herr, -⟩, #Hpe⟩, -⟩
  subst Herr
  iapply netN.opErrPtr_errAny $$ Hpe

/-- An accepted connection at replica `k`'s port `a0` (`Accept`'s result, at an address `a` the
wildcard listener takes). -/
def acceptedConn (γ : GryffNames GF) (k : Fin 3) (conn : GoInterface) : IProp GF :=
  iprop(∃ (t : Loc) (c : Nat) (a a0 : GoString) (la ra : GoInterface),
    ⌜conn = interface.mkOk (go.GoType.PointerType Perennial.net.TCPConn.ty) #t ∧ a0 ∈ replicaAddrs⌝ ∗
    Perennial.net.connAt t c true a la ra ∗
    connEnd c true (gryffWireQ γ a0) (gryffWireP γ a0) [] [] ∗
    connFresh c true ∗ □ protoInvs γ)

set_option goose.wp.extras true

theorem clientListener_wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR : Loc)
    (conn : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr ∗ isReplica γ ρ k r ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ acceptedConn γ k conn }}
      (App (Val (gR @!! go.GoType.PointerType src.genericsmr.Replica.ty @!! go!"clientListener"))
        (Val #conn))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hrep, #HgR, Hac⟩
  iunfold acceptedConn at Hac
  icases Hac with ⟨%t, %c, %a, %a0, %la, %ra, %Hconn, #Hcat, Hce, Hfresh, #Hsh⟩
  iunfold connEnd at Hce
  icases Hce with ⟨Hsend, Hrecv⟩
  obtain ⟨rfl, ha0⟩ := Hconn
  ihave #Hbufio : isPkgInit (PROP := IProp GF) pkg_id.bufio $$ []
  · iPkgInit
  ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  ihave #Hlog : isPkgInit (PROP := IProp GF) pkg_id.log $$ []
  · iPkgInit
  ihave #Hbin : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  ihave #Hpoll : isPkgInit (PROP := IProp GF) pkg_id.internal.poll $$ []
  · iPkgInit
  ihave ⟨%eof, #Heof⟩ := eof_of_io $$ Hio
  ihave ⟨%ed, #Hed⟩ := ed_of_poll_cc $$ Hpoll
  ihave #Hrdok := Perennial.net.conn_readerOk (netN.NetSpecs.read (GF := GF)) t c true a la ra eof ed
    (gryffWireP γ a0) $$ [$Hio $Hcat $Heof $Hed]
  ihave #Hwok := Perennial.net.conn_streamWriterOk (netN.NetSpecs.write (GF := GF)) t c true a la ra
    ed (gryffWireQ γ a0) (gryffWireQ_closed γ a0) $$ [$Hcat $Hed]
  ihave Hrecv := recvTok_L c true (gryffWireP γ a0) [] $$ Hrecv
  wp_auto
  rw [show (interface.mkOk (go.GoType.PointerType Perennial.net.TCPConn.ty) #t : GoInterface) =
    GoInterface.ok (Perennial.net.connIface t) from rfl]
  wp_apply (wire.wp_NewReader (connRSt t eof la ra ed) (recvTokL c true (gryffWireP γ a0)) []
    (Perennial.net.connIface_ne_bufioReader t)) $$ [Hrecv] as %br Hown
  · iframe Hrecv; iframe #
  try wp_auto
  have e0 : arrayIndexRef w8 (sint.Z (W64 0)) idBytes_ptr = idBytes_ptr := go.arrayIndexRef_0 _ _
  have e4 : (W64 4 - W64 0 : w64) = W64 4 := rfl
  rw [e0, e4]
  ihave Hb := slice_array idBytes_ptr _ _ (by decide) $$ idBytes
  wp_apply (wire.wp_wire_ReadFull br (connRSt t eof la ra ed) (recvTokL c true (gryffWireP γ a0))
    [] _ _) $$ [Hown Hb] as %n %err ⟨%data, Hown, Hres⟩
  · iframe Hown Hb
    unfold wire.readerOk; iframe #
  icases Hres with (⟨%Hok, Hb⟩ | ⟨%Hne, #Hrerr, %vs', Hb⟩)
  rotate_left
  · -- a read error: logged, the connection dropped
    ihave ⟨#Herr, %Hptr⟩ := netN.rdErr_conn' t eof la ra ed err $$ [$Hrerr $Hio $Hbin $Heof]
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
    wp_auto
    wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_apply log.wp_Printf_logArg _ _ _ _ $$ [Hasl] as -
    · iframe
      iintro !>
      simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl, List.set_cons_succ, List.set_cons_zero]
      iapply BigSepL.bigSepL_cons.2
      isplitr
      · iapply logArg_err $$ Herr
      iapply BigSepL.bigSepL_singleton.2
      iapply logArg_int
    try wp_auto
    iapply HΦ; itrivial
  obtain ⟨rfl, hl4⟩ := Hok
  try simp only [List.length_replicate] at hl4
  by_cases hn4 : n = W64 4
  rotate_left
  · -- a short count (not returned by `ReadFull` without an error, but the code checks it)
    wp_auto
    rw [decide_eq_false hn4]
    wp_auto
    wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_apply log.wp_Printf_logArg _ _ _ _ $$ [Hasl] as -
    · iframe
      iintro !>
      simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl, List.set_cons_succ, List.set_cons_zero]
      iapply BigSepL.bigSepL_cons.2
      isplitr
      · iapply logArg_nil
      iapply BigSepL.bigSepL_singleton.2
      iapply logArg_int
    try wp_auto
    iapply HΦ; itrivial
  subst hn4
  wp_auto
  wp_apply (encoding.binary.wp_LittleEndian_Uint32 _ data (DFrac.own 1) [] hl4) $$ [Hb] as Hb
  · simp only [List.append_nil]; iexact Hb
  have hhs : u32Le (leToU32 data) = data := leToU32_le data hl4
  generalize leToU32 data = hs at hhs
  subst hhs
  try wp_auto
  by_cases hpk : hs &&& W32 2147483648 = W32 0
  rotate_left
  · -- a late peer's connection: closed
    rw [decide_eq_false hpk]
    simp only [Bool.not_false]
    try wp_auto
    wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_apply log.wp_Printf_logArg _ _ _ _ $$ [Hasl] as -
    · iframe
      iintro !>
      iapply BigSepL.bigSepL_singleton.2
      iapply logArg_uint32
    try wp_auto
    ihave #Hcis := sendTok_connIs c true (gryffWireQ γ a0) [] $$ Hsend
    wp_apply (netN.NetSpecs.close (GF := GF) t c true a la ra
      (fun res => iprop(⌜∃ st d st' d', CloseOutcome st d res st' d'⌝))) $$ [] as %e -
    · iframe Hcat
      imod close_au c true $$ Hcis with ⟨%st, %d, He, Hd, Hk⟩
      imodintro
      iexists st, d
      iframe He Hd
      iintro %res %st' %d' %Hc He Hd
      imod Hk $$ %res %st' %d' %Hc He Hd with -
      imodintro
      ipureintro; exact ⟨st, d, st', d', Hc⟩
    try wp_auto
    iapply HΦ; itrivial
  rw [decide_eq_true hpk]
  simp only [Bool.not_true]
  have hhs : hs < peerMark := lt_peerMark_of_and hpk
  wp_auto
  simp only [List.nil_append] at *
  -- the handshake's facts
  iapply fupd_wp
  imod ownReader_protoNow br (connRSt t eof la ra ed) c true (gryffWireP γ a0) _ ⊤ $$ Hown
    with ⟨Hown, #Hp⟩
  ihave #Hca := acc_client_conn γ a0 c hs hhs $$ Hp
  ihave ⟨Hown, #Hlb⟩ := ownReader_sentLb br (connRSt t eof la ra ed) c true (gryffWireP γ a0) _
    $$ Hown
  simp only [Bool.not_true]
  ihave #Hbridge := acc_client_writer γ a0 c hs hhs $$ Hlb
  ihave #Hpeek := acc_client_reader γ a0 c hs hhs br (connRSt t eof la ra ed)
  imodintro
  wp_apply (serveClient_wp γ ρ k r gR _ br hs) $$ [Hown Hsend Hfresh]
  · iframe #
    isplitl [Hown Hsend Hfresh]
    rotate_left
    · ipureintro; exact hhs
    iunfold clientConnIn
    iexists t, c, a, a0, la, ra, ed, eof, recvTokL c true (gryffWireP γ a0)
    iframe Hown Hsend Hfresh
    iframe #
    isplitr
    · ipureintro; exact ⟨rfl, ha0⟩
    unfold wire.readerOk; iframe #
  try wp_auto
  iapply HΦ
  first | itrivial | (ipureintro; trivial) | (iclear Hb; itrivial)

/-- `listenerOwn`'s body (opened without unfolding the `Net/` predicates inside). -/
theorem listenerOwn_open (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (gR : Loc) :
    listenerOwn γ ρ k gR ⊢ ∃ (li : GoInterface) (l : w64) (a0 : GoString) (o : Bool),
      gR.[src.genericsmr.Replica, go!"Listener"] ↦□ li ∗ Perennial.net.isListener li l ∗
      netLisOn (extLocalGS netExt (L := hG.goose_localGS)) l (lisAddrOf a0) ∗
      netLis (extLocalGS netExt (L := hG.goose_localGS)) l (lisAddrOf a0) o ∗
      lisProto (lisAddrOf a0) (gryffWireP γ a0) (gryffWireQ γ a0) ∗
      ⌜a0 ∈ replicaAddrs⌝ ∗ portId γ a0 (rid32 k) ∗ □ protoInvs γ := by
  unfold listenerOwn; exact .rfl

theorem isListener_open (li : GoInterface) (l : w64) :
    Perennial.net.isListener (GF := GF) li l ⊢ ∃ (t : Loc) (x : GoInterface),
      ⌜li = interface.mkOk (go.GoType.PointerType Perennial.net.TCPListener.ty) #t⌝ ∗
      Perennial.net.lisAt t l x := by
  unfold Perennial.net.isListener; exact .rfl

theorem WaitForClientConnections_wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3)
    (r gR : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr ∗ isReplica γ ρ k r ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ listenerOwn γ ρ k gR }}
      (App (Val (gR @!! go.GoType.PointerType src.genericsmr.Replica.ty @!!
        go!"WaitForClientConnections")) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hrep, #HgR, Hlo⟩
  icases listenerOwn_open γ ρ k gR $$ Hlo with ⟨%li, %l, %a0, %o, #Hlf, #Hli, #Hon, Hl, #Hlp, %ha0, -, #Hsh⟩
  ihave Hr := (isReplica_open ..).1 $$ Hrep
  icases Hr with ⟨%gR2, %h, -, #HgR2, -, -, -, -, -, -, -, #Hgen⟩
  icombine HgR HgR2 gives %Heq
  subst Heq
  ihave ⟨%ct, %st, %mu, %cwm, %crm, %CM, -, -, -, -, -, -, -, -, -, -, -, #HSh, -⟩ :=
    genericOk_serve γ ρ k r gR h $$ Hgen
  ihave #HcC : gR.[src.genericsmr.Replica, go!"clientConnect"] ↦□ false $$ [Hgen]
  · iunfold genericOk at Hgen
    icases Hgen with ⟨%rt, %ct, %st, %mu, %cwm, %crm, %M, %CM, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, #H, -⟩
    iexact H
  ihave #Hlog : isPkgInit (PROP := IProp GF) pkg_id.log $$ []
  · iPkgInit
  icases isListener_open li l $$ Hli with ⟨%tl, %x, %Hli, #Hlat⟩
  subst Hli
  -- keep the listener's state folded (`wp_auto` unfolds `netLis`)
  generalize hN : netLis (extLocalGS netExt (L := hG.goose_localGS)) l (lisAddrOf a0) = N
  wp_auto
  wp_for Hl
  try wp_auto
  subst hN
  wp_apply (netN.NetSpecs.accept (GF := GF) tl l x (lisAddrOf a0)
      (fun _ => netLis (extLocalGS netExt (L := hG.goose_localGS)) l (lisAddrOf a0) o)
      (fun a cn => iprop(netLis (extLocalGS netExt (L := hG.goose_localGS)) l (lisAddrOf a0) o ∗
        connEnd cn true (gryffWireQ γ a0) (gryffWireP γ a0) [] [] ∗ connFresh cn true)))
    $$ [Hl] as %cv %err Hres
  · iframe Hlat Hon
    iapply accept_lis_au (lisAddrOf a0) (gryffWireP γ a0) (gryffWireQ γ a0)
      (extLocalGS netExt (L := hG.goose_localGS)) l o $$ Hlp Hl
  icases Hres with (⟨%Herr, %cn, %a, %Ha, #Hic, Hl, Hce, Hfresh⟩ | ⟨%kd, Hl, #Hop⟩)
  all_goals generalize hN : netLis (extLocalGS netExt (L := hG.goose_localGS)) l (lisAddrOf a0) = N
  rotate_left
  · ihave #Herr := resErr_errAny' _ _ _ _ _ _ err $$ Hop
    try wp_auto
    ihave %Hne := models_lab.errAny_ne_nil err $$ Herr
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
    wp_auto
    wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_apply log.wp_Printf_logArg _ _ _ _ $$ [Hasl] as -
    · iframe
      iintro !>
      iapply BigSepL.bigSepL_singleton.2
      iapply logArg_err $$ Herr
    try wp_auto
    wp_for_post
    iframe
  subst Herr
  iunfold Perennial.net.isConn at Hic
  icases Hic with ⟨%tc, %la, %ra, %Hcv, #Hcat⟩
  subst Hcv
  ihave #Hcat' := Hcat
  iunfold Perennial.net.connAt at Hcat'
  icases Hcat' with ⟨%nw, -, -, -, #Hra', -⟩
  iunfold Perennial.net.netAddr at Hra'
  icases Hra' with ⟨%rp, %rv, %Hrp, -⟩
  try wp_auto
  wp_apply (netN.NetSpecs.remoteAddr (GF := GF) tc cn true a la ra) $$ [Hcat]
  · iexact Hcat
  subst Hrp
  wp_auto
  wp_apply (lib.wp_TCPAddr_String rp) as %ras -
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  wp_apply log.wp_Printf_logArg _ _ _ _ $$ [Hasl] as -
  · iframe
    iintro !>
    iapply BigSepL.bigSepL_singleton.2
    iapply logArg_string
  try wp_auto
  wp_apply wp_fork $$ [Hce Hfresh]
  · try wp_auto
    wp_apply (clientListener_wp γ ρ k r gR _) $$ [Hce Hfresh]
    · iframe #
      iunfold acceptedConn
      iexists tc, cn, a, a0, la, _
      isplitr
      · ipureintro; exact ⟨rfl, ha0⟩
      iframe Hcat Hfresh Hsh Hce
    itrivial
  try wp_auto
  wp_for_post
  iframe

end

end Perennial.gryff.replica2
