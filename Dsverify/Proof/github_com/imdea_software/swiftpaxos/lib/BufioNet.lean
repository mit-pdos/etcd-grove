/-
The bridge between the lab's `bufio` vocabulary (`lib/Bufio.lean`) and a connection over `Net/`
(dsverify-lab `harness/lean/Harness/Proof/bufio/Net.lean` and `ReadFull.lean`'s `readsOk_conn`,
re-proved over `Net/Spec/net/Conn__{Read,Write}` and `GooseLang/Ext/Net/Proto.lean`'s laws, as
dsv-bufio's `Net/Proof/net/ConnIo.lean` does for the generic `io` contracts):

* `readerOk_conn`: `readerOk cv (recvTok cid side P)`: a read extends the reader's token by the
  bytes read (`read_au`), whose protocol fact comes a step later (`recvTokL_later`: `readerOk`'s
  `▷ I`); its error is `nil`, `io.EOF`'s value or a read `*OpError` (`errOrNil`).
* `writerOk_conn`: `writerOk cv (sendTok cid side P) (P cid)` for a prefix-closed protocol
  (`write_acc`, `writeP`).
* `readsOk_conn`: `readerOk_conn` without the `*bufio.Reader` condition.

Each takes `isPkgInit net` (the values of `io.EOF` and `poll.ErrDeadlineExceeded`, from the
packages `net` imports) and the connection (`net.rpc.connIface`), as the lab's did.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.Bufio
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.NetRpc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.NetLab
public import Net.Proof.net.ConnIo
public import Net.Proof.net.rpc.Errs
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Pkg
public import Perennial.Proof.io.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.LibDeps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace bufio

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.rpc.Assumptions] [π : NetProtoGS]

theorem tcpConn_ne_reader :
    go.GoType.PointerType net.TCPConn.ty ≠ go.GoType.PointerType bufio.Reader.ty := by
  unfold net.TCPConn.ty bufio.Reader.ty; simp

theorem tcpConn_ne_writer :
    go.GoType.PointerType net.TCPConn.ty ≠ go.GoType.PointerType bufio.Writer.ty := by
  unfold net.TCPConn.ty bufio.Writer.ty; simp

/-- A failure's error (`resErr (some k)`, an `*OpError`) is an error with some message. -/
theorem resErr_errOrNil (k : NetErr) (op : GoString) (src addr : GoInterface)
    (ed : Option GoInterface) (nm : GoString → Prop) (err : GoInterface) :
    syscall.errnoOk (GF := GF) ⊢ net.resErr (some k) op src addr ed nm err -∗ errOrNil err := by
  iintro #Hsys #H
  ihave %Hn := net.resErr_netErr _ _ _ _ _ _ _ $$ H
  ihave #Ha := net.rpc.errAny_resErr _ _ _ _ _ _ _ $$ Hsys H
  unfold errOrNil
  iright
  iframe Ha
  ipureintro
  obtain ⟨pe, rfl⟩ := Hn.2 (by simp)
  intro e h T _; cases h; exact ⟨pe, rfl⟩

/-- `io.EOF`'s value is an error with some message. -/
theorem eof_errOrNil (eof : GoInterface) :
    errors.newVar (GF := GF) io.EOF go!"EOF" ⊢ globalAddr io.EOF ↦□ eof -∗ errOrNil eof := by
  iintro #Hv #He
  ihave #Ha := net.rpc.errAny_newVar _ _ eof $$ Hv He
  unfold errors.newVar
  icases Hv with ⟨%x, #Hx, -⟩
  icombine He Hx gives %Heq
  subst Heq
  unfold errOrNil
  iright
  iframe Ha
  ipureintro
  intro e h T _; cases h; exact ⟨x, rfl⟩

/-- The package facts a connection's `Read` and `Write` name, from `net`'s initialization. -/
theorem net_facts :
    isPkgInit (PROP := IProp GF) pkg_id.net ⊢
      ∃ eof ed : GoInterface, globalAddr io.EOF ↦□ eof ∗ errors.newVar (GF := GF) io.EOF go!"EOF" ∗
        globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed := by
  iintro #Hpkg
  ihave #Hio : (isPkgInit (PROP := IProp GF) pkg_id.io) $$ []
  · iPkgInit
  ihave #Hpoll : (isPkgInit (PROP := IProp GF) pkg_id.internal.poll) $$ []
  · iPkgInit
  ihave #Hv := io.eof_of_init $$ Hio
  ihave #Hed := github_com.mit_pdos.etcd_grove.examples.net.wire.ed_of_poll $$ Hpoll
  icases Hed with ⟨%ed, #Hed⟩
  ihave #Hv' := Hv
  iunfold errors.newVar at Hv'
  icases Hv' with ⟨%x, #Hx, -⟩
  iexists _, ed
  iframe Hx Hv Hed

/-- A connection is an underlying reader of `bufio`, with the end's reader token `recvTokL`
(the protocol fact of what was read a step later): dsv-bufio's `net.conn_readerOk`. -/
theorem readerOk_conn [github_com.imdea_software.swiftpaxos.SwiftNetDeps GF] (cv : GoInterface) (cid : Nat) (side : Bool) (P : Proto GF) :
    (isPkgInit (PROP := IProp GF) pkg_id.net ∗ net.rpc.connIface cv cid side) ⊢
      readerOk cv (recvTokL (Gg := hG.goose_globalGS) cid side P) := by
  iintro ⟨#Hpkg, #Hc⟩
  icases net_facts $$ Hpkg with ⟨%eof, %ed, #Heof, #Hv, #Hed⟩
  ihave #Hio : (isPkgInit (PROP := IProp GF) pkg_id.io) $$ []
  · iPkgInit
  ihave #Hpoll0 : (isPkgInit (PROP := IProp GF) pkg_id.internal.poll) $$ []
  · iPkgInit
  ihave #Hsys := net.errnoOk_of_poll $$ Hpoll0
  icases newVar_err _ _ $$ Hv with ⟨%eof', #Heof', #Ha, %Hw⟩
  icombine Heof Heof' gives %Heq
  subst Heq
  iunfold net.rpc.connIface at Hc
  icases Hc with ⟨%t, %a, %la, %ra, %Hcv, #Hat, -⟩
  subst Hcv
  iunfold readerOk
  iexists net.connIface t, net.connReadE eof la ra ed
  isplitr
  · ipureintro; exact ⟨rfl, tcpConn_ne_reader⟩
  isplitr
  · unfold errsOk net.connReadE
    iintro !> %r %e (%h | ⟨%k, #H⟩)
    · subst h; iframe Ha; ipureintro; exact Hw.1
    · ihave %Hn := net.resErr_netErr _ _ _ _ _ _ _ $$ H
      ihave #Ha' := net.rpc.errAny_resErr _ _ _ _ _ _ _ $$ Hsys H
      iframe Ha'
      ipureintro; exact errWf_of_ptrTyped (net.netErr_ptrTyped (Hn.2 (by simp)))
  iapply net.conn_readerOk (github_com.imdea_software.swiftpaxos.SwiftNetDeps.connRead (GF := GF)) t cid side a la ra eof ed P $$ [$Hio $Hat $Heof $Hed]

/-- The error evidence of a connection as a writer: an error with some message (`errOrNil`'s). -/
def wrErr (err : GoInterface) : IProp GF :=
  iprop(models_lab.errAny err ∗ ⌜errWf err⌝)

theorem errOrNil_werrAt (err : GoInterface) :
    errOrNil (GF := GF) err ⊢ EtcdGrove.io.werrAt wrErr err := by
  unfold errOrNil EtcdGrove.io.werrAt wrErr
  iintro (%h | ⟨#Ha, %Hw⟩)
  · ileft; ipureintro; exact h
  · iright; imodintro; iframe Ha; ipureintro; exact Hw

/-- A connection is an underlying writer of `bufio`, with the end's writer token, for a
prefix-closed protocol. -/
theorem writerOk_conn [github_com.imdea_software.swiftpaxos.SwiftNetDeps GF] (cv : GoInterface) (cid : Nat) (side : Bool) (P : Proto GF) :
    (isPkgInit (PROP := IProp GF) pkg_id.net ∗ net.rpc.connIface cv cid side ∗
      prefixClosed (P cid)) ⊢
      writerOk cv (sendTok (Gg := hG.goose_globalGS) cid side P) (P cid) := by
  iintro ⟨#Hpkg, #Hc, #Hpc⟩
  icases net_facts $$ Hpkg with ⟨%eof, %ed, -, -, #Hed⟩
  iunfold net.rpc.connIface at Hc
  icases Hc with ⟨%t, %a, %la, %ra, %Hcv, #Hat, -⟩
  subst Hcv
  iunfold writerOk
  iexists ⟨go.GoType.PointerType net.TCPConn.ty, #t⟩, wrErr
  isplitr
  · ipureintro; exact ⟨rfl, tcpConn_ne_writer⟩
  iframe Hpc
  unfold EtcdGrove.io.streamWriterOk
  isplitr
  · iapply prefixClosed_io $$ Hpc
  imodintro
  iintro %W %b %dq %bs !> %Φ ⟨HJ, #HQ, Hb⟩ HΦ
  dsimp only
  ihave HJ0 := writeP_init cid side P W $$ HJ
  ihave #Hacc := write_acc cid side P W bs $$ HQ
  iapply (github_com.imdea_software.swiftpaxos.SwiftNetDeps.connWrite (GF := GF)) t cid side a la ra b bs dq ed (writeP cid side P W)
    $$ [HJ0 Hb]
  · iframe Hat Hb Hed HJ0 Hacc
  iintro !> %n %err ⟨%w, %res, HJ, Hb, %Hw, #HE⟩
  obtain ⟨hpre, rfl, hnone, -⟩ := Hw
  unfold writeP
  ihave %Hres := net.resErr_netErr _ _ _ _ _ _ _ $$ HE
  have hk2 : w.length ≤ bs.length ∧ (err = interface.nil → w.length = bs.length) := by
    refine ⟨hpre.length_le, fun herr => ?_⟩
    cases res with
    | none => rw [hnone rfl]
    | some k => exact absurd herr (net.netErr_ne_nil (Hres.2 (by simp)))
  have htake : bs.take w.length = w := by
    obtain ⟨rs, rfl⟩ := hpre; simp
  ihave #Hsys := net.connAt_errnoOk _ _ _ _ _ _ $$ Hat
  ihave He : errOrNil err $$ []
  · cases res with
    | none => unfold errOrNil; ileft; ipureintro; exact Hres.1 rfl
    | some k => iapply resErr_errOrNil $$ Hsys HE
  iapply HΦ
  iexists w.length
  isplitr
  · ipureintro
    exact ⟨by simp, hk2.1, hk2.2⟩
  rw [htake]
  iframe Hb HJ
  iapply errOrNil_werrAt $$ He

/-- The lab's `net.TCPConn.Write.spec` (`Harness/Spec/net/TCPConn__Write.lean`; its error code
dropped: no caller here uses it), from `Net/`'s `Conn.Write` and `write_acc`. -/
theorem _root_.Perennial.net.TCPConn.Write.labProof [github_com.imdea_software.swiftpaxos.SwiftNetDeps GF] (c : Loc) (cid : Nat) (side : Bool)
    (b : GoSlice) (bs : List w8) (dq : DFrac) (P : Proto GF) (W : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ net.ownTCPConn (GF := GF) c cid side ∗
        sendTok (Gg := hG.goose_globalGS) cid side P W ∗ □ P cid (W ++ bs) ∗ b ↦*{dq} bs }}
      (App (Val (c @!! go.GoType.PointerType net.TCPConn.ty @!! go!"Write")) (Val #b))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ k : Nat, ⌜n = W64 k ∧ k ≤ bs.length ∧ (err = interface.nil → k = bs.length)⌝ ∗
        b ↦*{dq} bs ∗ sendTok (Gg := hG.goose_globalGS) cid side P (W ++ bs.take k) }} := by
  iintro %Φ ⟨#Hpkg, #Hc, HJ, #HQ, Hb⟩ HΦ
  icases net_facts $$ Hpkg with ⟨%eof, %ed, -, -, #Hed⟩
  iunfold net.ownTCPConn at Hc
  icases Hc with ⟨%a, %la, %ra, #Hat, -⟩
  ihave HJ0 := writeP_init cid side P W $$ HJ
  ihave #Hacc := write_acc cid side P W bs $$ HQ
  iapply (github_com.imdea_software.swiftpaxos.SwiftNetDeps.connWrite (GF := GF)) c cid side a la ra b bs dq ed (writeP cid side P W)
    $$ [HJ0 Hb]
  · iframe Hat Hb Hed HJ0 Hacc
  iintro !> %n %err ⟨%w, %res, HJ, Hb, %Hw, #HE⟩
  obtain ⟨hpre, rfl, hnone, -⟩ := Hw
  unfold writeP
  ihave %Hres := net.resErr_netErr _ _ _ _ _ _ _ $$ HE
  have hk2 : w.length ≤ bs.length ∧ (err = interface.nil → w.length = bs.length) := by
    refine ⟨hpre.length_le, fun herr => ?_⟩
    cases res with
    | none => rw [hnone rfl]
    | some k => exact absurd herr (net.netErr_ne_nil (Hres.2 (by simp)))
  have htake : bs.take w.length = w := by
    obtain ⟨rs, rfl⟩ := hpre; simp
  iapply HΦ
  iexists w.length
  isplitr
  · ipureintro
    exact ⟨by simp, hk2.1, hk2.2⟩
  rw [htake]
  iframe Hb HJ

end proofs

end bufio

end Perennial
