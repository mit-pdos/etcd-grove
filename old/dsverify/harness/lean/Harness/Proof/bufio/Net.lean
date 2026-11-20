/-
`bufio` over a connection: a `net.Conn` holding the `*TCPConn` of end `side` of `cid`
(`net.rpc.connIface`) meets the underlying reader's and writer's specs of `Defs.lean`, with the
end's tokens (`TCPConn__Read`, `TCPConn__Write`):
* `readerOk_conn`: `readerOk cv (recvTok cid side P)`; so `NewReader(conn)` from
  `recvTok cid side P R` gives `ownReader br cv (recvTok cid side P) R`, and the bytes a
  `ReadByte` / `Read` returns are the next ones of the stream, the reader holding the end's
  token for what the stream delivered (`R ++ pend`).
* `writerOk_conn`: `writerOk cv (sendTok cid side P) (P cid)` when the protocol `P cid` is
  prefix-closed (`prefixClosed`); so `NewWriter(conn)` from `sendTok cid side P W` and
  `□ P cid W` gives `ownWriter bw cv (sendTok cid side P) (P cid) W [] nil`.
-/
module

public import Harness.Proof.bufio.Writer
public import Harness.Proof.net.TCPConn__Read
public import Harness.Proof.net.TCPConn__Write
public import Harness.Proof.net.rpc.WireSpec

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn

namespace bufio

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions]

theorem tcpConn_ne_reader :
    go.GoType.PointerType net.TCPConn.ty ≠ go.GoType.PointerType bufio.Reader.ty := by
  unfold net.TCPConn.ty bufio.Reader.ty; simp

theorem tcpConn_ne_writer :
    go.GoType.PointerType net.TCPConn.ty ≠ go.GoType.PointerType bufio.Writer.ty := by
  unfold net.TCPConn.ty bufio.Writer.ty; simp

/-- The error of a connection operation is well formed (`errWf`): `nil`, the value of
`io.EOF` (an `*errorString`), or an `*OpError`. -/
theorem connErr_errWf (op : GoString) (code : w64) (err : GoInterface) :
    (isPkgInit (PROP := IProp GF) pkg_id.net ∗ net.connErr op code err) ⊢ ⌜errWf err⌝ := by
  unfold net.connErr
  iintro ⟨#Hpkg, Herr⟩
  by_cases h0 : code = NetConn.errNone
  · simp only [h0, ite_true]
    icases Herr with %Hn
    ipureintro; subst Hn; intro e h; cases h
  simp only [h0, ite_false]
  by_cases h1 : code = NetConn.errEOF
  · simp only [h1, ite_true]
    icases Herr with ⟨-, #He⟩
    ihave #Hio := net.io_init_of_net $$ Hpkg
    ihave #Hv := io.eof_of_init $$ Hio
    iunfold errors.newVar at Hv
    icases Hv with ⟨%x, #Hx, -⟩
    icombine He Hx gives %Heq
    ipureintro; subst Heq
    intro e h T _; cases h; exact ⟨x, rfl⟩
  · simp only [h1, ite_false]
    unfold net.opErr
    icases Herr with ⟨%l, %inner, %h, -⟩
    ipureintro; subst h
    intro e h T _; cases h; exact ⟨l, rfl⟩

/-- The error of a connection operation: `nil` or with some message. -/
theorem connErr_errOrNil (op : GoString) (code : w64) (err : GoInterface) :
    (isPkgInit (PROP := IProp GF) pkg_id.net ∗ net.connErr op code err) ⊢ errOrNil err := by
  iintro ⟨#Hpkg, #Herr⟩
  ihave %Hwf := connErr_errWf op code err $$ [$Hpkg $Herr]
  unfold errOrNil
  icases net.rpc.connErr_errAny op code err $$ [$Hpkg $Herr] with (%Hn | ⟨#Ha, -⟩)
  · ileft; ipureintro; exact Hn
  · iright; iframe Ha; ipureintro; exact Hwf

/-- A connection is an underlying reader of `bufio`, with the end's reader token. -/
theorem readerOk_conn (cv : GoInterface) (cid : w64) (side : Bool) (P : Proto GF) :
    (isPkgInit (PROP := IProp GF) pkg_id.net ∗ net.rpc.connIface cv cid side) ⊢
      readerOk cv (recvTok cid side P) := by
  iintro ⟨#Hpkg, #Hc⟩
  iunfold net.rpc.connIface at Hc
  icases Hc with ⟨%c, %Hcv, #Hown⟩
  subst Hcv
  iunfold readerOk
  iexists interface.mk (go.GoType.PointerType net.TCPConn.ty) #c
  isplitr
  · ipureintro; exact ⟨rfl, tcpConn_ne_reader⟩
  imodintro
  iintro %b %bs %R %Φ HI Hb HΦ
  wp_apply net.TCPConn.Read.wp_proof c cid side b bs P R $$ [$Hpkg $Hown $HI $Hb]
    as %n %err ⟨%data, %code, %Hd, Hb, HI, Herr⟩
  obtain ⟨rfl, hdl, -, -, -⟩ := Hd
  ihave #He := connErr_errOrNil _ _ _ $$ [$Hpkg $Herr]
  iapply HΦ $$ %data %err %hdl Hb HI He

/-- A connection is an underlying writer of `bufio`, with the end's writer token, for a
prefix-closed protocol. -/
theorem writerOk_conn (cv : GoInterface) (cid : w64) (side : Bool) (P : Proto GF) :
    (isPkgInit (PROP := IProp GF) pkg_id.net ∗ net.rpc.connIface cv cid side ∗
      prefixClosed (P cid)) ⊢
      writerOk cv (sendTok cid side P) (P cid) := by
  iintro ⟨#Hpkg, #Hc, #Hpc⟩
  iunfold net.rpc.connIface at Hc
  icases Hc with ⟨%c, %Hcv, #Hown⟩
  subst Hcv
  iunfold writerOk
  iexists interface.mk (go.GoType.PointerType net.TCPConn.ty) #c
  isplitr
  · ipureintro; exact ⟨rfl, tcpConn_ne_writer⟩
  iframe Hpc
  imodintro
  iintro %b %dq %bs %W %Φ HJ #HQ Hb HΦ
  wp_apply net.TCPConn.Write.wp_proof c cid side b bs dq P W $$ [$Hpkg $Hown $HJ $HQ $Hb]
    as %n %err ⟨%k, %code, %Hk, Hb, HJ, Herr⟩
  obtain ⟨rfl, hkl, -, hnil⟩ := Hk
  ihave #He := connErr_errOrNil _ _ _ $$ [$Hpkg $Herr]
  have hk2 : k ≤ bs.length ∧ (err = interface.nil → k = bs.length) := ⟨hkl, hnil⟩
  iapply HΦ $$ %k %err %hk2 Hb HJ He

end proofs

end bufio

end Perennial
