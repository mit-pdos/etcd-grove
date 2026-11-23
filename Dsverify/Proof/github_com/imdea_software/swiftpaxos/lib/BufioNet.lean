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
public import Net.Proof.net.Conn__Read
public import Net.Proof.net.Conn__Write
public import Net.Proof.net.rpc.Errs
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Pkg
public import Perennial.Proof.io.Base

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
variable [net.Assumptions] [net.FieldAssumptions] [net.rpc.Assumptions] [π : NetProtoGS]

theorem tcpConn_ne_reader :
    go.GoType.PointerType net.TCPConn.ty ≠ go.GoType.PointerType bufio.Reader.ty := by
  unfold net.TCPConn.ty bufio.Reader.ty; simp

theorem tcpConn_ne_writer :
    go.GoType.PointerType net.TCPConn.ty ≠ go.GoType.PointerType bufio.Writer.ty := by
  unfold net.TCPConn.ty bufio.Writer.ty; simp

/-- A failure's error (`resErr (some k)`, an `*OpError`) is an error with some message. -/
theorem resErr_errOrNil (k : NetErr) (op : GoString) (src addr : GoInterface)
    (ed : Option GoInterface) (nm : GoString → Prop) (err : GoInterface) :
    net.resErr (GF := GF) (some k) op src addr ed nm err ⊢ errOrNil err := by
  iintro #H
  ihave %Hn := net.resErr_netErr _ _ _ _ _ _ _ $$ H
  ihave #Ha := net.rpc.errAny_resErr _ _ _ _ _ _ _ $$ H
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

/-- A connection is an underlying reader of `bufio`, with the end's reader token. -/
theorem readerOk_conn (cv : GoInterface) (cid : Nat) (side : Bool) (P : Proto GF) :
    (isPkgInit (PROP := IProp GF) pkg_id.net ∗ net.rpc.connIface cv cid side) ⊢
      readerOk cv (recvTok (Gg := hG.goose_globalGS) cid side P) := by
  iintro ⟨#Hpkg, #Hc⟩
  icases net_facts $$ Hpkg with ⟨%eof, %ed, #Heof, #Hv, #Hed⟩
  iunfold net.rpc.connIface at Hc
  icases Hc with ⟨%t, %a, %la, %ra, %Hcv, #Hat, -⟩
  subst Hcv
  iunfold readerOk
  iexists ⟨go.GoType.PointerType net.TCPConn.ty, #t⟩
  isplitr
  · ipureintro; exact ⟨rfl, tcpConn_ne_reader⟩
  imodintro
  iintro %b %bs %R %Φ %Hpos HI Hb HΦ
  dsimp only
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  have hpl : b.len.toNat = bs.length := by rw [Hlen.1]; word
  ihave HL := recvTok_L cid side P R $$ HI
  iapply net.Conn.Read.wp_proof t cid side a la ra b bs eof ed
    (fun r => iprop(recvTokL (Gg := hG.goose_globalGS) cid side P (R ++ r.got) ∗
      ⌜r.got.length ≤ b.len.toNat ∧ (r = .bytes [] → b.len.toNat = 0)⌝)) $$ [HL Hb]
  · iframe Hat Hb Heof Hed
    imod read_au cid side P R b.len.toNat $$ HL with ⟨%st, %d, HE, HD, Hcl⟩
    imodintro
    iexists st, d
    iframe HE HD
    iintro %r %d' %Hrd HE HD
    imod Hcl $$ %r %d' %Hrd HE HD with ⟨HP, -⟩
    imodintro
    iframe HP
    ipureintro
    exact readOutcome_got_le Hrd
  iintro !> %k %err ⟨%r, %bs', ⟨HP, %Hrl⟩, Hb, %Hout, HE⟩
  rw [hpl] at Hrl
  obtain ⟨Hrl, Hz⟩ := Hrl
  ihave HP := recvTokL_later cid side P _ $$ HP
  cases r with
  | bytes data =>
    obtain ⟨hk, rfl⟩ := Hout
    simp only [ReadRes.got] at Hrl
    isimp only [ReadRes.got] at HP
    simp only [net.ReadErr]
    icases HE with %Herr
    subst Herr
    have hd1 : 1 ≤ data.length := by
      rcases data with _ | ⟨x, data⟩
      · have := Hz rfl; omega
      · simp
    have hkd : k = W64 data.length := by
      rw [Nat.min_eq_right Hrl] at hk
      have : sint.nat k = (sint.Z k).toNat := rfl
      have h63 : data.length < 2 ^ 63 := by
        have h2 := BitVec.toInt_lt (x := b.len)
        have h3 := Hlen.1
        have h4 : sint.nat b.len = b.len.toInt.toNat := rfl
        have : bs.length < 2 ^ 63 := by simp at h2; rw [h3, h4]; omega
        omega
      have hz : sint.Z k = data.length := by omega
      apply BitVec.eq_of_toInt_eq
      rw [show (W64 data.length).toInt = sint.Z (W64 data.length) from rfl,
        net.rpc.sint_Z_W64_length h63]
      exact hz
    subst hkd
    rw [List.take_of_length_le Hrl]
    iapply HΦ $$ %data %_ %Hrl Hb HP
    unfold errOrNil; ileft; ipureintro; rfl
  | eof =>
    obtain ⟨rfl, hbs⟩ := Hout
    subst hbs
    isimp only [ReadRes.got, List.append_nil] at HP
    simp only [net.ReadErr]
    icases HE with %Herr
    ihave He := eof_errOrNil eof $$ Hv Heof
    rw [← Herr] at *
    ihave HΦ' := HΦ $$ %([] : List w8) %err %(Nat.zero_le _)
    rw [show (0 : w64) = W64 (([] : List w8).length : Int) from rfl]
    ihave Hb : (b ↦* (([] : List w8) ++ List.drop ([] : List w8).length bs') : IProp GF) $$ [Hb]
    · simp only [List.length_nil, List.drop_zero, List.nil_append]; iexact Hb
    ihave HP : (▷ recvTok (Gg := hG.goose_globalGS) cid side P (R ++ [])) $$ [HP]
    · simp only [List.append_nil]; iexact HP
    iapply HΦ' $$ Hb HP He
  | err e =>
    obtain ⟨rfl, hbs⟩ := Hout
    subst hbs
    isimp only [ReadRes.got, List.append_nil] at HP
    simp only [net.ReadErr]
    ihave He := resErr_errOrNil _ _ _ _ _ _ _ $$ HE
    ihave HΦ' := HΦ $$ %([] : List w8) %err %(Nat.zero_le _)
    rw [show (0 : w64) = W64 (([] : List w8).length : Int) from rfl]
    ihave Hb : (b ↦* (([] : List w8) ++ List.drop ([] : List w8).length bs') : IProp GF) $$ [Hb]
    · simp only [List.length_nil, List.drop_zero, List.nil_append]; iexact Hb
    ihave HP : (▷ recvTok (Gg := hG.goose_globalGS) cid side P (R ++ [])) $$ [HP]
    · simp only [List.append_nil]; iexact HP
    iapply HΦ' $$ Hb HP He

/-- A connection is an underlying writer of `bufio`, with the end's writer token, for a
prefix-closed protocol. -/
theorem writerOk_conn (cv : GoInterface) (cid : Nat) (side : Bool) (P : Proto GF) :
    (isPkgInit (PROP := IProp GF) pkg_id.net ∗ net.rpc.connIface cv cid side ∗
      prefixClosed (P cid)) ⊢
      writerOk cv (sendTok (Gg := hG.goose_globalGS) cid side P) (P cid) := by
  iintro ⟨#Hpkg, #Hc, #Hpc⟩
  icases net_facts $$ Hpkg with ⟨%eof, %ed, -, -, #Hed⟩
  iunfold net.rpc.connIface at Hc
  icases Hc with ⟨%t, %a, %la, %ra, %Hcv, #Hat, -⟩
  subst Hcv
  iunfold writerOk
  iexists ⟨go.GoType.PointerType net.TCPConn.ty, #t⟩
  isplitr
  · ipureintro; exact ⟨rfl, tcpConn_ne_writer⟩
  iframe Hpc
  imodintro
  iintro %b %dq %bs %W %Φ HJ #HQ Hb HΦ
  dsimp only
  ihave HJ0 := writeP_init cid side P W $$ HJ
  ihave #Hacc := write_acc cid side P W bs $$ HQ
  iapply net.Conn.Write.wp_proof t cid side a la ra b bs dq ed (writeP cid side P W)
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
  ihave He : errOrNil err $$ []
  · cases res with
    | none => unfold errOrNil; ileft; ipureintro; exact Hres.1 rfl
    | some k => iapply resErr_errOrNil $$ HE
  rw [show BitVec.ofNat 64 w.length = W64 (w.length : Int) from by simp]
  ihave HΦ' := HΦ $$ %w.length %err %hk2
  rw [htake]
  iapply HΦ' $$ Hb HJ He

/-- A connection's `Read` spec over the end's reader token (`readerOk_conn`). -/
theorem readsOk_conn (cv : GoInterface) (cid : Nat) (side : Bool) (P : Proto GF) :
    (isPkgInit (PROP := IProp GF) pkg_id.net ∗ net.rpc.connIface cv cid side) ⊢
      readsOk cv (recvTok (Gg := hG.goose_globalGS) cid side P) := by
  iintro H
  iapply readerOk_readsOk
  iapply readerOk_conn $$ H

end proofs

end bufio

end Perennial
