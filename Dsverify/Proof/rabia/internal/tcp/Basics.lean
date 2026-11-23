/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/tcp/Base.lean`, run
`rabia-r1wake-1`, onto `Net/`'s connections and the revised bufio.)

Shared lemmas of `rabia/internal/tcp`'s proofs: a connection end's buffered reader and writer
(`rdOwn`, `wrOwn`: the revised bufio's `ownBufReader`/`ownBufWriter` over the connection's
contracts `net.conn_readerOk`/`net.conn_writerOk`, the lab's `ownReader`/`ownWriter` over
`readerOk_conn`/`writerOk_conn`), `GetReaderWriter` (the socket options through
`sockopt_au`; `bufio.NewReaderSize`/`NewWriterSize`), and message's framing specs over them
(`wp_cmdReadUnmarshal`, `wp_msgReadUnmarshal`, `wp_cmdMarshalWriteFlush`,
`wp_msgMarshalWriteFlush`, `wp_writeFlush`). A writer is made over a connection before anything
is known of what it will write: `NewWriterSize` asks `□ Q W` of what was written, which the
protocols allow of the empty stream (`Core/Proto.lean`).
-/
module

public import Dsverify.Proof.rabia.internal.tcp.Spec
public import Dsverify.Proof.rabia.internal.tcp.Wg
public import Dsverify.Proof.rabia.internal.tcp.Enc
public import Dsverify.Proof.rabia.internal.message.ReadUnmarshal
public import Dsverify.Proof.rabia.internal.message.MarshalWriteFlush
public import Dsverify.Proof.rabia.internal.message.WriteFlush
public import Net.Proof.net.ConnIo
public import Net.Proof.net.Conn__Read
public import Net.Proof.net.Conn__Write
public import Net.Proof.net.TCPConn__SetWriteBuffer
public import Net.Proof.net.TCPConn__SetReadBuffer
public import Net.Proof.net.TCPConn__SetKeepAlive
public import Net.Proof.net.TCPConn__SetKeepAlivePeriod
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Pkg
public import Proof.bufio.NewReaderSize
public import Proof.bufio.NewWriterSize
public import Perennial.Proof.time

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.rabia.internal.tcp

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode model Net rabia
  rabia.internal.message rabia.internal.config

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]

/-- The `*bufio.Reader` `br` over the end `s` of the connection `cn` (protocol `P` towards `s`)
has returned `R` (the lab's `ownReader br cv (recvTok cid side P) R`). -/
def rdOwn (br : Loc) (cn : Nat) (s : Bool) (P : Proto GF) (R : List w8) : IProp GF :=
  iprop(∃ (ri : GoInterfaceOk) (E : List w8 → GoInterface → IProp GF),
    EtcdGrove.bufio.ownBufReader br ri connPre (recvTokL (Gg := hG.goose_globalGS) cn s P) E R)

/-- The `*bufio.Writer` `bw` over the end `s` of `cn` (protocol `P` from `s`) has sent `W` and
buffers `pend`, its sticky error `err` (the lab's `ownWriter br cv (sendTok cid side P) (P cid) …`
with its `writerOk`). -/
def wrOwn (bw : Loc) (cn : Nat) (s : Bool) (P : Proto GF) (W pend : List w8) (err : GoInterface) :
    IProp GF :=
  iprop(∃ (wi : GoInterfaceOk) (Ew : GoInterface → IProp GF) (sz : Nat),
    EtcdGrove.io.writerOk wi (sendTok (Gg := hG.goose_globalGS) cn s P) (P cn) Ew ∗
    EtcdGrove.bufio.ownBufWriter bw wi (sendTok (Gg := hG.goose_globalGS) cn s P) (P cn) Ew sz W
      pend err)

end defs

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [_root_.Perennial.bufio.Assumptions] [net.Assumptions] [net.FieldAssumptions]

/-- What a connection's reader has returned meets the protocol up to extension, one step later
(`net.connReader_proto`). -/
theorem rdOwn_proto (br : Loc) (cn : Nat) (s : Bool) (P : Proto GF) (R : List w8) :
    rdOwn br cn s P R ⊢ rdOwn br cn s P R ∗ ▷ protoPrefix P cn R := by
  unfold rdOwn
  iintro ⟨%ri, %E, H⟩
  ihave ⟨H, Hp⟩ := net.connReader_proto br ri connPre cn s P E R $$ H
  iframe Hp
  iexists ri, E
  iexact H

/-- What a connection's writer has sent was written (`sendTok_sentLb`). -/
theorem wrOwn_sentLb (bw : Loc) (cn : Nat) (s : Bool) (P : Proto GF) (W pend : List w8)
    (err : GoInterface) :
    wrOwn bw cn s P W pend err ⊢ wrOwn bw cn s P W pend err ∗
      sentLb (Gg := hG.goose_globalGS) cn s W := by
  unfold wrOwn
  iintro ⟨%wi, %Ew, %sz, #Hwi, H⟩
  ihave ⟨H, #Hlb⟩ := EtcdGrove.bufio.ownBufWriter_fact bw wi _ _ Ew sz W pend err
    (fun w => sentLb (Gg := hG.goose_globalGS) cn s w) (fun w => sendTok_sentLb cn s P w) $$ H
  iframe Hlb
  iexists wi, Ew, sz
  iframe Hwi H

end laws

section pkg
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [_root_.Perennial.io.Assumptions]

/-- `io.EOF`'s value, from tcp's initialization. -/
theorem eof_init :
    isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.tcp ⊢
      ∃ eof : GoInterface, globalAddr _root_.Perennial.io.EOF ↦□ eof := by
  iintro #Hpkg
  ihave #Hio : (isPkgInit (PROP := IProp GF) pkg_id.io) $$ []
  · iPkgInit
  ihave #Hn := _root_.Perennial.io.eof_of_init $$ Hio
  isimp only [_root_.Perennial.errors.newVar] at Hn
  icases Hn with ⟨%eofl, #Heof, -⟩
  iexists _
  iexact Heof

/-- `poll.ErrDeadlineExceeded`'s value, from tcp's initialization. -/
theorem ed_init :
    isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.tcp ⊢
      ∃ ed : GoInterface, globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed := by
  iintro #Hpkg
  ihave #Hpoll : (isPkgInit (PROP := IProp GF) pkg_id.internal.poll) $$ []
  · iPkgInit
  iapply github_com.mit_pdos.etcd_grove.examples.net.wire.ed_of_poll $$ Hpoll

end pkg

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.internal.tcp.Assumptions]
variable [_root_.Perennial.bufio.Assumptions] [_root_.Perennial.io.Assumptions]
variable [net.Assumptions] [net.FieldAssumptions] [go.BasicIntoValInj]
variable [msg_sem : rabia.internal.message.Assumptions]

set_option goose.wp.extras true

/-- A socket option's update: nothing to record. -/
theorem sockopt_true (cn : Nat) (s : Bool) (v : Option Bool) :
    connIs (Gg := hG.goose_globalGS) cn ⊢
      |={⊤,∅}=> ∃ st, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗
        ∀ res, ⌜SockOptOutcome st v res⌝ -∗
          netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ={∅,⊤}=∗
            (fun _ : Option NetErr => iprop(True)) res := by
  iintro #Hc
  imod sockopt_au cn s v $$ Hc with ⟨%st, Hst, Hcl⟩
  imodintro
  iexists st
  iframe Hst
  iintro %res %Ho Hst
  imod Hcl $$ %res %Ho Hst with -
  imodintro
  itrivial

theorem wp_GetReaderWriter (cf : RCfg) (cl : Loc) (cv : GoInterface) (cn : Nat) (s : Bool)
    (a : GoString) (Pin Pout : Proto GF) (R W : List w8) (hP : ProtoPrefixClosed Pout) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.tcp ∗ confRO cf ∗ cl ↦□ cv ∗
        net.isConn cv cn s a ∗ recvTok (Gg := hG.goose_globalGS) cn s Pin R ∗
        sendTok (Gg := hG.goose_globalGS) cn s Pout W ∗ □ Pout cn W }}
      (App (Val (@! GetReaderWriter)) (Val #cl))
    {{ (br bw : Loc), RET (PairV #br #bw); rdOwn br cn s Pin R ∗
        wrOwn bw cn s Pout W [] interface.nil }} := by
  wp_start as ⟨#Hconf, #Hcl, #Hc, HR, HS, #HW⟩
  ihave ⟨%ps, #Hcv⟩ := confRO_val cf $$ Hconf
  ihave Hc2 := Hcv
  iStructNamed Hc2
  unfold net.isConn
  icases Hc with ⟨%t, %la, %ra, %Hct, #Hca⟩
  subst Hct
  ihave #Hconn := sendTok_connIs cn s Pout W $$ HS
  ihave ⟨%eof, #Heof⟩ := eof_init $$ Hpkg
  ihave ⟨%ed, #Hed⟩ := ed_init $$ Hpkg
  ihave #Hio : (isPkgInit (PROP := IProp GF) pkg_id.io) $$ []
  · iPkgInit
  ihave #Hbuf : (isPkgInit (PROP := IProp GF) pkg_id.bufio) $$ []
  · iPkgInit
  wp_auto
  wp_apply net.TCPConn.SetWriteBuffer.wp_proof t cn s a la ra _ (fun _ => iprop(True)) $$ [] as %_ -
  · iframe Hca; iapply sockopt_true $$ Hconn
  wp_apply net.TCPConn.SetReadBuffer.wp_proof t cn s a la ra _ (fun _ => iprop(True)) $$ [] as %_ -
  · iframe Hca; iapply sockopt_true $$ Hconn
  wp_apply net.TCPConn.SetKeepAlive.wp_proof t cn s a la ra _ (fun _ => iprop(True)) $$ [] as %_ -
  · iframe Hca; iapply sockopt_true $$ Hconn
  wp_apply net.TCPConn.SetKeepAlivePeriod.wp_proof t cn s a la ra _ (fun _ => iprop(True)) $$ []
    as %_ -
  · iframe Hca; iapply sockopt_true $$ Hconn
  ihave #Hrok := net.conn_readerOk net.Conn.Read.wp_proof t cn s a la ra eof ed Pin $$ [$Hio $Hca $Heof $Hed]
  ihave #Hwok := net.conn_writerOk net.Conn.Write.wp_proof t cn s a la ra ed Pout hP $$ [$Hca $Hed]
  ihave HRL := recvTok_L cn s Pin R $$ HR
  ihave #Hpu := EtcdGrove.bufio.preUpTo_trivial (recvTokL (Gg := hG.goose_globalGS) cn s Pin)
    (max (sint.Z (W64 16384000)) 16).toNat
  rw [show interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t = GoInterface.ok (net.connIface t)
    from rfl]
  wp_apply EtcdGrove.bufio.NewReaderSize.wp_proof (net.connIface t) connPre _ _ R _
    $$ [$Hbuf $Hrok $Hpu $HRL] as %br Hbr
  · ipureintro; exact net.connIface_ne_bufioReader t
  wp_apply EtcdGrove.bufio.NewWriterSize.wp_proof (net.connIface t) _ _ _ W _
    $$ [$Hbuf $Hwok $HS $HW] as %bw Hbw
  · ipureintro; exact net.connIface_ne_bufioWriter t
  iapply HΦ
  unfold rdOwn wrOwn
  isplitl [Hbr]
  · iexists _, _; iexact Hbr
  iexists _, _, _
  iframe Hwok Hbw

/-! ### Message's framing over a connection end's reader and writer -/

/-- `(*Command).ReadUnmarshal` over `rdOwn`. -/
theorem wp_cmdReadUnmarshal (l br : Loc) (cn : Nat) (s : Bool) (P : Proto GF) (R : List w8)
    (sl : GoSlice) (ds : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗ l ↦ (zeroValDef : Command) ∗
        rdOwn br cn s P R ∗ frameIs P cn R (fun bs => ∃ c, bs = encCmd c) ∗ sl ↦* ds }}
      (App (App (Val (l @!! go.GoType.PointerType Command.ty @!! go!"ReadUnmarshal")) (Val #br))
        (Val #sl))
    {{ (e : GoInterface), RET #e; ∃ (ds' : List w8), sl ↦* ds' ∗
        ((⌜e = interface.nil⌝ ∗ ∃ (v : Command) (c : CmdV), ⌜(encCmd c).length ≤ ds.length⌝ ∗
            l ↦ v ∗ cmdRep v c ∗ rdOwn br cn s P (R ++ frame (encCmd c))) ∨
         (⌜e ≠ interface.nil⌝ ∗ ∃ (R' : List w8) (v : Command), ⌜R <+: R'⌝ ∗ l ↦ v ∗
            rdOwn br cn s P R')) }} := by
  iintro %Φ ⟨#Hpkg, Hl, Hrd, #HF, Hsl⟩ HΦ
  unfold rdOwn
  icases Hrd with ⟨%ri, %E, Hrd⟩
  iapply Command.ReadUnmarshal.wp_proof l br ri cn s P E R sl ds $$ [$Hpkg $Hl $Hrd $HF $Hsl]
  inext
  iintro %e ⟨%ds', Hsl, Hres⟩
  iapply HΦ
  iexists ds'
  iframe Hsl
  icases Hres with (⟨%He, %v, %c, %Hc, Hl, #Hrep, Hrd⟩ | ⟨%He, %R', %v, %HR, Hl, Hrd⟩)
  · ileft
    isplitr
    · ipureintro; exact He
    iexists v, c
    iframe Hl Hrep
    isplitr
    · ipureintro; exact Hc
    iexists ri, E; iexact Hrd
  · iright
    isplitr
    · ipureintro; exact He
    iexists R', v
    iframe Hl
    isplitr
    · ipureintro; exact HR
    iexists ri, E; iexact Hrd

/-- `(*Msg).ReadUnmarshal` over `rdOwn`. -/
theorem wp_msgReadUnmarshal (l br : Loc) (cn : Nat) (s : Bool) (P : Proto GF) (R : List w8)
    (sl : GoSlice) (ds : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗ l ↦ (zeroValDef : Msg) ∗
        rdOwn br cn s P R ∗ frameIs P cn R (fun bs => ∃ m, bs = encMsg m) ∗ sl ↦* ds }}
      (App (App (Val (l @!! go.GoType.PointerType Msg.ty @!! go!"ReadUnmarshal")) (Val #br))
        (Val #sl))
    {{ (e : GoInterface) (n : w64), RET (PairV #e #n); ∃ (ds' : List w8), sl ↦* ds' ∗
        ((⌜e = interface.nil⌝ ∗ ∃ (v : Msg) (m : MsgV), ⌜(encMsg m).length ≤ ds.length⌝ ∗
            l ↦ v ∗ msgRep v m ∗ rdOwn br cn s P (R ++ frame (encMsg m))) ∨
         (⌜e ≠ interface.nil⌝ ∗ ∃ (R' : List w8) (v : Msg), ⌜R <+: R'⌝ ∗ l ↦ v ∗
            rdOwn br cn s P R')) }} := by
  iintro %Φ ⟨#Hpkg, Hl, Hrd, #HF, Hsl⟩ HΦ
  unfold rdOwn
  icases Hrd with ⟨%ri, %E, Hrd⟩
  iapply Msg.ReadUnmarshal.wp_proof l br ri cn s P E R sl ds $$ [$Hpkg $Hl $Hrd $HF $Hsl]
  inext
  iintro %e %n ⟨%ds', Hsl, Hres⟩
  iapply HΦ
  iexists ds'
  iframe Hsl
  icases Hres with (⟨%He, %v, %m, %Hm, Hl, #Hrep, Hrd⟩ | ⟨%He, %R', %v, %HR, Hl, Hrd⟩)
  · ileft
    isplitr
    · ipureintro; exact He
    iexists v, m
    iframe Hl Hrep
    isplitr
    · ipureintro; exact Hm
    iexists ri, E; iexact Hrd
  · iright
    isplitr
    · ipureintro; exact He
    iexists R', v
    iframe Hl
    isplitr
    · ipureintro; exact HR
    iexists ri, E; iexact Hrd

/-- `(*Command).MarshalWriteFlush` over `wrOwn`. -/
theorem wp_cmdMarshalWriteFlush (l : Loc) (v : Command) (c : CmdV) (bw : Loc) (cn : Nat)
    (s : Bool) (P : Proto GF) (W pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗ l ↦□ v ∗ cmdRep v c ∗
        ⌜c.commands.length ≤ 1⌝ ∗ wrOwn bw cn s P W pend err ∗
        □ (⌜(encCmd c).length < 2 ^ 32⌝ -∗ P cn (W ++ pend ++ frame (encCmd c))) }}
      (App (Val (l @!! go.GoType.PointerType Command.ty @!! go!"MarshalWriteFlush")) (Val #bw))
    {{ (e : GoInterface), RET #e; ∃ (W' pend' : List w8),
        ⌜W <+: W' ∧
          ((encCmd c).length < 2 ^ 32 ∧ W' ++ pend' <+: W ++ pend ++ frame (encCmd c) ∧
            (e = interface.nil → W' = W ++ pend ++ frame (encCmd c) ∧ pend' = []) ∨
           2 ^ 32 ≤ (encCmd c).length ∧ W' ++ pend' <+: W ++ pend)⌝ ∗
        wrOwn bw cn s P W' pend' e }} := by
  iintro %Φ ⟨#Hpkg, #Hl, #Hrep, %Hc1, Hwr, #HQ⟩ HΦ
  unfold wrOwn
  icases Hwr with ⟨%wi, %Ew, %sz, #Hwi, Hwr⟩
  iapply Command.MarshalWriteFlush.wp_proof l v c bw wi _ _ Ew sz W pend err
    $$ [$Hpkg $Hl $Hrep $Hwi $Hwr $HQ]
  · ipureintro; exact Hc1
  inext
  iintro %e ⟨%W', %pend', %HW, Hwr⟩
  iapply HΦ
  iexists W', pend'
  isplitr
  · ipureintro; exact HW
  iexists wi, Ew, sz
  iframe Hwi Hwr

/-- `(*Msg).MarshalWriteFlush` over `wrOwn`. -/
theorem wp_msgMarshalWriteFlush (l : Loc) (v : Msg) (m : MsgV) (bw : Loc) (cn : Nat)
    (s : Bool) (P : Proto GF) (W pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗ l ↦□ v ∗ msgRep v m ∗
        ⌜(encMsg m).length < 2 ^ 32⌝ ∗ wrOwn bw cn s P W pend err ∗
        □ P cn (W ++ pend ++ frame (encMsg m)) }}
      (App (Val (l @!! go.GoType.PointerType Msg.ty @!! go!"MarshalWriteFlush")) (Val #bw))
    {{ (e : GoInterface), RET #e; ∃ (W' pend' : List w8),
        ⌜W <+: W' ∧ W' ++ pend' <+: W ++ pend ++ frame (encMsg m) ∧
          (e = interface.nil → W' = W ++ pend ++ frame (encMsg m) ∧ pend' = [])⌝ ∗
        wrOwn bw cn s P W' pend' e }} := by
  iintro %Φ ⟨#Hpkg, #Hl, #Hrep, %Hm, Hwr, #HQ⟩ HΦ
  unfold wrOwn
  icases Hwr with ⟨%wi, %Ew, %sz, #Hwi, Hwr⟩
  iapply Msg.MarshalWriteFlush.wp_proof l v m bw wi _ _ Ew sz W pend err
    $$ [$Hpkg $Hl $Hrep $Hwi $Hwr $HQ]
  · ipureintro; exact Hm
  inext
  iintro %e ⟨%W', %pend', %HW, Hwr⟩
  iapply HΦ
  iexists W', pend'
  isplitr
  · ipureintro; exact HW
  iexists wi, Ew, sz
  iframe Hwi Hwr

/-- `WriteFlush` over `wrOwn`. -/
theorem wp_writeFlush (bw : Loc) (cn : Nat) (s : Bool) (P : Proto GF) (W pend : List w8)
    (err : GoInterface) (sl : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗ ⌜bs.length < 2 ^ 32⌝ ∗
        wrOwn bw cn s P W pend err ∗ □ P cn (W ++ pend ++ frame bs) ∗ sl ↦*{dq} bs }}
      (App (App (Val (@! WriteFlush)) (Val #bw)) (Val #sl))
    {{ (e : GoInterface), RET #e; ∃ (W' pend' : List w8),
        ⌜W <+: W' ∧ W' ++ pend' <+: W ++ pend ++ frame bs ∧
          (e = interface.nil → W' = W ++ pend ++ frame bs ∧ pend' = [])⌝ ∗
        sl ↦*{dq} bs ∗ wrOwn bw cn s P W' pend' e }} := by
  iintro %Φ ⟨#Hpkg, %Hbs, Hwr, #HQ, Hsl⟩ HΦ
  unfold wrOwn
  icases Hwr with ⟨%wi, %Ew, %sz, #Hwi, Hwr⟩
  iapply WriteFlush.wp_proof bw wi _ _ Ew sz W pend err sl dq bs
    $$ [$Hpkg $Hwi $Hwr $HQ $Hsl]
  · ipureintro; exact Hbs
  inext
  iintro %e ⟨%W', %pend', %HW, Hsl, Hwr⟩
  iapply HΦ
  iexists W', pend'
  iframe Hsl
  isplitr
  · ipureintro; exact HW
  iexists wi, Ew, sz
  iframe Hwi Hwr

end proofs

end Perennial.rabia.internal.tcp
