/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/AwaitConf.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
kit.go's `awaitConf(addr, ch)`: the configuration protocol's reader, shared by the server nodes
(`serve`) and the client nodes (`newClient`). Every connection to a configuration port carries a
prefix of a configuration message (the port's dialer protocol `P`: `conf.dialP` for a server
node, `conf.dialPC` for a client node), so `confLen` bytes read in full are a message
`c.encodeC cs`; `decode` accepts it; the first is handed to the caller over `ch` (a future whose
contract is `confMsg γ Ok R`), and every one is acknowledged (the port's acceptor protocol `Q`).
Before the first acknowledgment the node turns `Pre` into the persistent `A` that every
acknowledgment needs and `R`, which the future carries to the caller (a predicted node: its
registration, `client.claimGhost.spec`; the master: nothing). A connection cut short gives
`ReadFull` an error: nothing is decoded, nothing sent.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.Decode
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.NodeGhost

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [examples.swiftnet.Assumptions] [net.FieldAssumptions]
  [io.ExtraAssumptions]

set_option goose.wp.extras true

/-- `net.Listen(a)`'s result (its spec's postcondition, less the token). -/
abbrev listenRes (a : GoString) (lv err : GoInterface) : IProp netDistGF :=
  iprop((∃ (l : Loc) (lid : w64),
      ⌜lv = interface.mkOk (go.GoType.PointerType net.TCPListener.ty) #l ∧
        err = interface.nil⌝ ∗ net.ownListener l lid a) ∨
    (∃ i, ⌜lv = interface.nil ∧ err = interface.ok i⌝ ∗
      ∃ code : w64, ⌜code ≠ errNone⌝ ∗ net.opErr go!"listen" code err))

/-- `awaitConf(addr, ch)` on a configuration port `a` (its token and protocols `P`, `Q`), with
the future `ch` and the promise to fulfill it with `confMsg γ Ok R`, and `Pre`, which the node
turns into the acknowledgments' `A` and the caller's `R` (`hclaim`) before the first
acknowledgment: it never returns. -/
theorem wp_awaitConf (γ : SwiftNames netDistGF) (a : GoString) (ch : Loc) (γf : FutureNames)
    (P Q : Proto netDistGF) (Ok : Conf → List Change → Prop) (Pre A R : IProp netDistGF)
    [Persistent A]
    (hPc : ProtoPrefixClosed P)
    (hP : ∀ cid bs, bs.length = confLen → P cid bs ⊢ ∃ c cs, conf.is γ c ∗
      ⌜bs = c.encodeC cs ∧ c.valid ∧ c.changesOk cs ∧ Ok c cs⌝)
    (hQ : ∀ cid, A ⊢ Q cid [confAck])
    (hclaim : ⊢ isPkgInit (PROP := IProp netDistGF)
        pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet -∗ Pre ={⊤}=∗ A ∗ R) :
    {{ isPkgInit (PROP := IProp netDistGF)
          pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet ∗
        addrTok a ∗ addrProto a P Q ∗
        isFuture examples.swiftnet.msg γf ch ∗ Fulfill γf (confMsg γ Ok R) ∗ Pre }}
      (App (App (Val (@! examples.swiftnet.awaitConf)) (Val #a)) (Val #ch))
    {{ RET #(); False }} := by
  wp_start as ⟨Htok, #Hpr, #Hfut, Hful, HPre⟩
  wp_auto
  wp_apply net.Listen.wp_proof a $$ [$Htok] as %lv %err ⟨Htok, Hres⟩
  ihave HI : (∃ (lv err : GoInterface), "l" ∷ l_ptr ↦ lv ∗ "err" ∷ err_ptr ↦ err ∗
      "Hres" ∷ listenRes a lv err : IProp netDistGF) $$ [l err Hres]
  · iexists lv, err; iframe
  wp_for HI
  icases Hres with (⟨%l, %lid, %Hlv, #Hl⟩ | ⟨%i, %Hlv, -⟩) <;> obtain ⟨rfl, rfl⟩ := Hlv
  rotate_left
  · wp_auto
    wp_if_destruct
    · wp_apply time.wp_Sleep
      wp_apply net.Listen.wp_proof a $$ [$Htok] as %lv' %err' ⟨Htok, Hres⟩
      wp_for_post
      iframe
      iexists lv', err'
      iframe
    · exact absurd rfl Hif
  wp_auto
  wp_if_destruct
  · have := go.intoVal_inj Hif; simp at this
  ihave HJ : (∃ fst : Bool, "first" ∷ first_ptr ↦ fst ∗
      "Hful" ∷ (if fst then Fulfill γf (confMsg γ Ok R) else A) ∗
      "HPre" ∷ (if fst then Pre else True) : IProp netDistGF)
      $$ [first Hful HPre]
  · iexists true; simp only [↓reduceIte]; iframe
  wp_for HJ
  wp_apply net.TCPListener.Accept.wp_proof l lid a P Q $$ [$Hl $Hpr]
    as %cv %err Hres
  unfold net.newConnResult
  icases Hres with (⟨%c, %cid, %Hcv, #Hc, ⟨Hsend, Hrecv⟩, Hf⟩ | ⟨%i, %Hcv, -⟩) <;>
    obtain ⟨rfl, rfl⟩ := Hcv
  rotate_left
  · wp_auto
    wp_for_post
    iframe
    iexists fst; iframe
  wp_auto
  have hsl : slice.mk (arrayIndexRef w8 (sint.Z (W64 0)) b_ptr) (W64 9 - W64 0) (W64 9 - W64 0) =
      slice.mk b_ptr (W64 9) (W64 9) := by
    rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0]; rfl
  rw [hsl]
  ihave Hb := slice_array (GF := netDistGF) b_ptr _ _ (by decide) $$ b
  ihave #Hnet : isPkgInit (PROP := IProp netDistGF) pkg_id.net $$ []
  · iPkgInit
  ihave #Hio : isPkgInit (PROP := IProp netDistGF) pkg_id.io $$ []
  · iPkgInit
  ihave #Hrd := bufio.readsOk_conn (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c) cid
    true P $$ [$Hnet]
  · unfold net.rpc.connIface; iexists c; iframe Hc; ipureintro; rfl
  wp_apply bufio.wp_ReadFull _ (recvTok cid true P) [] _ _ $$ [$Hio $Hrd $Hrecv $Hb]
    as %n %err ⟨%data, %Hd, Hb, Hrecv, #He⟩
  have h9 : (zero_val (GoArray w8 9)).arr.length = 9 := rfl
  rw [h9] at Hd
  obtain ⟨rfl, Hdl, Herr⟩ := Hd
  cases err with
  | ok i =>
    have : data.length ≠ 9 := fun h => nomatch Herr.2 h
    wp_auto
    wp_apply net.TCPConn.Close.wp_proof c cid true $$ [$Hnet $Hc] as %err2 -
    wp_for_post
    iframe
    iexists fst; iframe
  | nil =>
    have hd9 : data.length = confLen := Herr.1 rfl
    rw [List.nil_append]
    ihave ⟨Hrecv, #Hp⟩ := recvTok_proto_closed hPc cid true data $$ Hrecv
    ihave ⟨%cf, %cs, #Hcf, %Hcf⟩ := hP cid data hd9 $$ Hp
    obtain ⟨rfl, Hv, Hcs, Hok⟩ := Hcf
    have hdrop : List.drop (cf.encodeC cs).length (List.replicate 9 (zero_val w8)) = [] := by
      rw [Conf.encodeC_length]; rfl
    rw [hdrop, List.append_nil]
    wp_auto
    rw [hsl]
    wp_apply wp_decode _ (DFrac.own 1) cf cs Hv Hcs $$ [$Hb] as %sl ⟨Hb, Hsl⟩
    skip
    cases fst
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hful with #HA
      wp_auto
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.byte))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := w8) (t := go.byte) [W8 107]
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %lit_ptr ⟨Hlit, -⟩
      wp_auto
      wp_apply net.TCPConn.Write.wp_proof c cid true _ [W8 107] (DFrac.own 1) Q []
        $$ [$Hnet $Hc $Hsend $Hlit] as %nw %errw -
      · iintro !>
        rw [show ([] : List w8) ++ [W8 107] = [confAck] from rfl]
        iapply hQ; iexact HA
      wp_apply net.TCPConn.Close.wp_proof c cid true $$ [$Hnet $Hc] as %err2 -
      wp_for_post
      iframe
      iexists false
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe
      iexact HA
    · simp only [↓reduceIte]
      imod hclaim $$ Hpkg HPre with ⟨#HA, HR⟩
      wp_auto
      wp_apply (wp_future_fulfill (t := examples.swiftnet.msg.ty) γf ch
        (⟨goConf cf, sl⟩ : examples.swiftnet.msg)) $$ [Hful Hsl HR]
      · iframe Hfut
        unfold Fulfilled
        iexists confMsg γ Ok R
        iframe Hful
        unfold confMsg
        iexists cf, cs
        iframe Hcf Hsl HR
        ipureintro; exact ⟨Hv, Hcs, Hok, rfl⟩
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.byte))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := w8) (t := go.byte) [W8 107]
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %lit_ptr ⟨Hlit, -⟩
      wp_auto
      wp_apply net.TCPConn.Write.wp_proof c cid true _ [W8 107] (DFrac.own 1) Q []
        $$ [$Hnet $Hc $Hsend $Hlit] as %nw %errw -
      · iintro !>
        rw [show ([] : List w8) ++ [W8 107] = [confAck] from rfl]
        iapply hQ; iexact HA
      wp_apply net.TCPConn.Close.wp_proof c cid true $$ [$Hnet $Hc] as %err2 -
      wp_for_post
      iframe
      iexists false
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe
      isplitl []
      · iexact HA
      itrivial

/-- The predicted node `n`'s registration before its first acknowledgment (the claim of its
ghost, `client.claimGhost.spec`): what `wp_awaitConf`'s `hclaim` asks of a predicted node. -/
theorem claim_pred (wp_claim : client.claimGhost.spec) (γ : SwiftNames netDistGF)
    (n : sp.PNode) :
    ⊢ isPkgInit (PROP := IProp netDistGF)
        pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet -∗
      (sp.inv γ.sp γ.conf γ.mem γ.lin ∗ sp.predTok γ.sp n ∗ client.ghostFresh) ={⊤}=∗
        sp.predReg γ.sp n ∗ client.nodeGhostOk γ.sp n := by
  iintro #Hpkg ⟨#Hinv, Htok, Hfr⟩
  ihave #Hcl : isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client
    $$ []
  · iPkgInit
  iapply (wp_claim γ.sp γ.conf γ.mem γ.lin n) $$ Hcl Hinv Hfr Htok

/-- The acknowledgment of predicted node `n`'s configuration port, once it registered. -/
theorem ackQP_of_reg (γ : SwiftNames netDistGF) (n : sp.PNode) (cid : w64) :
    sp.predReg γ.sp n ⊢ conf.ackQP γ n cid [confAck] := by
  unfold conf.ackQP
  iintro #H
  isplitl []
  · ipureintro; exact List.prefix_refl _
  iright; iexact H

/-- `awaitConf` at a predicted node `n`'s configuration port (a replica node's or a client
node's): it registers `n`'s prediction (from `sp.predTok` and the node's fresh ghost,
`client.ghostFresh`) before its first acknowledgment, and
the future carries `client.nodeGhostOk γ.sp n` to the caller with the message. -/
theorem wp_awaitConf_pred (wp_claim : client.claimGhost.spec) (γ : SwiftNames netDistGF)
    (n : sp.PNode) (a : GoString) (ch : Loc) (γf : FutureNames) (P : Proto netDistGF)
    (Ok : Conf → List Change → Prop) (hPc : ProtoPrefixClosed P)
    (hP : ∀ cid bs, bs.length = confLen → P cid bs ⊢ ∃ c cs, conf.is γ c ∗
      ⌜bs = c.encodeC cs ∧ c.valid ∧ c.changesOk cs ∧ Ok c cs⌝) :
    {{ isPkgInit (PROP := IProp netDistGF)
          pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet ∗
        addrTok a ∗ addrProto a P (conf.ackQP γ n) ∗
        isFuture examples.swiftnet.msg γf ch ∗
        Fulfill γf (confMsg γ Ok (client.nodeGhostOk γ.sp n)) ∗
        sp.inv γ.sp γ.conf γ.mem γ.lin ∗ sp.predTok γ.sp n ∗ client.ghostFresh }}
      (App (App (Val (@! examples.swiftnet.awaitConf)) (Val #a)) (Val #ch))
    {{ RET #(); False }} := by
  iintro %Φ ⟨#Hpkg, Htok, #Hpr, #Hfut, Hful, #Hinv, Hpt, Hfr⟩ HΦ
  iapply (wp_awaitConf γ a ch γf P (conf.ackQP γ n) Ok
    iprop(sp.inv γ.sp γ.conf γ.mem γ.lin ∗ sp.predTok γ.sp n ∗ client.ghostFresh)
    (sp.predReg γ.sp n)
    (client.nodeGhostOk γ.sp n) hPc hP (ackQP_of_reg γ n) (claim_pred wp_claim γ n))
    $$ [Htok Hful Hpt Hfr] HΦ
  iframe Hpkg Htok Hpr Hfut Hful
  iframe Hinv Hpt Hfr

/-- `awaitConf` at client node `c`'s configuration port (port 9000 of node `1 + c`, its
dialers' protocol `conf.dialPC`): the message carries the configuration and the node's leader
changes, and the node's registration `client.nodeGhostOk γ.sp (sp.PNode.cl c)`. -/
theorem wp_awaitConf_client (wp_claim : client.claimGhost.spec) (γ : SwiftNames netDistGF)
    (c : Nat) (a : GoString) (ch : Loc) (γf : FutureNames) :
    {{ isPkgInit (PROP := IProp netDistGF)
          pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet ∗
        addrTok a ∗ addrProto a (conf.dialPC γ) (conf.ackQP γ (sp.PNode.cl c)) ∗
        isFuture examples.swiftnet.msg γf ch ∗
        Fulfill γf (confMsg γ (fun _ _ => True) (client.nodeGhostOk γ.sp (sp.PNode.cl c))) ∗
        sp.inv γ.sp γ.conf γ.mem γ.lin ∗ sp.predTok γ.sp (sp.PNode.cl c) ∗ client.ghostFresh }}
      (App (App (Val (@! examples.swiftnet.awaitConf)) (Val #a)) (Val #ch))
    {{ RET #(); False }} :=
  wp_awaitConf_pred wp_claim γ (sp.PNode.cl c) a ch γf (conf.dialPC γ) (fun _ _ => True)
    (conf.dialPC_closed γ) (conf.dialPC_full γ)

/-- `awaitConf` at replica node `k`'s configuration port (server node `k + 2`; dialers'
protocol `conf.dialP`: no change). -/
theorem wp_awaitConf_replica (wp_claim : client.claimGhost.spec) (γ : SwiftNames netDistGF)
    (k : Nat) (a : GoString) (ch : Loc) (γf : FutureNames) :
    {{ isPkgInit (PROP := IProp netDistGF)
          pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet ∗
        addrTok a ∗ addrProto a (conf.dialP γ) (conf.ackQP γ (sp.PNode.rep k)) ∗
        isFuture examples.swiftnet.msg γf ch ∗
        Fulfill γf (confMsg γ (fun _ cs => cs = []) (client.nodeGhostOk γ.sp (sp.PNode.rep k))) ∗
        sp.inv γ.sp γ.conf γ.mem γ.lin ∗ sp.predTok γ.sp (sp.PNode.rep k) ∗ client.ghostFresh }}
      (App (App (Val (@! examples.swiftnet.awaitConf)) (Val #a)) (Val #ch))
    {{ RET #(); False }} :=
  wp_awaitConf_pred wp_claim γ (sp.PNode.rep k) a ch γf (conf.dialP γ) (fun _ cs => cs = [])
    (conf.dialP_closed γ) (conf.dialP_full γ)

/-- `awaitConf` at the master's configuration port (server node 1: `conf.dialP`, `conf.ackQ`;
nothing to register). -/
theorem wp_awaitConf_master (γ : SwiftNames netDistGF) (a : GoString) (ch : Loc)
    (γf : FutureNames) :
    {{ isPkgInit (PROP := IProp netDistGF)
          pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet ∗
        addrTok a ∗ addrProto a (conf.dialP γ) conf.ackQ ∗
        isFuture examples.swiftnet.msg γf ch ∗
        Fulfill γf (confMsg γ (fun _ cs => cs = []) iprop(True)) }}
      (App (App (Val (@! examples.swiftnet.awaitConf)) (Val #a)) (Val #ch))
    {{ RET #(); False }} := by
  have hQ : ∀ cid, (iprop(True) : IProp netDistGF) ⊢ conf.ackQ cid [confAck] := by
    intro cid; unfold conf.ackQ; iintro -; ipureintro; exact List.prefix_refl _
  have hcl : ⊢ isPkgInit (PROP := IProp netDistGF)
      pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet -∗ (iprop(True) : IProp netDistGF)
        ={⊤}=∗ iprop(True) ∗ iprop(True) := by
    iintro - - !>; isplitl [] <;> itrivial
  iintro %Φ ⟨#Hpkg, Htok, #Hpr, #Hfut, Hful⟩ HΦ
  iapply (wp_awaitConf γ a ch γf (conf.dialP γ) conf.ackQ (fun _ cs => cs = [])
    iprop(True) iprop(True) iprop(True) (conf.dialP_closed γ) (conf.dialP_full γ) hQ hcl)
    $$ [Htok Hful] HΦ
  iframe Hpkg Htok Hpr Hfut Hful

end proof

end Perennial.github_com.imdea_software.swiftpaxos
