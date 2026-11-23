/-
The network callees of the kit's own code (dsv-swiftpaxos, notes/dsv-swiftpaxos.md): `net`'s
`Dial`, `Listen`, `Listener.Accept`, `Conn.{Read,Write,Close}` (`Net/Spec/net/*`) and `io.ReadFull`
over a connection (`io.ReadFull.specLt`, dsv-rabia's `ConnRead.lean`: the condition asked only of
the reads `io.ReadAtLeast` makes), as hypotheses of the kit's proofs (`SwNetDeps`), linked in
`Link.lean` (CLAUDE.md, "Import tiers": a proof sees its callees through their specs), as
dsv-rabia's `KitNetDeps`; and the kit's own specs its proofs share (`awaitConf.spec`). Also the configuration protocol's address facts the proofs share
(`ownLis`, the start port's protocol laws).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ServersDefs
public import Dsverify.Proof.rabia.examples.rabianet.ConnRead
public import Net.Spec.net.Dial
public import Net.Spec.net.Listen
public import Net.Spec.net.Listener__Accept
public import Net.Spec.net.Conn__Read
public import Net.Spec.net.Conn__Write
public import Net.Spec.net.Conn__Close
public import Net.Proof.net.AtAddr
public import GooseLang.Ext.Net.Decide
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Pkg

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section deps
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [net.Assumptions] [net.FieldAssumptions] [io.Assumptions] [π : NetProtoGS]

/-- The network callees of the kit's code (see the file header). -/
structure SwNetDeps : Prop where
  dial : net.Dial.spec (GF := netDistGF) (hG := hG)
  listen : net.Listen.spec (GF := netDistGF) (hG := hG)
  accept : net.Listener.Accept.spec (GF := netDistGF) (hG := hG)
  read : net.Conn.Read.spec (GF := netDistGF) (hG := hG)
  write : net.Conn.Write.spec (GF := netDistGF) (hG := hG)
  close : net.Conn.Close.spec (GF := netDistGF) (hG := hG)
  readFullLt : rabia.examples.rabianet.io.ReadFull.specLt (GF := netDistGF) (hG := hG)

/-- The listener `li` (`l`) at `a`, open, with its address (what `Listen` gives at a valid
address). -/
def ownLis (li : GoInterface) (l : w64) (a : GoString) : IProp netDistGF :=
  iprop(net.isListener li l ∗ netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true ∗
    netLisAt (extLocalGS netExt (L := hG.goose_localGS)) l a)

end deps

section conf
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [π : NetProtoGS]
variable [SwiftNetPkgState netDistGF]

/-- `conf.startP` is prefix-closed. -/
theorem conf.startP_closed (γ : SwiftNames netDistGF) : ProtoPrefixClosed (conf.startP γ) where
  nil cid := by
    unfold conf.startP
    iintro !>
    ileft; ipureintro; rfl
  pre cid a b h := by
    unfold conf.startP
    iintro #(%Hb | ⟨%c, #Hc, #Hr, %Hb⟩)
    · iintro !>; ileft; ipureintro; subst Hb; exact List.prefix_nil.mp h
    · iintro !>; iright; iexists c; iframe Hc Hr; ipureintro; exact h.trans Hb

/-- What a client node's start port's reader has read, `confLen` bytes of it: a configuration's
encoding with no change, and every predicted node's registration. -/
theorem conf.startP_full (γ : SwiftNames netDistGF) (cid : Nat) (bs : List w8)
    (hl : bs.length = confLen) :
    conf.startP γ cid bs ⊢ ∃ c cs, conf.is γ c ∗ sp.allPredsReg γ.sp γ.conf ∗
      ⌜bs = c.encodeC cs ∧ c.valid ∧ c.changesOk cs ∧ cs = []⌝ := by
  unfold conf.startP
  iintro (%Hb | ⟨%c, #Hc, #Hr, %Hb⟩)
  · subst Hb; simp [confLen, maxChanges] at hl
  · ihave %Hv := ((conf.is_confIs γ c).1.trans (confIs_valid γ.conf c)) $$ Hc
    iexists c, []
    iframe Hc Hr
    ipureintro
    refine ⟨?_, Hv, ⟨by simp [maxChanges], by simp⟩, rfl⟩
    exact Hb.eq_of_length (by rw [hl]; exact (Conf.encodeC_length c []).symm)

end conf

section protos
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [SwiftNetPkgState netDistGF]

/-! ## The configuration ports' protocols -/

/-- The acknowledgment protocol of server node `k + 1`'s configuration port (`confAddrs[k]`):
the master's carries nothing, replica node `k - 1`'s its registration. -/
def srvAckQ (γ : SwiftNames netDistGF) (k : Nat) : Proto netDistGF :=
  if k = 0 then conf.ackQ else conf.ackQP γ (sp.PNode.rep (k - 1))

theorem protoP_conf (γ : SwiftNames netDistGF) (k : Nat) (a : GoString) (hk : confAddrs[k]? = some a) :
    protoP γ a = conf.dialP γ ∧ protoQ γ a = srvAckQ γ k := by
  match k, hk with
  | 0, hk | 1, hk | 2, hk | 3, hk | 4, hk | 5, hk =>
    simp only [confAddrs, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at hk
    subst hk
    unfold protoP protoQ srvAckQ
    rw [if_pos (by decide)]
    exact ⟨rfl, rfl⟩

theorem protoP_clientConf (γ : SwiftNames netDistGF) (c : Nat) (a : GoString)
    (hc : clientConfAddrs[c]? = some a) :
    protoP γ a = conf.dialPC γ ∧ protoQ γ a = conf.ackQP γ (sp.PNode.cl c) := by
  match c, hc with
  | 0, hc | 1, hc | 2, hc | 3, hc | 4, hc | 5, hc =>
    simp only [clientConfAddrs, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at hc
    subst hc
    unfold protoP protoQ
    rw [if_neg (by decide), if_pos (by decide)]
    exact ⟨rfl, rfl⟩

theorem protoP_clientStart (γ : SwiftNames netDistGF) (c : Nat) (a : GoString)
    (hc : clientStartAddrs[c]? = some a) :
    protoP γ a = conf.startP γ ∧ protoQ γ a = conf.ackQ := by
  match c, hc with
  | 0, hc | 1, hc | 2, hc | 3, hc | 4, hc | 5, hc =>
    simp only [clientStartAddrs, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at hc
    subst hc
    simp [protoP, protoQ, clientConfAddrs, confAddrs, clientStartAddrs, List.idxOf?,
      List.findIdx?, List.findIdx?.go]

/-- What `configure` needs of the run (persistent; from `common`). -/
def confEnv (γ : SwiftNames netDistGF) : IProp netDistGF :=
  iprop(([∗list] k ↦ a ∈ confAddrs, addrProto a (conf.dialP γ) (srvAckQ γ k)) ∗
    ([∗list] c ↦ a ∈ clientConfAddrs, addrProto a (conf.dialPC γ)
      (conf.ackQP γ (sp.PNode.cl c))) ∗
    [∗list] a ∈ clientStartAddrs, addrProto a (conf.startP γ) conf.ackQ)

instance confEnv_persistent (γ : SwiftNames netDistGF) : Persistent (confEnv γ) := by
  unfold confEnv; infer_instance

theorem common_confEnv [RpcHttpAddr netDistGF] (γ : SwiftNames netDistGF) :
    common γ ⊢ confEnv γ := by
  unfold common confEnv
  iintro ⟨#Hpl, -, -, -, -⟩
  have hpl : plainAddrs = ([orchAddr] ++ clientNodeAddrs ++ clientConfAddrs ++ clientStartAddrs) ++
      confAddrs := rfl
  rw [hpl]
  ihave ⟨#H2, #Hc⟩ := BigSepL.bigSepL_append.1 $$ Hpl
  ihave ⟨#H3, #Hcs⟩ := BigSepL.bigSepL_append.1 $$ H2
  ihave ⟨-, #Hcc⟩ := BigSepL.bigSepL_append.1 $$ H3
  isplitl
  · iapply BigSepL.bigSepL_mono _ $$ Hc
    intro k a hka
    obtain ⟨h1, h2⟩ := protoP_conf γ k a hka
    rw [h1, h2]
  isplitl
  · iapply BigSepL.bigSepL_mono _ $$ Hcc
    intro k a hka
    obtain ⟨h1, h2⟩ := protoP_clientConf γ k a hka
    rw [h1, h2]
  · iapply BigSepL.bigSepL_mono _ $$ Hcs
    intro k a hka
    obtain ⟨h1, h2⟩ := protoP_clientStart γ k a hka
    rw [h1, h2]

end protos

/-- An acknowledgment of a predicted node's configuration port: its registration. -/
theorem ackQP_reg [GoGlobalContext] [GooseGlobalGS .hasLC netDistGF] (γ : SwiftNames netDistGF)
    (n : sp.PNode) (cid : Nat) (ext : List w8) (h : [confAck] <+: ext) :
    conf.ackQP γ n cid ext ⊢ sp.predReg γ.sp n := by
  unfold conf.ackQP
  iintro ⟨-, (%He | #H)⟩
  · subst He; simp at h
  · iexact H


section netlemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [SwiftNetPkgState netDistGF] [examples.swiftnet.Assumptions]
variable [net.Assumptions] [net.FieldAssumptions] [io.Assumptions]

/-- `poll.ErrDeadlineExceeded`'s value, from the kit's initialization. -/
theorem kit_ed_init :
    isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet ⊢
      ∃ ed : GoInterface, globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed := by
  iintro #Hpkg
  ihave #Hpoll : (isPkgInit (PROP := IProp netDistGF) pkg_id.internal.poll) $$ []
  · iPkgInit
  iapply github_com.mit_pdos.etcd_grove.examples.net.wire.ed_of_poll $$ Hpoll

/-- `c.Close()` of a connection's end: it returns. -/
theorem wp_closeConn (D : SwNetDeps (hG := hG)) (t : Loc) (cn : Nat) (s : Bool) (a : GoString)
    (la ra : GoInterface) :
    {{ net.connAt t cn s a la ra ∗ connIs (Gg := hG.goose_globalGS) cn }}
      (App (Val #(methods (go.GoType.PointerType net.TCPConn.ty) go!"Close" #t)) (Val #()))
    {{ (err : GoInterface), RET #err; True }} := by
  iintro %Φ ⟨#Hca, #Hconn⟩ HΦ
  iapply D.close t cn s a la ra (fun _ => iprop(True)) $$ []
  · iframe Hca
    imod close_au cn s $$ Hconn with ⟨%st, %dd, Hst, Hdd, Hcl⟩
    imodintro
    iexists st, dd
    iframe Hst Hdd
    iintro %res %st' %d' %Hd' Hst Hdd
    imod Hcl $$ %res %st' %d' %Hd' Hst Hdd with -
    imodintro
    itrivial
  inext
  iintro %err -
  iapply HΦ; itrivial

/-- `c.Write(ls)` of the acknowledgment on an accepted end whose acceptor protocol allows it. -/
theorem wp_ack (D : SwNetDeps (hG := hG)) (t : Loc) (cn : Nat) (a : GoString)
    (la ra ed : GoInterface) (Q : Proto netDistGF) (ls : GoSlice) :
    {{ net.connAt t cn true a la ra ∗
        globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗
        □ Q cn ([] ++ [W8 107]) ∗ sendTok (Gg := hG.goose_globalGS) cn true Q [] ∗
        ls ↦* [W8 107] }}
      (App (Val #(methods (go.GoType.PointerType net.TCPConn.ty) go!"Write" #t)) (Val #ls))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err); True }} := by
  iintro %Φ ⟨#Hca, #Hed, #HQ, Hsend, Hls⟩ HΦ
  iapply D.write t cn true a la ra ls [W8 107] (DFrac.own 1) ed
    (writeP cn true Q []) $$ [Hls Hsend]
  · iframe Hca Hls Hed
    isplitl [Hsend]
    · iapply writeP_init $$ Hsend
    · iapply write_acc cn true Q [] [W8 107] $$ HQ
  inext
  iintro %n %err -
  iapply HΦ; itrivial

end netlemmas

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [SwiftNetPkgState netDistGF] [examples.swiftnet.Assumptions]

/-- `awaitConf(a, ch)` on a configuration port `a` (its protocols `P`, `Q`), with the future
`ch` and the promise to fulfill it with `confMsg γ Ok R`, and `Pre`, which the node turns, with
the first message's `X`, into the acknowledgments' `A` and the caller's `R` (`hclaim`) before the
first acknowledgment: it never returns. -/
abbrev awaitConf.spec : Prop :=
  ∀ (γ : SwiftNames netDistGF) (a : GoString) (ch : Loc) (γf : FutureNames)
    (P Q : Proto netDistGF) (Ok : Conf → List Change → Prop) (Pre A R X : IProp netDistGF),
  ProtoPrefixClosed P →
  (∀ cid bs, bs.length = confLen → P cid bs ⊢ ∃ c cs, conf.is γ c ∗ X ∗
      ⌜bs = c.encodeC cs ∧ c.valid ∧ c.changesOk cs ∧ Ok c cs⌝) →
  (∀ cid, A ⊢ Q cid [confAck]) →
  (⊢ isPkgInit (PROP := IProp netDistGF)
      pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet -∗ Pre -∗ X ={⊤}=∗ □ A ∗ R) →
  {{ isPkgInit (PROP := IProp netDistGF)
        pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet ∗
      addrProto (Gg := hG.goose_globalGS) a P Q ∗
      isFuture examples.swiftnet.msg γf ch ∗ Fulfill γf (confMsg γ Ok R) ∗ Pre }}
    (App (App (Val (@! examples.swiftnet.awaitConf)) (Val #a)) (Val #ch))
  {{ RET #(); False }}

/-- `sendConf(a, b)`: the message `bs` meets `a`'s dialers' protocol; an acknowledgment carries
`a`'s acceptors' protocol of a reply starting with `confAck`. -/
abbrev sendConf.spec : Prop :=
  ∀ (a : GoString) (b : GoSlice) (bs : List w8) (P Q : Proto netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF)
        pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet ∗
      addrProto (Gg := hG.goose_globalGS) a P Q ∗ □ (∀ cid, P cid bs) ∗ b ↦* bs }}
    (App (App (Val (@! examples.swiftnet.sendConf)) (Val #a)) (Val #b))
  {{ (ok : Bool), RET #ok;
      if ok then ∃ (cid : Nat) (ext : List w8), ⌜[confAck] <+: ext⌝ ∗ □ Q cid ext else True }}

/-- `New(addrs)`: from the configuration's writer token and the run's facts, every predicted node
of the configuration it chose registered (and every node configured, the client nodes started). -/
abbrev New.spec [RpcHttpAddr netDistGF] (γ : SwiftNames netDistGF) : Prop :=
  ∀ (asl : GoSlice),
  {{ isPkgInit (PROP := IProp netDistGF)
        pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet ∗
      conf.writer γ ∗ common γ ∗ asl ↦*□ addrs }}
    (App (Val (@! examples.swiftnet.New)) (Val #asl))
  {{ RET #(); sp.allPredsReg γ.sp γ.conf }}

end spec

end Perennial.github_com.imdea_software.swiftpaxos
