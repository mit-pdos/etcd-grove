/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/client/Readers.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The client's readers (client/client.go `RegisterRPCTable`, called by `swift.NewClient` on the
client's table): a goroutine per connected replica reads a type byte, looks it up in the
table, decodes the message (`Unmarshal.lean`) and hands it, after `time.Sleep` of the
(nil) latency table's wait, to the message's channel from a goroutine of its own.

The reader's invariant: what it has read are the frames of client messages `done`
(`sp.cw.cMsg`); the stream (protocol `sp.outQ`) gives the next type byte as a client
message's (`sp.cw.next_code`), the decoded message as the stream's next with its witness
(`sp.cw.rd_witness`). Each channel carries the decoded messages with their witnesses:
`repP` (`MReply`: the handler's `replyArg`), `facP` (`MFastAckClient`), `lsP`
(`MLightSlowAck`: the handler's `lsArg`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.Unmarshal
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.HandleReply
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.rpc.TableC
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.defs.LatencyTable__WaitDuration
public import Perennial.Proof.time.Link

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.rd

open swift.handler

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [client.Assumptions] [time.Assumptions]
  [dlog.Assumptions] [bytes.Assumptions]

/-- An `MReply` on `replyChan`. -/
def repP (H : HC) (v : GoInterface) : IProp netDistGF :=
  iprop(∃ (x : sp.CmdId) (l : Loc),
    ⌜v = interface.mkOk (go.GoType.PointerType swift.MReply.ty) #l⌝ ∗ replyArg H x l)

/-- An `MLightSlowAck` on `lightSlowAckChan`. -/
def lsP (H : HC) (v : GoInterface) : IProp netDistGF :=
  iprop(∃ (x : sp.CmdId) (l : Loc),
    ⌜v = interface.mkOk (go.GoType.PointerType swift.MLightSlowAck.ty) #l⌝ ∗ lsArg H x l)

/-- An `MFastAckClient` on `fastAckClientChan`. -/
def facP (H : HC) (v : GoInterface) : IProp netDistGF :=
  iprop(∃ (l : Loc) (fac : swift.MFastAckClient) (hs : List sp.Hash),
    ⌜v = interface.mkOk (go.GoType.PointerType swift.MFastAckClient.ty) #l ∧ sp.cw.hashOk hs ∧
      (cmdOf fac.CmdId').cl = H.cid⌝ ∗
    l ↦□ fac ∗ fac.Checksum' ↦*□ hs.map shashOf ∗
    sp.msgOk H.γ H.γc H.γm (.fastAckClient fac.Replica' fac.Ballot' (cmdOf fac.CmdId') hs))

instance repP_persistent H v : Persistent (repP H v) := by unfold repP; infer_instance
instance lsP_persistent H v : Persistent (lsP H v) := by unfold lsP; infer_instance
instance facP_persistent H v : Persistent (facP H v) := by
  unfold facP; haveI := sp.msgOk_persistent (γ := H.γ) (γc := H.γc) (γm := H.γm); infer_instance

/-- One replica's reader: none, or a connection of kind `client cid` with its reader at the
stream's start. -/
def rdEnd (H : HC) (rd : Loc) : IProp netDistGF :=
  iprop(⌜rd = null⌝ ∨ ∃ (srv : GoInterface) (c : w64),
    bufio.readerOk srv (recvTok c false (sp.outQ H.γ H.γc H.γm)) ∗
    sp.connKind H.γ c (.client H.cid) ∗
    bufio.ownReader rd srv (recvTok c false (sp.outQ H.γ H.γc H.γm)) [])

/-- The client's table, read-only: the three client messages' entries, their channels'
protocols. -/
def tblOk (H : HC) (t : Loc) : IProp netDistGF :=
  iprop(∃ (M : GMap w8 rpc.Pair') (o1 o2 o3 : Loc) (ch1 ch2 ch3 : Loc) (g1 g2 g3 : ChanNames),
    rpc.tblRO t M ∗
    ⌜M !! W8 10 = some ⟨interface.mkOk (go.GoType.PointerType swift.MFastAckClient.ty) #o1, ch1⟩ ∧
      M !! W8 12 = some ⟨interface.mkOk (go.GoType.PointerType swift.MLightSlowAck.ty) #o2, ch2⟩ ∧
      M !! W8 15 = some ⟨interface.mkOk (go.GoType.PointerType swift.MReply.ty) #o3, ch3⟩⌝ ∗
    isChanBag g1 ch1 (facP H) ∗ isChanBag g2 ch2 (lsP H) ∗ isChanBag g3 ch3 (repP H))

instance tblOk_persistent H t : Persistent (tblOk H t) := by unfold tblOk; infer_instance

end defs

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [client.Assumptions] [time.Assumptions]
  [dlog.Assumptions] [bytes.Assumptions]

/-- `c.RegisterRPCTable(t)` on the client's struct `cl`: a reader per connected replica. -/
abbrev RegisterRPCTable.specI : Prop :=
  ∀ (H : HC) (cl t : Loc) (rsl rpsl : GoSlice) (rds : List Loc) (l : List GoString)
    (ov : GoInterface),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.bufio ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.io ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.time ∗
      structFieldRef client.Client go!"readers" cl ↦□ rsl ∗ rsl ↦*□ rds ∗
      structFieldRef client.Client go!"replicas" cl ↦□ rpsl ∗ rpsl ↦*□ l ∗
      structFieldRef client.Client go!"dt" cl ↦□ null ∗
      globalAddr swift.errVarintOverflow ↦□ ov ∗ ⌜ov ≠ interface.nil ∧ rds.length = l.length⌝ ∗
      tblOk H t ∗ [∗list] rd ∈ rds, rdEnd H rd }}
    (App (Val (cl @!! go.GoType.PointerType client.Client.ty @!! go!"RegisterRPCTable")) (Val #t))
  {{ RET #(); True }}

end specs

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [client.Assumptions] [time.Assumptions]
  [dlog.Assumptions] [bytes.Assumptions] [io.Assumptions]
  [errors.Assumptions] [bufio.Assumptions] [rpc.Assumptions] [replica.defs.Assumptions]

set_option goose.wp.extras true

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [swift.Assumptions] [replica.Assumptions] [client.Assumptions]
  [time.Assumptions] [dlog.Assumptions] [bytes.Assumptions] [io.Assumptions]
  [errors.Assumptions] [bufio.Assumptions] [rpc.Assumptions] [replica.defs.Assumptions] in
/-- A buffered reader is not nil (unfolds the harness's `ownReader`: a missing law). -/
theorem ownReader_not_null (br : Loc) (rd : GoInterface) (I : List w8 → IProp netDistGF)
    (R : List w8) : bufio.ownReader br rd I R ⊢ ⌜br ≠ null⌝ := by
  unfold bufio.ownReader bufio.readerRep
  iintro ⟨%pend, %perr, -, %buf, %r, %w, %lb, %lrs, %pre, %post, Hb, -⟩
  iapply typedPointsto_not_null $$ Hb

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [replica.Assumptions] [client.Assumptions]
  [time.Assumptions] [dlog.Assumptions] [bytes.Assumptions] [io.Assumptions]
  [errors.Assumptions] [bufio.Assumptions] [rpc.Assumptions] [replica.defs.Assumptions] in
theorem wp_New_MFastAckClient (o : Loc) :
    {{ (True : IProp netDistGF) }}
      (App (Val (o @!! go.GoType.PointerType swift.MFastAckClient.ty @!! go!"New")) (Val #()))
    {{ (l : Loc), RET #(interface.mkOk (go.GoType.PointerType swift.MFastAckClient.ty) #l);
        l ↦ (zero_val swift.MFastAckClient) }} := by
  wp_start
  wp_auto
  wp_alloc_auto
  wp_auto
  iapply HΦ; iframe

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [replica.Assumptions] [client.Assumptions]
  [time.Assumptions] [dlog.Assumptions] [bytes.Assumptions] [io.Assumptions]
  [errors.Assumptions] [bufio.Assumptions] [rpc.Assumptions] [replica.defs.Assumptions] in
theorem wp_New_MLightSlowAck (o : Loc) :
    {{ (True : IProp netDistGF) }}
      (App (Val (o @!! go.GoType.PointerType swift.MLightSlowAck.ty @!! go!"New")) (Val #()))
    {{ (l : Loc), RET #(interface.mkOk (go.GoType.PointerType swift.MLightSlowAck.ty) #l);
        l ↦ (zero_val swift.MLightSlowAck) }} := by
  wp_start
  wp_auto
  wp_alloc_auto
  wp_auto
  iapply HΦ; iframe

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [replica.Assumptions] [client.Assumptions]
  [time.Assumptions] [dlog.Assumptions] [bytes.Assumptions] [io.Assumptions]
  [errors.Assumptions] [bufio.Assumptions] [rpc.Assumptions] [replica.defs.Assumptions] in
theorem wp_New_MReply (o : Loc) :
    {{ (True : IProp netDistGF) }}
      (App (Val (o @!! go.GoType.PointerType swift.MReply.ty @!! go!"New")) (Val #()))
    {{ (l : Loc), RET #(interface.mkOk (go.GoType.PointerType swift.MReply.ty) #l);
        l ↦ (zero_val swift.MReply) }} := by
  wp_start
  wp_auto
  wp_alloc_auto
  wp_auto
  iapply HΦ; iframe

theorem RegisterRPCTable.wp_proof : RegisterRPCTable.specI (hG := hG) := by
  intro H cl t rsl rpsl rds l ov
  wp_start as ⟨#Hrsl, #Hrds, #Hrpsl, #Hl, #Hdt, #Hov, ⟨%Hovn, %Hlen⟩, #Htbl, Hends⟩
  wp_auto
  rename_i ip0
  irename : (ip0 ↦ (zero_val w64 : w64)) => Hi0
  ipersist c
  ipersist t
  ihave %Hrl := ownSlice_len $$ Hrds
  ihave %Hll := ownSlice_len $$ Hl
  ihave HL : (∃ (k : Nat) (rv : Loc) (iv : w64),
      "i" ∷ i_ptr ↦ W64 k ∗ "reader" ∷ reader_ptr ↦ rv ∗ "i'" ∷ ip0 ↦ iv ∗
      "Hends" ∷ ([∗list] rd ∈ rds.drop k, rdEnd H rd) ∗ "%Hk" ∷ ⌜k ≤ rds.length⌝ : IProp netDistGF)
    $$ [i reader Hi0 Hends]
  · iexists 0, _, _
    iframe
    ipureintro; omega
  wp_for HL
  wp_if_destruct
  · have hk : k < rds.length := by
      have h1 : sint.Z (W64 (k : Int)) = k := by word
      obtain ⟨h2, h3⟩ := Hrl
      have : sint.nat rsl.len = (sint.Z rsl.len).toNat := rfl
      omega
    obtain ⟨rd, hrd⟩ : ∃ rd, rds[k]? = some rd := ⟨_, List.getElem?_eq_getElem hk⟩
    rw [List.drop_eq_getElem_cons hk, (List.getElem_eq_iff hk).2 hrd]
    icases (BigSepL.bigSepL_cons).1 $$ Hends with ⟨Hend, Hends⟩
    have hk64 : sint.Z (W64 (k : Int)) = k := by word
    have hb : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z rsl.len := by
      obtain ⟨h2, h3⟩ := Hrl
      have : sint.nat rsl.len = (sint.Z rsl.len).toNat := rfl
      omega
    rw [ite_cond_eq_true _ _ (eq_true hb)]
    wp_apply wp_load_slice_index rsl (sint.Z (W64 (k : Int))) rds DFrac.discard rd (by omega) $$ [Hrds] as -
    · iframe Hrds; ipureintro; rw [hk64]; simpa using hrd
    try wp_auto
    unfold rdEnd
    icases Hend with (%Hnull | ⟨%srv, %cc, #Hrd, #Hk, Hown⟩)
    · subst Hnull
      wp_auto
      wp_for_post
      iframe
      iexists k + 1, _, _
      iframe
      isplitl [i]
      · iExactEq i; congr 1; word
      ipureintro; omega
    ihave %hnn := ownReader_not_null $$ Hown
    rw [decide_eq_false hnn]
    wp_auto
    wp_apply wp_fork $$ [Hown]
    · -- the reader
      wp_auto
      ipersist i
      ihave HR : (∃ done : List sp.Msg,
          "Hown" ∷ bufio.ownReader rd srv (recvTok cc false (sp.outQ H.γ H.γc H.γm)) (sp.framesOf done) ∗
          "%Hdone" ∷ ⌜∀ d ∈ done, sp.cw.cMsg H.cid d⌝ : IProp netDistGF) $$ [Hown]
      · iexists []
        iframe
        ipureintro; simp
      wp_for HR
      wp_apply bufio.wp_ReadByte rd srv _ _ $$ [$Hpkg3 $Hrd $Hown] as %cb %err Hr
      icases Hr with (⟨%Hen, Hown⟩ | ⟨%Hen, -, Hown⟩)
      rotate_left
      · -- a read error: the reader stops
        rcases err with e | _
        · wp_auto
          wp_for_post
          itrivial
        · exact absurd rfl Hen
      subst Hen
      wp_auto
      icases sp.cw.rd_stOk rd srv cc H.cid _ $$ [$Hk $Hown] with ⟨Hown, %Hst⟩
      have hcode := sp.cw.next_code Hdone Hst
      unfold tblOk
      icases Htbl with ⟨%M, %o1, %o2, %o3, %ch1, %ch2, %ch3, %g1, %g2, %g3, #HM, %HMk, #Hb1, #Hb2, #Hb3⟩
      wp_apply rpc.wp_Get t M cb $$ [$HM]
      obtain ⟨hM1, hM2, hM3⟩ := HMk
      rcases hcode with rfl | rfl | rfl
      · -- MFastAckClient
        rw [hM1]
        simp only [Option.getD_some, Option.isSome_some, _root_.decide_true]
        wp_auto
        ipersist p
        wp_apply wp_New_MFastAckClient o1 as %ob Hob
        wp_apply (MFastAckClient.Unmarshal.wp_proof ob _ rd srv cc H.γ H.γc H.γm H.cid done ov) $$
          [$Hpkg4 $Hpkg3 $Hrd $Hk $Hown $Hov $Hob] as %err ⟨%data, Hown, Hres⟩
        · ipureintro; exact ⟨Hovn, Hdone⟩
        icases Hres with (⟨%Hen, %r, %b, %x, %cs, %csl, ⟨%Hd, %Hh⟩, Hob, Hcsl⟩ | ⟨%Hen, %v', -⟩)
        rotate_left
        · rcases err with e | _
          · wp_auto
            wp_for_post
            itrivial
          · exact absurd rfl Hen
        subst Hen Hd
        have hk : sp.cw.cKind (.fastAckClient r b x cs) := Hh
        icases sp.cw.rd_witness rd srv cc H.cid done (.fastAckClient r b x cs) Hdone hk $$
          [$Hk Hown] with ⟨Hown, #Hw, %Hcm⟩
        · iExactEq Hown; simp [sp.Msg.frame, sp.Msg.code, sp.rpcTable]; rfl
        ipersist Hob
        ipersist Hcsl
        ihave #HP : facP H (interface.mkOk (go.GoType.PointerType swift.MFastAckClient.ty) #ob) $$ []
        · unfold facP
          iexists ob, _, cs
          iframe Hob Hcsl
          isplitr
          · ipureintro; exact ⟨rfl, Hh, Hcm.1⟩
          iExactEq Hw; rfl
        wp_auto
        wp_apply wp_fork
        · -- the message's goroutine: no wait (nil latency table), then the channel
          wp_auto
          have hbl : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z rpsl.len := by
            obtain ⟨h2, h3⟩ := Hll
            have : sint.nat rpsl.len = (sint.Z rpsl.len).toNat := rfl
            omega
          rw [ite_cond_eq_true _ _ (eq_true hbl)]
          obtain ⟨a, ha⟩ : ∃ a, l[k]? = some a := ⟨_, List.getElem?_eq_getElem (by omega)⟩
          wp_apply wp_load_slice_index rpsl (sint.Z (W64 (k : Int))) l DFrac.discard a (by omega) $$ [Hl] as -
          · iframe Hl; ipureintro; rw [hk64]; simpa using ha
          wp_apply replica.defs.LatencyTable.WaitDuration.wp_proofNil a
          wp_apply time.wp_Sleep
          ihave #Hp := p
          iStructNamed Hp
          wp_auto
          wp_apply wp_bag_send g1 ch1 _ (facP H) $$ [$Hb1 $HP]
          itrivial
        try wp_auto
        wp_for_post
        iframe
        iexists done ++ [.fastAckClient r b x cs]
        isplitl [Hown]
        · iExactEq Hown; simp [sp.framesOf]
        ipureintro
        intro d hd
        rcases List.mem_append.1 hd with h' | h'
        · exact Hdone d h'
        · simp at h'; subst h'; exact Hcm
      · -- MLightSlowAck
        rw [hM2]
        simp only [Option.getD_some, Option.isSome_some, _root_.decide_true]
        wp_auto
        ipersist p
        wp_apply wp_New_MLightSlowAck o2 as %ob Hob
        ihave #Hbr := bufio.bufioReadsOk rd srv (recvTok cc false (sp.outQ H.γ H.γc H.γm)) $$ [$Hpkg3 $Hrd]
        wp_apply (MLightSlowAck.Unmarshal.wp_proof ob _ _ _ _) $$
          [$Hpkg4 $Hbr $Hown $Hob] as %err ⟨%data, Hown, Hres⟩
        icases Hres with (⟨%Hen, %sa, %Hd, Hob⟩ | ⟨%Hen, %v', -⟩)
        rotate_left
        · rcases err with e | _
          · wp_auto
            wp_for_post
            itrivial
          · exact absurd rfl Hen
        subst Hen Hd
        icases sp.cw.rd_witness rd srv cc H.cid done (.lightSlowAck sa) Hdone trivial $$
          [$Hk Hown] with ⟨Hown, #Hw, %Hcm⟩
        · iExactEq Hown; simp [sp.Msg.frame, sp.Msg.code, sp.rpcTable, sp.Msg.body]; rfl
        ipersist Hob
        ihave %Hwire : ⌜sp.wireOk sa.rep sa.bal⌝ $$ [Hw]
        · ihave Hw2 := Hw
          simp only [sp.msgOk]
          icases Hw2 with ⟨%Hw', -⟩
          ipureintro; exact Hw'
        ihave #HP : lsP H (interface.mkOk (go.GoType.PointerType swift.MLightSlowAck.ty) #ob) $$ []
        · unfold lsP lsArg
          iexists sa.id, ob
          isplitr
          · ipureintro; rfl
          iexists _
          iframe Hob
          isplitr
          · ipureintro; exact ⟨rfl, Hcm.1, Hwire⟩
          iExactEq Hw; rfl
        wp_auto
        wp_apply wp_fork
        · -- the message's goroutine: no wait (nil latency table), then the channel
          wp_auto
          have hbl : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z rpsl.len := by
            obtain ⟨h2, h3⟩ := Hll
            have : sint.nat rpsl.len = (sint.Z rpsl.len).toNat := rfl
            omega
          rw [ite_cond_eq_true _ _ (eq_true hbl)]
          obtain ⟨a, ha⟩ : ∃ a, l[k]? = some a := ⟨_, List.getElem?_eq_getElem (by omega)⟩
          wp_apply wp_load_slice_index rpsl (sint.Z (W64 (k : Int))) l DFrac.discard a (by omega) $$ [Hl] as -
          · iframe Hl; ipureintro; rw [hk64]; simpa using ha
          wp_apply replica.defs.LatencyTable.WaitDuration.wp_proofNil a
          wp_apply time.wp_Sleep
          ihave #Hp := p
          iStructNamed Hp
          wp_auto
          wp_apply wp_bag_send g2 ch2 _ (lsP H) $$ [$Hb2 $HP]
          itrivial
        try wp_auto
        wp_for_post
        iframe
        iexists done ++ [.lightSlowAck sa]
        isplitl [Hown]
        · iExactEq Hown; simp [sp.framesOf]
        ipureintro
        intro d hd
        rcases List.mem_append.1 hd with h' | h'
        · exact Hdone d h'
        · simp at h'; subst h'; exact Hcm
      · -- MReply
        rw [hM3]
        simp only [Option.getD_some, Option.isSome_some, _root_.decide_true]
        wp_auto
        ipersist p
        wp_apply wp_New_MReply o3 as %ob Hob
        wp_apply (MReply.Unmarshal.wp_proof ob _ rd srv cc H.γ H.γc H.γm H.cid done ov) $$
          [$Hpkg4 $Hpkg3 $Hrd $Hk $Hown $Hov $Hob] as %err ⟨%data, Hown, Hres⟩
        · ipureintro; exact ⟨Hovn, Hdone⟩
        icases Hres with (⟨%Hen, %r, %b, %x, %cs, %val, %csl, %vsl, ⟨%Hd, %Hh, %Hne⟩, Hob, Hcsl, Hvsl⟩ |
          ⟨%Hen, %v', -⟩)
        rotate_left
        · rcases err with e | _
          · wp_auto
            wp_for_post
            itrivial
          · exact absurd rfl Hen
        subst Hen Hd
        have hk : sp.cw.cKind (.reply r b x cs val) := ⟨Hh, Hne⟩
        icases sp.cw.rd_witness rd srv cc H.cid done (.reply r b x cs val) Hdone hk $$
          [$Hk Hown] with ⟨Hown, #Hw, %Hcm⟩
        · iExactEq Hown; simp [sp.Msg.frame, sp.Msg.code, sp.rpcTable]; rfl
        ipersist Hob
        ipersist Hcsl
        ipersist Hvsl
        ihave #HP : repP H (interface.mkOk (go.GoType.PointerType swift.MReply.ty) #ob) $$ []
        · unfold repP replyArg
          iexists x, ob
          isplitr
          · ipureintro; rfl
          iexists _, cs, val
          iframe Hob Hcsl Hvsl
          isplitr
          · ipureintro; exact ⟨rfl, Hcm.1, Hh⟩
          iExactEq Hw; rfl
        wp_auto
        wp_apply wp_fork
        · -- the message's goroutine: no wait (nil latency table), then the channel
          wp_auto
          have hbl : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z rpsl.len := by
            obtain ⟨h2, h3⟩ := Hll
            have : sint.nat rpsl.len = (sint.Z rpsl.len).toNat := rfl
            omega
          rw [ite_cond_eq_true _ _ (eq_true hbl)]
          obtain ⟨a, ha⟩ : ∃ a, l[k]? = some a := ⟨_, List.getElem?_eq_getElem (by omega)⟩
          wp_apply wp_load_slice_index rpsl (sint.Z (W64 (k : Int))) l DFrac.discard a (by omega) $$ [Hl] as -
          · iframe Hl; ipureintro; rw [hk64]; simpa using ha
          wp_apply replica.defs.LatencyTable.WaitDuration.wp_proofNil a
          wp_apply time.wp_Sleep
          ihave #Hp := p
          iStructNamed Hp
          wp_auto
          wp_apply wp_bag_send g3 ch3 _ (repP H) $$ [$Hb3 $HP]
          itrivial
        try wp_auto
        wp_for_post
        iframe
        iexists done ++ [.reply r b x cs val]
        isplitl [Hown]
        · iExactEq Hown; simp [sp.framesOf]
        ipureintro
        intro d hd
        rcases List.mem_append.1 hd with h' | h'
        · exact Hdone d h'
        · simp at h'; subst h'; exact Hcm
    try wp_auto
    wp_for_post
    iframe
    iexists k + 1, _, _
    iframe
    isplitl [i]
    · iExactEq i; congr 1; word
    ipureintro; omega
  · iapply HΦ; itrivial

end proof

end swift.rd

end Perennial.github_com.imdea_software.swiftpaxos
