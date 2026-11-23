/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/ReplyChan.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The reply channel (swift/replychan.go): `NewReplyChan`'s goroutine, `stop`, `reply`
(notes/prove-swift.md §12).

The goroutine of the epoch of ballot `b0` loops on a `select` over `exit` and `args`:
* `exit`: hands back on `ok` its reading right of `ballot` (or the cell's unused claim token)
  and `historySize`, and returns;
* `args`: the first message's `cellFilled` lets it claim its reading right; the leader's
  `MReply` (`optExec`, `Id == leader()`) is sent to the client with the witness the message
  carries (`replyOk`); the `MAccept` branch is dead (the `GPropose` has `Proxy = false`); the
  next history slot (`historySize % len(history)`, then `+ 1`) goes back on the descriptor's
  channel.

Hypotheses (open): `clientChecksum`'s spec and `MReply`'s `Marshal` (`marshalOk`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.LeaderM
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Deliver
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ReplyOk

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions]

/-- `clientChecksum(hs, dep)` (dpath.go): a fresh slice of `hs`'s hashes then the dependencies'
hash (`depHash`). -/
abbrev swift.clientChecksum.specR : Prop :=
  ∀ (hs dep : GoSlice) (Hs : List sp.Hash) (D : List swift.CommandId) (dqh dqd : DFrac),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      hs ↦*{dqh} Hs.map swift.handler.shashOf ∗ dep ↦*{dqd} D ∗
      ⌜sp.hashesWf Hs ∧ Hs.length + 1 < 2 ^ 62 ∧ D.length < 2 ^ 62⌝ }}
    (App (App (Val (@! swift.clientChecksum)) (Val #hs)) (Val #dep))
  {{ (out : GoSlice), RET #out; hs ↦*{dqh} Hs.map swift.handler.shashOf ∗ dep ↦*{dqd} D ∗
      ∃ d : sp.Hash, out ↦* (Hs ++ [d]).map swift.handler.shashOf ∗
        sp.depHash (D.map toCmdId) d ∗ ⌜d.length = 32⌝ }}

/-- `(*MReply).Marshal` (hypothesis, the swift messages' writers): an `*MReply` of the fields
of `.reply r b x cs v` writes its body, with its struct, its checksum slice and its value (read
only) as resources. -/
def swift.MReply.marshalH : Prop :=
  ∀ (l : Loc) (r b : w32) (x : swift.CommandId) (csl vsl : GoSlice) (cs : List sp.Hash)
    (v : List w8),
    sp.Msg.wf (.reply r b (toCmdId x) cs v) →
    ⊢ sp.marshalOk (interface.mkOk (go.GoType.PointerType swift.MReply.ty) #l)
        (.reply r b (toCmdId x) cs v)
        iprop(l ↦ swift.MReply.mk r b x csl vsl ∗ csl ↦* cs.map swift.handler.shashOf ∗
          vsl ↦*□ v)

instance swift.replyChanH_persistent (γ : sp.Names) (γc γm : GName) (rp : Loc)
    (γl : swift.CellNames) (b0 : w32) (rc : Loc) :
    Persistent (swift.replyChanH γ γc γm rp γl b0 rc) := by
  unfold swift.replyChanH; infer_instance

/-- What a descriptor gives `repchan.reply` for `x` (persistent), besides its fields: the
cell's witness, the replica's sending context, the proposal read-only (request SWC-1), its
hashes as the model's, its channel taking history slots, the value read-only, and the leader's
reply witness at the reply channel's ballot `b0` (`replyOk`). -/
def swift.replyCtx (γ : sp.Names) (γc γm : GName) (rp : Loc) (γl : swift.CellNames) (b0 : w32)
    (MP : GoInterface → IProp netDistGF) (dv : swift.DescV) (x : swift.CommandId) (v : GoSlice) :
    IProp netDistGF :=
  iprop(∃ (Hs : List sp.Hash) (vals : List w8) (rr s p w mu : Loc) (addr : GoString) (N : Nat)
      (me : w32) (γw : GName) (γs : ChanNames) (csv : swift.CommunicationSupply) (oe : Bool),
    swift.cellFilled γl ∗
    ⌜dv.Hs = Hs.map swift.handler.shashOf ∧ sp.hashesWf Hs ∧ Hs.length + 1 < 2 ^ 62 ∧
      dv.D.length < 2 ^ 62 ∧ vals.length < 2 ^ 62⌝ ∗ v ↦*□ vals ∗
    swift.fld rp go!"Replica" ↦□ rr ∗ replica.isReplica rr γ γc γm γw N me ∗
    swift.fld rp go!"sender" ↦□ s ∗ isChanBag γs s (replica.sendArgP rr γ γc γm N) ∗
    swift.fld rp go!"cs" ↦□ csv ∗ ⌜swift.csCodes csv⌝ ∗ swift.fld rp go!"optExec" ↦□ oe ∗
    dv.propose ↦□ replica.defs.GPropose.mk p w mu false addr ∗
    typedPointsto (p.[replica.defs.Propose, go!"ClientId"]) x.ClientId' DFrac.discard ∗
    □ (∀ n : w64, ⌜swift.slotIn n⌝ -∗ MP (interface.mkOk go.int #n)) ∗
    swift.replyOk γ γc γm N me b0 x dv.D Hs vals)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 1000000 in
instance swift.replyCtx_persistent (γ : sp.Names) (γc γm : GName) (rp : Loc)
    (γl : swift.CellNames) (b0 : w32) (MP : GoInterface → IProp netDistGF) (dv : swift.DescV)
    (x : swift.CommandId) (v : GoSlice) :
    Persistent (swift.replyCtx γ γc γm rp γl b0 MP dv x v) := by
  unfold swift.replyCtx; infer_instance

/-- `rc.reply(desc, cmdId, v)` on the reply channel of ballot `b0`: copies the descriptor's
dependencies and hashes and queues the arguments (the descriptor keeps its fields). The form
`deliver` needs is `swift.replyChan.reply.specI` (Deliver.lean): its `replyWit` must be turned
into `replyCtx` by the descriptor side (notes §12, OPEN). -/
abbrev swift.replyChan.reply.specR : Prop :=
  ∀ (γ : sp.Names) (γc γm : GName) (rp : Loc) (γl : swift.CellNames) (b0 : w32) (rc d : Loc)
    (γd : ChanNames) (MP : GoInterface → IProp netDistGF) (dv : swift.DescV) (x : swift.CommandId)
    (v : GoSlice),
  {{ swift.replyChanH γ γc γm rp γl b0 rc ∗ swift.descF d γd MP dv ∗
      swift.replyCtx γ γc γm rp γl b0 MP dv x v }}
    (App (App (App (Val (rc @!! go.GoType.PointerType swift.replyChan.ty @!! go!"reply"))
      (Val #d)) (Val #x)) (Val #v))
  {{ RET #(); swift.descF d γd MP dv }}

/-- `rc.stop()`: the goroutine's reading right (or the cell's claim token) and `historySize`
come back. -/
abbrev swift.replyChan.stop.specR : Prop :=
  ∀ (γ : sp.Names) (γc γm : GName) (rp : Loc) (γl : swift.CellNames) (b0 : w32) (rc : Loc),
  {{ swift.replyChanH γ γc γm rp γl b0 rc }}
    (App (Val (rc @!! go.GoType.PointerType swift.replyChan.ty @!! go!"stop")) (Val #()))
  {{ RET #(); swift.replyBack rp γl b0 }}

end specs

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [replica.Assumptions]

set_option goose.wp.extras true

/-- A receive clause on a bag channel (any element type). -/
theorem swift.bag_clauseT (t : go.GoType) {V : Type} [ZeroVal V]
    [TypedPointsto (GF := netDistGF) V] [IntoValTyped (GF := netDistGF) V t] [Pos.Countable V]
    (γ : ChanNames) (ch : Loc) (P : V → IProp netDistGF) (handler : Expr)
    (Ψ : val → IProp netDistGF) :
    ⊢ £ 1 -∗ £ 1 -∗ isChanBag γ ch P -∗
      (▷ ∀ v, P v -∗ WP (App handler (Val (PairV #v #true))) {{ Ψ }}) -∗
    chan.blockingClausePre (.CommClause (.RecvCase t (Val #ch)) handler) Ψ := by
  iintro Hlc1 Hlc2 #Hbag HP
  simp only [chan.blockingClausePre]
  iexists V, inferInstance, inferInstance, inferInstance, inferInstance, ch, γ
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply is_bag_is_chan $$ Hbag
  iapply bag_recv_au γ ch P _ $$ [$Hlc1 $Hlc2] Hbag
  iexact HP

instance swift.replyRes_timeless (rp : Loc) (b0 : w32) : Timeless (swift.replyRes rp b0) := by
  unfold swift.replyRes; infer_instance

instance swift.replyCellRes_timeless (rp : Loc) (b0 : w32) :
    Timeless (swift.replyCellRes rp b0) := by
  unfold swift.replyCellRes swift.replyRes; infer_instance

omit [SwiftNetPkgState netDistGF] [swift.Assumptions] [replica.Assumptions] in
theorem swift.srem_bounds (a b : w64) (ha : 0 ≤ sint.Z a) (hb : 0 < sint.Z b) :
    0 ≤ sint.Z (BitVec.srem a b) ∧ sint.Z (BitVec.srem a b) < sint.Z b := by
  show 0 ≤ (BitVec.srem a b).toInt ∧ (BitVec.srem a b).toInt < b.toInt
  replace ha : 0 ≤ a.toInt := ha
  replace hb : 0 < b.toInt := hb
  have hma : a.msb = false := by
    rw [BitVec.msb_eq_toInt]; simp; exact ha
  have hmb : b.msb = false := by
    rw [BitVec.msb_eq_toInt]; simp; omega
  rw [BitVec.srem_eq]; simp only [hma, hmb]
  have h2 : b.toInt = b.toNat := BitVec.toInt_eq_toNat_of_msb hmb
  have hlt : (a % b).toNat < b.toNat := by
    rw [BitVec.toNat_umod]; apply Nat.mod_lt; omega
  have hm : (a % b).msb = false := by
    rw [BitVec.msb_eq_decide]; simp
    have : b.toNat < 2^63 := by have := (BitVec.msb_eq_false_iff_two_mul_lt (x := b)).1 hmb; omega
    have : a.toNat % b.toNat < b.toNat := Nat.mod_lt _ (by omega)
    omega
  rw [BitVec.toInt_eq_toNat_of_msb hm]; omega

omit [SwiftNetPkgState netDistGF] [swift.Assumptions] [replica.Assumptions] in
theorem swift.slot_succ (s : w64) (h : 0 ≤ sint.Z s ∧ sint.Z s < 10010001) :
    0 ≤ sint.Z (s + W64 1) ∧ sint.Z (s + W64 1) ≤ 10010001 := by
  word

omit [SwiftNetPkgState netDistGF] [swift.Assumptions] [replica.Assumptions] in
theorem swift.snat_eq (x : w64) (h : 0 ≤ sint.Z x) : (sint.nat x : Int) = sint.Z x := by
  show ((sint.Z x).toNat : Int) = _; omega

/-- The goroutine's state between two messages. -/
def swift.replyLoopSt (rp : Loc) (γl : swift.CellNames) (b0 : w32) : IProp netDistGF :=
  swift.replyBack rp γl b0

omit [SwiftNetPkgState netDistGF] [replica.Assumptions] in
theorem swift.replyLoopSt_intro (rp : Loc) (γl : swift.CellNames) (b0 : w32) (n : w64)
    (h : 0 ≤ sint.Z n ∧ sint.Z n ≤ 10010001) :
    swift.fld rp go!"historySize" ↦ n ∗ swift.replyRes rp b0 ⊢ swift.replyLoopSt rp γl b0 := by
  iintro ⟨H1, H2⟩
  unfold swift.replyLoopSt swift.replyBack swift.replyCellRes
  ileft
  iframe H2
  iexists n
  iframe H1
  ipureintro; exact h

theorem swift.NewReplyChan.wp_proof (wp_cc : swift.clientChecksum.specR (hG := hG))
    (hmar : swift.MReply.marshalH (hG := hG))
    (wp_send : replica.Sender.SendToClient.spec (hG := hG))
    (wp_Leader : replica.Leader.spec) :
    swift.NewReplyChan.specI (hG := hG) := by
  intro rp rr hsl γ γc γm γl b0
  wp_start as ⟨#HReplica, #HShutdown, #Hhist, #Hcell, Hclaim, %Hn⟩
  wp_auto
  wp_apply chan.wp_make2 (V := Unit) (W64 1) as %ok %γok ⟨#Hok, %Hokcap, Hokown⟩
  · ipureintro; decide
  wp_apply chan.wp_make2 (V := Unit) (W64 2) as %ex %γex ⟨#Hex, %Hexcap, Hexown⟩
  · ipureintro; decide
  wp_apply chan.wp_make2 (V := Loc) (W64 2000000) as %ar %γa ⟨#Har, %Harcap, Harown⟩
  · ipureintro; decide
  try wp_auto
  ipersist rc
  ipersist r
  ipersist «$r0»
  iapply fupd_wp
  imod start_bag (fun _ : Unit => swift.replyBack rp γl b0) (ChanState.Buffered []) ok γok
    (by trivial) $$ [$Hok] [Hokown] with #Hbok
  · iexact Hokown
  imod start_bag (fun _ : Unit => iprop(True)) (ChanState.Buffered []) ex γex
    (by trivial) $$ [$Hex] [Hexown] with #Hbex
  · iexact Hexown
  imod start_bag (fun a : Loc => swift.replyArgP γ γc γm rp γl b0 a) (ChanState.Buffered []) ar γa
    (by trivial) $$ [$Har] [Harown] with #Hbar
  · iexact Harown
  imodintro
  wp_apply wp_fork $$ [Hclaim]
  · ihave #R2 := «$r0»
    iStructNamedPrefix R2 "RC"
    wp_auto_lc 2
    ihave HL : (swift.replyLoopSt rp γl b0 ∗ "Hlc1" ∷ £ 1 ∗ "Hlc2" ∷ £ 1 : IProp netDistGF)
      $$ [Hclaim Hlc1 Hlc2]
    · iframe; iunfold swift.replyLoopSt; iunfold swift.replyBack; iright; iexact Hclaim
    wp_for HL
    icases HL with ⟨HL, Hlc1, Hlc2⟩
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `exit`
      iapply swift.bag_clauseT $$ Hlc1 Hlc2 Hbex
      inext
      iintro %v -
      wp_auto
      iunfold swift.replyLoopSt at HL
      wp_apply wp_bag_send γok ok () (fun _ : Unit => swift.replyBack rp γl b0) $$ [$Hbok HL]
      · iexact HL
      wp_for_post
      itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `args`
      iapply swift.bag_clauseT $$ Hlc1 Hlc2 Hbar
      inext
      iintro %a Ha
      wp_auto_lc 2
      iunfold swift.replyArgP at Ha
      icases Ha with ⟨%ra, %D, %Hs, %vals, %γf, %F, %rr', %s, %p, %w, %mu, %addr, %N, %me, %γw,
        %γs, %csv, %oe, Ha, #Hfilled, Hdep, Hhs', #Hval, %Hwf, #HRep', #HisR, #Hsnd, #Hsbag, #Hcs,
        %Hcodes, #Hoe, #Hprop, #Hcid, #Hfin, #HF, #Hrok⟩
      icombine HReplica HRep' gives %Hrr
      subst Hrr
      iunfold swift.replyLoopSt at HL
      iunfold swift.replyBack at HL
      -- the reading right and `historySize`: claimed at the first message
      iapply fupd_wp
      ihave Hb : |={⊤}=> swift.replyCellRes rp b0 $$ [HL]
      · icases HL with (Hb | Hk)
        · imodintro; iexact Hb
        · imod swift.cell_claim swift.replyCellN ⊤ (by simp) γl (swift.replyCellRes rp b0)
            $$ [$Hcell $Hk $Hfilled] with >Hb
          imodintro; iexact Hb
      imod Hb
      iunfold swift.replyCellRes at Hb
      icases Hb with ⟨Hb, %n', Hhs, %Hn'⟩
      imodintro
      iStructNamedPrefix Ha "A"
      ihave #P2 := Hprop
      iStructNamedPrefix P2 "P"
      ihave #R2 := HisR
      iunfold replica.isReplica at R2
      icases R2 with ⟨%lg, %cfgp, %tbl, %pc, %fr, %nid, %ents, %γpc, %pwsl, %alsl, %latsl, %pws,
        %cwm, -, -, #HN, #HId, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, %HNp, -⟩
      have hN : 1 ≤ N ∧ N ≤ 7 := by
        obtain ⟨_, h1, h2, h3⟩ := HNp; refine ⟨?_, h3⟩; have := Int.lt_of_le_of_lt h1 h2; omega
      ihave #C2 := Hcs
      iStructNamedPrefix C2 "C"
      wp_auto
      cases oe
      · -- no `optExec`: no reply
        wp_auto
        have hl0 : ¬ sint.Z hsl.len = 0 := by rw [Hn]; decide
        isimp only [hl0, ↓reduceIte]
        wp_auto
        have hsb := swift.srem_bounds n' hsl.len Hn'.1 (by rw [Hn]; decide)
        have hslot : swift.slotIn (BitVec.srem n' hsl.len) := by
          unfold swift.slotIn; rw [Hn] at hsb; exact hsb
        ihave HFv : F (interface.mkOk go.int #(BitVec.srem n' hsl.len + W64 1 - W64 1)) $$ []
        · iapply HF; ipureintro
          rw [BitVec.add_sub_cancel]; exact hslot
        wp_apply wp_bag_send (t := go.InterfaceType []) γf ra.finish' _ F $$ [$Hfin $HFv]
        wp_for_post
        isplitl [Hhs Hb]
        · iapply swift.replyLoopSt_intro rp γl b0 _ (swift.slot_succ _ hslot)
          iframe Hhs; unfold swift.replyRes; iexact Hb
        iframe
      wp_auto
      iunfold swift.replyRes at Hb
      wp_apply swift.Replica.wp_leader wp_Leader rp rr b0 _ N hN $$ [$Hb $HReplica $HN] as Hb
      by_cases hld : me = BitVec.srem b0 (W32 (sint.Z (W64 (N : Int))))
      · isimp only [hld, _root_.decide_true]
        wp_auto
        wp_apply wp_cc ra.hs' ra.dep' Hs D (DFrac.own 1) (DFrac.own 1) $$ [$Hhs' $Hdep] as %csl ⟨Hhs', Hdep, %d, Hcsl, #Hdh, %Hd⟩
        · ipureintro; exact ⟨Hwf.1, Hwf.2.1, Hwf.2.2.1⟩
        wp_method_call
        wp_call
        wp_auto
        have hwf : sp.Msg.wf (.reply me b0 (toCmdId ra.cmdId') (Hs ++ [d]) vals) := by
          refine ⟨⟨?_, ?_⟩, Hwf.2.2.2⟩
          · simp; omega
          · intro h hh; simp at hh; rcases hh with hh | hh
            · exact Hwf.1.2 h hh
            · subst hh; exact Hd
        wp_apply wp_send rr γ γc γm γw N me γs s ra.cmdId'.ClientId'
          (interface.mkOk (go.GoType.PointerType swift.MReply.ty) #«$r0_ptr»)
          (.reply me b0 (toCmdId ra.cmdId') (Hs ++ [d]) vals) csv.replyRPC'
          iprop(«$r0_ptr» ↦ swift.MReply.mk me b0 ra.cmdId' csl ra.val' ∗
            csl ↦* (Hs ++ [d]).map swift.handler.shashOf ∗ ra.val' ↦*□ vals)
          $$ [$HisR $Hsbag «$r0» Hcsl]
        · unfold replica.toSend
          isplitl
          · isplitr
            · iapply (hmar «$r0_ptr» me b0 ra.cmdId' csl ra.val' (Hs ++ [d]) vals hwf)
            isplitl [«$r0» Hcsl]
            · iframe; iexact Hval
            isplitr
            · iunfold swift.replyOk at Hrok
              iapply Hrok
              · ipureintro; exact hld
              iexact Hdh
            isplitr
            · unfold replica.freeOk; ileft; ipureintro; rfl
            ipureintro
            refine ⟨hwf, ?_⟩
            rw [Hcodes.2.2.2.2.2.2.1]; rfl
          ipureintro
          simp [sp.Msg.isToClient, toCmdId]
        have hl0 : ¬ sint.Z hsl.len = 0 := by rw [Hn]; decide
        isimp only [hl0, ↓reduceIte]
        wp_auto
        have hsb := swift.srem_bounds n' hsl.len Hn'.1 (by rw [Hn]; decide)
        have hslot : swift.slotIn (BitVec.srem n' hsl.len) := by
          unfold swift.slotIn; rw [Hn] at hsb; exact hsb
        ihave HFv : F (interface.mkOk go.int #(BitVec.srem n' hsl.len + W64 1 - W64 1)) $$ []
        · iapply HF; ipureintro
          rw [BitVec.add_sub_cancel]; exact hslot
        wp_apply wp_bag_send (t := go.InterfaceType []) γf ra.finish' _ F $$ [$Hfin $HFv]
        wp_for_post
        isplitl [Hhs Hb]
        · iapply swift.replyLoopSt_intro rp γl b0 _ (swift.slot_succ _ hslot)
          iframe Hhs; unfold swift.replyRes; iexact Hb
        iframe

      · isimp only [hld, decide_false]
        wp_auto
        have hl0 : ¬ sint.Z hsl.len = 0 := by rw [Hn]; decide
        isimp only [hl0, ↓reduceIte]
        wp_auto
        have hsb := swift.srem_bounds n' hsl.len Hn'.1 (by rw [Hn]; decide)
        have hslot : swift.slotIn (BitVec.srem n' hsl.len) := by
          unfold swift.slotIn; rw [Hn] at hsb; exact hsb
        ihave HFv : F (interface.mkOk go.int #(BitVec.srem n' hsl.len + W64 1 - W64 1)) $$ []
        · iapply HF; ipureintro
          rw [BitVec.add_sub_cancel]; exact hslot
        wp_apply wp_bag_send (t := go.InterfaceType []) γf ra.finish' _ F $$ [$Hfin $HFv]
        wp_for_post
        isplitl [Hhs Hb]
        · iapply swift.replyLoopSt_intro rp γl b0 _ (swift.slot_succ _ hslot)
          iframe Hhs; unfold swift.replyRes; iexact Hb
        iframe
    iapply BigAndL.bigAndL_nil.2
    itrivial
  try wp_auto
  iapply HΦ
  unfold swift.replyChanH
  iexists «$v0_ptr», ok, ex, ar, γok, γex, γa
  isplitr
  · iexact «$r0»
  isplitr
  · iexact Hbar
  isplitr
  · iexact Hbex
  isplitr
  · iexact Hbok
  iexact Hcell

omit [SwiftNetPkgState netDistGF] [swift.Assumptions] [replica.Assumptions] in
theorem swift.copy_all {A : Type} (L : List A) (n : Nat) (z : A) (h : L.length = n) :
    List.take (List.replicate n z).length L ++ List.drop L.length (List.replicate n z) = L := by
  subst h; simp

theorem swift.replyChan.stop.wp_proof : swift.replyChan.stop.specR (hG := hG) := by
  intro γ γc γm rp γl b0 rc
  wp_start as Hrc
  unfold swift.replyChanH
  icases Hrc with ⟨%rep, %ok, %ex, %ar, %γok, %γex, %γa, #Hrc, #Har, #Hex, #Hok, #Hcell⟩
  ihave #R2 := Hrc
  iStructNamedPrefix R2 "RC"
  wp_auto
  wp_apply wp_bag_send (t := go.StructType []) γex ex () (fun _ : Unit => iprop(True)) $$ [$Hex]
  wp_apply wp_bag_receive (t := go.StructType []) γok ok (fun _ : Unit => swift.replyBack rp γl b0)
    $$ [$Hok] as %u Hb
  try wp_auto
  iapply HΦ
  iexact Hb

theorem swift.replyChan.reply.wp_proof : swift.replyChan.reply.specR (hG := hG) := by
  intro γ γc γm rp γl b0 rc d γd MP dv x v
  wp_start as ⟨#Hrc, Hd, #Hctx⟩
  ihave #Hctx2 := Hctx
  iunfold swift.replyCtx at Hctx2
  icases Hctx2 with ⟨%Hs, %vals, %rr, %s, %p, %w, %mu, %addr, %N, %me, %γw, %γs, %csv, %oe,
    #Hfilled, %Hpure, #Hval, #HRep, #HisR, #Hsnd, #Hsbag, #Hcs, %Hcodes, #Hoe, #Hprop, #Hcid, #HMP,
    #Hrok⟩
  ihave #Hrc2 := Hrc
  iunfold swift.replyChanH at Hrc2
  icases Hrc2 with ⟨%rep, %ok, %ex, %ar, %γok, %γex, %γa, #Hrcs, #Har, #Hex, #Hok, #Hcell⟩
  iStructNamedPrefix Hrcs "RC"
  iunfold swift.descF at Hd
  icases Hd with ⟨Hph, Hcmd, #Hvs, Hdep, #HD, Hhs, #HHs, Hprop', Hseq, Hmsgs, #Hmb, #Hsucc, %Hop⟩
  ihave %HDl := ownSlice_len _ _ _ $$ HD
  ihave %HHl := ownSlice_len _ _ _ $$ HHs
  try wp_auto
  wp_apply (wp_slice_make2 (V := swift.CommandId) dv.dep.len) as %dsl ⟨Hdsl, -⟩
  · ipureintro; exact HDl.2
  wp_apply (wp_slice_copy (V := swift.CommandId)) $$ [$Hdsl $HD] as %n1 ⟨%Hn1, Hdsl, -⟩
  try wp_auto
  wp_apply (wp_slice_make2 (V := swift.SHash) dv.hs.len) as %hsl ⟨Hhsl, -⟩
  · ipureintro; exact HHl.2
  try wp_auto
  wp_apply (wp_slice_copy (V := swift.SHash)) $$ [$Hhsl $HHs] as %n2 ⟨%Hn2, Hhsl, -⟩
  try wp_auto
  isimp only [swift.copy_all _ _ _ HDl.1] at Hdsl
  isimp only [swift.copy_all _ _ _ HHl.1] at Hhsl
  obtain ⟨hHs, hwf, hl1, hl2, hl3⟩ := Hpure
  isimp only [hHs] at Hhsl
  ihave HA : swift.replyArgP γ γc γm rp γl b0 «$v_ptr» $$ [«$v» Hdsl Hhsl]
  · iunfold swift.replyArgP
    iexists _, dv.D, Hs, vals, γd, MP, rr, s, p, w, mu, addr, N, me, γw, γs, csv, oe
    isplitl [«$v»]; · iexact «$v»
    isplitr; · iexact Hfilled
    isplitl [Hdsl]; · iexact Hdsl
    isplitl [Hhsl]; · iexact Hhsl
    isplitr; · iexact Hval
    isplitr; · ipureintro; exact ⟨hwf, hl1, hl2, hl3⟩
    isplitr; · iexact HRep
    isplitr; · iexact HisR
    isplitr; · iexact Hsnd
    isplitr; · iexact Hsbag
    isplitr; · iexact Hcs
    isplitr; · ipureintro; exact Hcodes
    isplitr; · iexact Hoe
    isplitr; · iexact Hprop
    isplitr; · iexact Hcid
    isplitr; · iexact Hmb
    isplitr; · iexact HMP
    iexact Hrok
  wp_apply wp_bag_send (t := go.GoType.PointerType swift.replyArgs.ty) γa ar «$v_ptr»
    (fun a : Loc => swift.replyArgP γ γc γm rp γl b0 a) $$ [$Har $HA]
  try wp_auto
  iapply HΦ
  unfold swift.descF
  iframe
  iframe Hvs HD HHs Hmb Hsucc
  ipureintro; exact Hop

/-- **`reply` on the reply-channel object** (SWC-2, round S1; `reply.specE`, ReplyDefs.lean):
`replyCtx` from `RCh` (the channel, its cell, the sending context), `deliver`'s replica facts, the
descriptor's `replyPre`, and `replyOk` from the execution witness (`swift.replyOk_of`). -/
theorem swift.replyChan.reply.wp_proofE : swift.replyChan.reply.specE (hG := hG) := by
  intro γ γc γm γl γw rp rr N me bw fr l oe rc d γd MP dv x v
  iintro %Φ ⟨#HRC, Hd, #HRep, #HisR, #Hoe, #Hinv, #Hcfg, %Hb, #Hwit, #Hpre, #HMP⟩ HΦ
  iunfold swift.RCh at HRC
  icases HRC with ⟨%γl', %rr', %s, %N', %γs, %csv, #Hrch, #Hfilled, #HRep', #HN', #Hsnd, #Hsbag,
    #Hcs, %Hcodes⟩
  icombine HRep HRep' gives %Hrr
  subst Hrr
  ihave #R2 := HisR
  iunfold replica.isReplica at R2
  icases R2 with ⟨%lg, %cfgp, %tbl, %pc, %fr', %nid, %ents, %γpc, %pwsl, %alsl, %latsl, %pws,
    %cwm, -, -, #HN, #HId, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, %HNp, -⟩
  icombine HN HN' gives %HNeq
  have hN : 1 ≤ N ∧ N ≤ 7 := by
    obtain ⟨_, h1, h2, h3⟩ := HNp; refine ⟨?_, h3⟩; have := Int.lt_of_le_of_lt h1 h2; omega
  have hNN : N' = N := by
    have h7 := Hcodes.2
    have : sint.Z (W64 (N : Int)) = sint.Z (W64 (N' : Int)) := by rw [HNeq]
    have e1 : sint.Z (W64 (N : Int)) = N := by word
    have e2 : sint.Z (W64 (N' : Int)) = N' := by word
    omega
  subst hNN
  iunfold swift.replyPre at Hpre
  icases Hpre with ⟨%Hs, %p, %w, %mu, %addr, #Hprop, #Hcid, %Hhs, #Hpaths⟩
  iapply fupd_wp
  imod (swift.replyOk_of γ γc γm γl N' fr l me bw x dv.D Hs v Hb.1 Hb.2 hN)
    $$ [Hinv Hcfg Hwit Hpaths] with ⟨%vals, #Hvals, %Hvl, #Hrok⟩
  · iframe Hinv Hcfg Hwit Hpaths
  imodintro
  iapply (swift.replyChan.reply.wp_proof γ γc γm rp γl' bw rc d γd MP dv x v) $$ [Hd] HΦ
  iframe Hrch Hd
  iunfold swift.replyCtx
  iexists Hs, vals, rr, s, p, w, mu, addr, N', me, γw, γs, csv, oe
  iframe Hfilled Hvals HRep HisR Hsnd Hsbag Hcs Hoe Hprop Hcid HMP Hrok
  ipureintro
  exact ⟨⟨Hhs.1, Hhs.2.1, Hhs.2.2.1, Hhs.2.2.2, Hvl⟩, Hcodes.1⟩

end proof

end Perennial.github_com.imdea_software.swiftpaxos
