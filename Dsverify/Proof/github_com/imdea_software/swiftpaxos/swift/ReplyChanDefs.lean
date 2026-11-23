/-
The definitions, specs and lemmas of `ReplyChan.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
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
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
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
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
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

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps] [swift.Assumptions] [replica.Assumptions] in
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

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps] [swift.Assumptions] [replica.Assumptions] in
theorem swift.slot_succ (s : w64) (h : 0 ≤ sint.Z s ∧ sint.Z s < 10010001) :
    0 ≤ sint.Z (s + W64 1) ∧ sint.Z (s + W64 1) ≤ 10010001 := by
  word

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps] [swift.Assumptions] [replica.Assumptions] in
theorem swift.snat_eq (x : w64) (h : 0 ≤ sint.Z x) : (sint.nat x : Int) = sint.Z x := by
  show ((sint.Z x).toNat : Int) = _; omega

/-- The goroutine's state between two messages. -/
def swift.replyLoopSt (rp : Loc) (γl : swift.CellNames) (b0 : w32) : IProp netDistGF :=
  swift.replyBack rp γl b0

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps] [replica.Assumptions] in
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

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps] [swift.Assumptions] [replica.Assumptions] in
theorem swift.copy_all {A : Type} (L : List A) (n : Nat) (z : A) (h : L.length = n) :
    List.take (List.replicate n z).length L ++ List.drop L.length (List.replicate n z) = L := by
  subst h; simp

end proof

end Perennial.github_com.imdea_software.swiftpaxos
