/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/client/HandlerState.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The client handler's Go-level state (`swift.Client`'s fields that `handleMsgs` owns), the part
the message sets' closures use (`core`, the `R` of `replica.mset`'s spec) and its context
(`ctxOk`, persistent). Notes: notes/prove-clientpkg.md, "The handler's design".

* `delivered` (keys `D`) mirrors the delivery tokens minted (`γd`'s authority, keys the
  sequence numbers): every delivered command is the client's, with a non-negative sequence
  number; so a command not delivered has no token yet.
* `reps[x][b]` holds a leader reply's result for `x` in ballot `b` (with the reply's witness);
  `γr` records the pairs `(x, b)` a leader entry of `x`'s message sets was built from
  (`repRec`, in `leaderP`): such a pair has its `reps` entry until `x` is delivered.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.HandlerInv
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.CmdKey

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.handler

/-- The handler's constants. -/
structure HC where
  γ : sp.Names
  γc : GName
  γm : GName
  γl : GName
  γd : GName
  γr : GName
  cid : w32
  N : Nat
  fr : Bool
  l : List GoString
  c : Loc
  b : Loc
  bv : client.BufferClient
  γch : ChanNames
  lg : Loc

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]

/-- The handler's context (persistent): the protocol's invariant and configuration, the reply
channel's protocol, the fields the handler only reads, the package-level variables it reads
(change log C6: `ReplyHook = nil`, the fast-ack pool off on the client node). -/
def ctxOk (H : HC) : IProp netDistGF :=
  iprop(sp.inv H.γ H.γc H.γm H.γl ∗ sp.cfg H.γc H.γm H.N H.fr H.l ∗ H.b ↦□ H.bv ∗
    isChanBag H.γch H.bv.Reply' (client.replyP H.γ H.cid H.γd) ∗
    structFieldRef swift.Client go!"BufferClient" H.c ↦□ H.b ∗
    structFieldRef client.Client go!"Logger" H.bv.Client' ↦□ H.lg ∗ dlog.quiet H.lg ∗
    structFieldRef swift.Client go!"n" H.c ↦□ (W64 H.N) ∗
    globalAddr swift.ReplyHook ↦□ func.nil ∗ globalAddr swift.useFastAckPool ↦□ false ∗
    ⌜1 ≤ H.N ∧ H.N < 2 ^ 31⌝)

instance ctxOk_persistent (H : HC) : Persistent (ctxOk H) := by unfold ctxOk; infer_instance

theorem ctxOk_N (H : HC) : ctxOk H ⊢ ⌜1 ≤ H.N ∧ H.N < 2 ^ 31⌝ := by
  unfold ctxOk
  iintro ⟨-, -, -, -, -, -, -, -, -, -, %HN⟩
  ipureintro; exact HN

/-- One command's reply results (`reps[x]`): each with a leader reply's witness. -/
def repsEntry (H : HC) (Gr : List (sp.CmdId × w32)) (x : swift.CommandId) (ir : GoMap) :
    IProp netDistGF :=
  iprop(∃ im : GMap w32 GoSlice, ir ↦$ im ∗
    ⌜∀ b, (cmdOf x, b) ∈ Gr → (im.lookup b).isSome⌝ ∗
    □ ∀ b vsl, ⌜im.lookup b = some vsl⌝ → ∃ v : List w8, vsl ↦*□ v ∗
      ∃ r cs, sp.msgOk H.γ H.γc H.γm (.reply r b (cmdOf x) cs v))

/-- The delivered commands and the tokens minted agree; delivered commands are the client's,
with non-negative sequence numbers; a recorded leader reply of a command not delivered has its
`reps` entry. -/
def coreOk (H : HC) (D : GMap swift.CommandId Unit) (Rm : GMap swift.CommandId GoMap)
    (Dn : GMap Nat Unit) (Gr : List (sp.CmdId × w32)) : Prop :=
  (∀ x, D.lookup x = some () → x.ClientId' = H.cid ∧ 0 ≤ x.SeqNum'.toInt) ∧
  (∀ n, (Dn.lookup n).isSome ↔ ∃ x, D.lookup x = some () ∧ x.SeqNum'.toNat = n) ∧
  (∀ x b, (cmdOf x, b) ∈ Gr → D.lookup x = none → (Rm.lookup x).isSome)

/-- **The closures' state** (`R` of the message sets): `delivered`, `reps`, `slowPaths`,
`alreadySlow`, the delivery tokens' and the reply records' authorities. -/
def core (H : HC) : IProp netDistGF :=
  iprop(∃ (dref rref aref : GoMap) (D : GMap swift.CommandId Unit)
      (Rm : GMap swift.CommandId GoMap) (Dn : GMap Nat Unit) (Gr : List (sp.CmdId × w32))
      (As : GMap swift.CommandId Unit) (spn : w64),
    structFieldRef swift.Client go!"delivered" H.c ↦ dref ∗ dref ↦$ D ∗
    structFieldRef swift.Client go!"reps" H.c ↦ rref ∗ rref ↦$ Rm ∗
    ([∗map] x ↦ ir ∈ Rm, repsEntry H Gr x ir) ∗
    structFieldRef swift.Client go!"slowPaths" H.c ↦ spn ∗
    structFieldRef swift.Client go!"alreadySlow" H.c ↦ aref ∗ aref ↦$ As ∗
    ghostMapAuth (K := Nat) (V := Unit) H.γd 1 Dn ∗
    monoListAuthOwn (A := sp.CmdId × w32) H.γr 1 Gr ∗
    ⌜coreOk H D Rm Dn Gr⌝)

/-- The quorums (both majorities of `N`, after `NewClient`'s `fixedMajority` step). -/
def quorumsOk (H : HC) : IProp netDistGF :=
  iprop(structFieldRef swift.Client go!"SQ" H.c ↦□
      interface.mkOk replica.Majority.ty #(W64 ((H.N / 2 + 1 : Nat) : Int)) ∗
    structFieldRef swift.Client go!"FQ" H.c ↦□
      interface.mkOk replica.Majority.ty #(W64 ((H.N / 2 + 1 : Nat) : Int)))

instance quorumsOk_persistent (H : HC) : Persistent (quorumsOk H) := by
  unfold quorumsOk; infer_instance

/-- One message set of command `x` (fast or slow) in the map: none yet, or a set. -/
def setOwn (H : HC) (fast : Bool) (x : swift.CommandId) (ms : Loc) : IProp netDistGF :=
  iprop(⌜ms = null⌝ ∨ replica.mset.own ms (H.N / 2 + 1) (entryP H.γ H.γc H.γm H.N H.cid fast (cmdOf x))
    accA (leaderP H.γ H.γc H.γm H.γr H.cid fast (cmdOf x)) (core H))

/-- The fast (`fastPathH`) or slow (`slowPathH`) message sets. -/
def pathsOwn (H : HC) (fast : Bool) (P : GMap swift.CommandId Loc → Prop) : IProp netDistGF :=
  iprop(∃ (pref : GoMap) (PM : GMap swift.CommandId Loc),
    structFieldRef swift.Client (if fast then go!"fastPathH" else go!"slowPathH") H.c ↦ pref ∗
    pref ↦$ PM ∗ ([∗map] x ↦ ms ∈ PM, setOwn H fast x ms) ∗ ⌜P PM⌝)

theorem pathsOwn_weaken (H : HC) (fast : Bool) (P : GMap swift.CommandId Loc → Prop) :
    pathsOwn H fast P ⊢ pathsOwn H fast (fun _ => True) := by
  unfold pathsOwn
  iintro ⟨%p, %PM, H1, H2, H3, -⟩
  iexists p, PM; iframe

/-- `x` has a (non-nil) message set. -/
def hasSet (x : swift.CommandId) (PM : GMap swift.CommandId Loc) : Prop :=
  ∃ ms, PM.lookup x = some ms ∧ ms ≠ null

/-- A non-leader ack as handed to `handleFastAck`/`MsgSet.Add` before its leader check (N4):
`entryP` without `rid k ≠ leaderOf`, with the wire values' signs. -/
def entryW (H : HC) (fast : Bool) (x : sp.CmdId) (k : w32) (m : GoInterface) : IProp netDistGF :=
  iprop(∃ (fa : swift.MFastAck) (hs : List sp.Hash), ackObj m fa hs ∗
    ⌜fa.Replica' = k ∧ cmdOf fa.CmdId' = x ∧ x.cl = H.cid ∧ fa.Dep' = slice.nil ∧
      sp.wireOk k fa.Ballot'⌝ ∗
    ((⌜fast = true⌝ ∗ sp.msgOk H.γ H.γc H.γm (.fastAckClient k fa.Ballot' x hs)) ∨
      (⌜hs = []⌝ ∗ sp.msgOk H.γ H.γc H.γm (.lightSlowAck ⟨k, fa.Ballot', x⟩))))

instance entryW_persistent H fast x k m : Persistent (entryW H fast x k m) := by
  unfold entryW; haveI := sp.msgOk_persistent (γ := H.γ) (γc := H.γc) (γm := H.γm); infer_instance

theorem entryW_entryP (H : HC) (fast : Bool) (x : sp.CmdId) (k : w32) (m : GoInterface)
    (fa : swift.MFastAck) (hs : List sp.Hash) :
    entryW H fast x k m ∗ ackObj m fa hs ∗ ⌜sp.rid k ≠ sp.leaderOf H.N (sp.bal fa.Ballot')⌝ ⊢
      entryP H.γ H.γc H.γm H.N H.cid fast x k m := by
  haveI := sp.msgOk_persistent (γ := H.γ) (γc := H.γc) (γm := H.γm)
  unfold entryW entryP
  iintro ⟨⟨%fa', %hs', #Ho', ⟨%H1, %H2, %H3, %H4, -⟩, #Hw⟩, #Ho, %Hnl⟩
  ihave %Hag := ackObj_agree m fa fa' hs hs' $$ [Ho Ho']
  · iframe #
  obtain ⟨rfl, rfl⟩ := Hag
  iexists fa, hs
  iframe #
  ipureintro; exact ⟨H1, H2, H3, H4, Hnl⟩

/-- The handler's whole state (its goroutine owns it): `core`, both kinds of message sets, the
highest ballot seen. -/
def hst (H : HC) : IProp netDistGF :=
  iprop(core H ∗ pathsOwn H true (fun _ => True) ∗ pathsOwn H false (fun _ => True) ∗
    ∃ bal : w32, structFieldRef swift.Client go!"ballot" H.c ↦ bal)

/-- `hasSet` decided. -/
def hasSetB (x : swift.CommandId) (PM : GMap swift.CommandId Loc) : Bool :=
  match PM.lookup x with
  | some ms => !Decidable.decide (ms = null)
  | none => false

theorem hasSetB_iff (x : swift.CommandId) (PM : GMap swift.CommandId Loc) :
    hasSetB x PM = true ↔ hasSet x PM := by
  unfold hasSetB hasSet
  cases PM.lookup x <;> simp

end defs

section laws
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]

/-- A decided command's sequence number is non-negative: the law `sp.doneRes_seq_nonneg`
(change log C8, HUB-REQUEST 9). The handler needs it to mint the delivery token of `x.seq` and
for `RegisterReply`. -/
theorem doneRes_seq_nonneg (γ : sp.Names) (γc γm γl : GName) (E : CoPset) (hE : ↑sp.spN ⊆ E)
    (x : sp.CmdId) (o : List w8) :
    sp.inv γ γc γm γl ∗ sp.doneRes γ x o ⊢ |={E}=> ⌜0 ≤ x.seq.toInt⌝ :=
  sp.doneRes_seq_nonneg E hE x o

/-- Inserting over a key (its old entry dropped). -/
theorem bigSepM_insert_over {K V : Type} [DecidableEq K] (Φ : K → V → IProp netDistGF)
    (m : GMap K V) (k : K) (v : V) :
    Φ k v ∗ ([∗map] k' ↦ v' ∈ m, Φ k' v') ⊢ [∗map] k' ↦ v' ∈ (<[k := v]> m), Φ k' v' := by
  iintro ⟨Hk, Hm⟩
  iapply (BigSepM.bigSepM_insert_delete (Φ := Φ) (m := m) (i := k) (x := v)).2
  iframe Hk
  cases h : m !! k with
  | none =>
    have : Iris.Std.PartialMap.delete m k = m := GMap.delete_notin m k h
    rw [this]; iexact Hm
  | some w =>
    ihave ⟨-, Hm⟩ := (BigSepM.bigSepM_delete (Φ := Φ) (m := m) (i := k) (x := w) h).1 $$ Hm
    iexact Hm

theorem cmdOf_inj : Function.Injective cmdOf := by
  intro a b h
  cases a; cases b
  simp only [cmdOf, sp.CmdId.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h; rfl

/-- A `reps` entry of another command survives a new record of `x`'s. -/
theorem repsEntry_grow (H : HC) (Gr : List (sp.CmdId × w32)) (x y : swift.CommandId) (b : w32)
    (ir : GoMap) (hxy : y ≠ x) :
    repsEntry H Gr y ir ⊢ repsEntry H (Gr ++ [(cmdOf x, b)]) y ir := by
  unfold repsEntry
  iintro ⟨%im, Him, %Hb, #Hv⟩
  iexists im
  iframe Him Hv
  ipureintro
  intro b' hb'
  rcases List.mem_append.mp hb' with h | h
  · exact Hb b' h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    exact absurd (cmdOf_inj h.1) hxy


end laws

end swift.handler

end Perennial.github_com.imdea_software.swiftpaxos
