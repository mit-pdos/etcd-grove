/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/Defs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The replica's internal predicates (`replica/replica.go`; the replica group's, not frozen).

* Writers (`WrKind`, `wrAt`, `wrSt`): a `*bufio.Writer` over one end of a connection to a peer
  (dialed: the stream `inP`, after this replica's hello; accepted: `outQ`) or to client `cl`
  (accepted: `outQ`, replies of `cl`'s commands): while it has no sticky error, what it sent and
  buffers is the head and whole frames of the kind's messages, each with its witness.
* `proposeP`: what the replica's `ProposeChan` carries: a `*GPropose` (not a proxy's) of a
  proposal the client registered (`cmdIs`), read-only (D16: nobody writes a `GPropose` or its
  `Propose` once sent; the run loop and the descriptors share it); its value slice read-only
  (`↦*□`, SWB-1: the state machine keeps a put's value slice, aliased, from its first execution
  on).
* The message table (`unmarshalOk`, `newOk`, `entryOk`, `tableOk`): every registered id `c`
  has an object whose `New()` gives fresh objects whose `Unmarshal`, on a `*bufio.Reader` whose
  next bytes are of a well-formed message of type `c` (`streamLaw … (nextOk c)`: the generated
  `Unmarshal`s need `ReadByte` and, for their `make`s, counts that are the frame's own),
  decodes a message of type `c` (`sp.decodes`) into the registrant's representation `Rep`, and
  a channel carrying such
  objects with their message's witness; every peer message's type other than the beacons' is
  registered (else a reader would lose the stream's alignment).
* `lockInv`: what `r.M` protects: `Alive`, `Latencies`, the peers' writers' states, the
  clients' writers map and every client writer registered so far (ghost map `γw`: writer ↦
  its client's id).
* `isReplica`: the persistent facts every method uses: read-only fields, the quiet logger, the
  plain configuration, the table, the channels, the mutex.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.Stream
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.rpc.Table
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Defs
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.config.Defs
public import Perennial.Proof.sync
public import Perennial.Golang.Theory.Chan.Idioms.Bag

-- PORT: lab imports dropped: Harness.Proof.bufio.ReadFull

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace sp

/-- What a replica's writer writes (see the file header). -/
inductive WrKind where
  | peerOut (me : w32)
  | peerIn
  | client (cl : w32)

def WrKind.conn : WrKind → ConnKind
  | .client cl => .client cl
  | _ => .peer

def WrKind.head : WrKind → List w8
  | .peerOut me => helloBytes me
  | _ => []

def WrKind.ok : WrKind → Msg → Prop
  | .client cl => Msg.isToClient cl
  | _ => Msg.isPeer

/-- The end a writer of kind `k` writes (the dialer's: `false`). -/
def WrKind.side : WrKind → Bool
  | .peerOut _ => false
  | _ => true

/-- The peer `i`'s writer kind at replica `me`: dialed when `i < me`. -/
def peerWrKind (me : w32) (i : Nat) : WrKind :=
  if (i : Int) < me.toInt then .peerOut me else .peerIn

end sp

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

namespace sp

def WrKind.proto (γ : Names) (γc γm : GName) : WrKind → Proto netDistGF
  | .peerOut _ => inP γ γc γm
  | _ => outQ γ γc γm

/-- The bytes `W` are the kind's head and whole frames of its messages, with their witnesses
(persistent). -/
def wrAt (γ : Names) (γc γm : GName) (k : WrKind) (W : List w8) : IProp netDistGF :=
  iprop(∃ ms : List Msg, ⌜W = k.head ++ framesOf ms ∧ ∀ m ∈ ms, k.ok m ∧ m.wf⌝ ∗
    [∗list] m ∈ ms, msgOk γ γc γm m)

instance wrAt_persistent (γ : Names) (γc γm : GName) (k : WrKind) (W : List w8) :
    Persistent (wrAt γ γc γm k W) := by
  unfold wrAt; infer_instance

/-- The writer `w` of kind `k` (see the file header). -/
def wrSt (γ : Names) (γc γm : GName) (w : Loc) (k : WrKind) : IProp netDistGF :=
  iprop(∃ (cv : GoInterface) (cid : Nat) (sent pend : List w8) (err : GoInterface),
    net.rpc.connIface cv cid k.side ∗ connKind γ cid k.conn ∗
    bufio.writerOk cv (sendTok cid k.side (k.proto γ γc γm)) (k.proto γ γc γm cid) ∗
    bufio.ownWriter w cv (sendTok cid k.side (k.proto γ γc γm)) (k.proto γ γc γm cid)
      sent pend err ∗
    (⌜err ≠ interface.nil⌝ ∨ wrAt γ γc γm k (sent ++ pend)))

/-- What `ProposeChan` carries (see the file header). -/
def proposeP (γ : Names) (gp : Loc) : IProp netDistGF :=
  iprop(∃ (p w mu : Loc) (addr : GoString) (seq cl : w32) (c : Cmd) (ts : w64) (vs : GoSlice),
    gp ↦□ replica.defs.GPropose.mk p w mu false addr ∗
    p ↦□ replica.defs.Propose.mk seq cl (state.Command.mk c.op c.key vs) ts ∗ vs ↦*□ c.val ∗
    cmdIs γ ⟨cl, seq⟩ c ∗ ⌜c.wf⌝)

instance proposeP_persistent (γ : Names) (gp : Loc) : Persistent (proposeP γ gp) := by
  unfold proposeP; infer_instance

/-- After a type byte `c`, the bytes `d` a peer stream delivers are a prefix of the body of a
well-formed peer message of type `c` (then more). (No such message has the type of the five
registered types the deployment never sends, `MSlowAck`, `MPing`, `MPingRep`, `MCollect`,
`MAccept`, nor of the client messages `MFastAckClient`, `MReply`.) -/
def nextOk (c : w8) (d : List w8) : Prop :=
  ∃ (m : Msg) (w : List w8), m.wf ∧ m.isPeer ∧ m.code = c ∧ d <+: m.body ++ w

/-- The stream law of the `*bufio.Reader` `br` (over `rd`, `I`) after it returned `R`: what it
returns next satisfies `L`, a step later (persistent). -/
def streamLaw (br : Loc) (rd : GoInterface) (I : List w8 → IProp netDistGF) (R : List w8)
    (L : List w8 → Prop) : IProp netDistGF :=
  iprop(□ ∀ d : List w8, bufio.ownReader br rd I (R ++ d) -∗
    bufio.ownReader br rd I (R ++ d) ∗ ▷ ⌜L d⌝)

instance streamLaw_persistent (br : Loc) (rd : GoInterface) (I : List w8 → IProp netDistGF)
    (R : List w8) (L : List w8 → Prop) : Persistent (streamLaw br rd I R L) := by
  unfold streamLaw; infer_instance

/-- A fresh object `o` of a registered type: its `Unmarshal(br)` on a `*bufio.Reader` `br` that
returned `R` (up to the type byte `c`), whose next bytes are of a well-formed message of type
`c` (`streamLaw … (nextOk c)`), reads the next bytes `data`; without an error they decode to
a message of type `c`, which `o` then represents (`Rep o m`). -/
def unmarshalOk (c : w8) (Rep : GoInterface → Msg → IProp netDistGF) (o : GoInterface) :
    IProp netDistGF :=
  iprop(∃ e : GoInterfaceOk, ⌜o = interface.ok e⌝ ∗
    ∀ (br : Loc) (rd : GoInterface) (I : List w8 → IProp netDistGF) (R : List w8)
      (Φ : val → IProp netDistGF),
      bufio.readerOk rd I -∗ streamLaw br rd I R (nextOk c) -∗ bufio.ownReader br rd I R -∗
      ▷ (∀ (err : GoInterface) (data : List w8), bufio.ownReader br rd I (R ++ data) -∗
          ((⌜err = interface.nil⌝ ∗ ∃ m, ⌜decodes c data m⌝ ∗ Rep o m) ∨
            ⌜err ≠ interface.nil⌝) -∗ Φ #err) -∗
      WP (App (Val #(methods e.ty go!"Unmarshal" e.v))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br))) {{ Φ }})

/-- The registered object `obj`: its `New()` returns fresh objects (persistent). -/
def newOk (c : w8) (Rep : GoInterface → Msg → IProp netDistGF) (obj : GoInterface) :
    IProp netDistGF :=
  iprop(∃ e : GoInterfaceOk, ⌜obj = interface.ok e⌝ ∗
    □ ∀ (Φ : val → IProp netDistGF),
      ▷ (∀ o : GoInterface, unmarshalOk c Rep o -∗ Φ #o) -∗
      WP (App (Val #(methods e.ty go!"New" e.v)) (Val #())) {{ Φ }})

instance newOk_persistent (c : w8) (Rep : GoInterface → Msg → IProp netDistGF)
    (obj : GoInterface) : Persistent (newOk c Rep obj) := by
  unfold newOk; infer_instance

/-- What the channel of type `c` carries: objects representing messages of type `c`, with
their witnesses. -/
def chanMsgP (γ : Names) (γc γm : GName) (c : w8) (Rep : GoInterface → Msg → IProp netDistGF)
    (o : GoInterface) : IProp netDistGF :=
  iprop(∃ m : Msg, Rep o m ∗ msgOk γ γc γm m ∗ ⌜m.code = c⌝)

/-- The table's entry of type `c` (persistent). -/
def entryOk (γ : Names) (γc γm : GName) (c : w8) (p : rpc.Pair') : IProp netDistGF :=
  iprop(∃ (Rep : GoInterface → Msg → IProp netDistGF) (γch : ChanNames),
    newOk c Rep p.Obj' ∗ isChanBag γch p.Chan' (chanMsgP γ γc γm c Rep))

instance entryOk_persistent (γ : Names) (γc γm : GName) (c : w8) (p : rpc.Pair') :
    Persistent (entryOk γ γc γm c p) := by
  unfold entryOk; infer_instance

/-- The table's entries (see the file header). -/
def tableOk (γ : Names) (γc γm : GName) (ents : GMap w8 rpc.Pair') : IProp netDistGF :=
  iprop(⌜∀ m : Msg, m.isPeer → m.code ≠ W8 6 → m.code ≠ W8 7 → (ents !! m.code).isSome⌝ ∗
    □ ∀ (c : w8) (p : rpc.Pair'), ⌜ents !! c = some p⌝ -∗ entryOk γ γc γm c p)

instance tableOk_persistent (γ : Names) (γc γm : GName) (ents : GMap w8 rpc.Pair') :
    Persistent (tableOk γ γc γm ents) := by
  unfold tableOk; infer_instance

end sp

/-- Field `f` of the replica at `r`. -/
abbrev replica.fld (r : Loc) (f : GoString) : Loc := structFieldRef replica.Replica f r

/-- The client writers registered so far (each with its client's id, ghost map `γw`) and the
clients' writers map (`id ↦ w` for a registered `w` of client `id`). -/
def replica.clientWrs (γ : sp.Names) (γc γm : GName) (γw : GName) (cwm : GoMap) :
    IProp netDistGF :=
  iprop(∃ (cw : GMap w32 Loc) (ws : GMap Loc w32),
    cwm ↦$ cw ∗ ghostMapAuth γw 1 ws ∗
    ⌜∀ id w, cw !! id = some w → ws !! w = some id⌝ ∗
    ([∗map] w ↦ cl ∈ ws, sp.wrSt γ γc γm w (.client cl)))

/-- What `r.M` protects (see the file header). -/
def replica.lockInv (γ : sp.Names) (γc γm : GName) (γw : GName) (me : w32) (N : Nat)
    (pws : List Loc) (alsl latsl : GoSlice) (cwm : GoMap) : IProp netDistGF :=
  iprop(∃ (alive : List Bool) (lats : List w64),
    alsl ↦* alive ∗ latsl ↦* lats ∗ ⌜alive.length = N ∧ lats.length = N⌝ ∗
    ([∗list] i ↦ w ∈ pws, ⌜w = null⌝ ∨ sp.wrSt γ γc γm w (sp.peerWrKind me i)) ∗
    replica.clientWrs γ γc γm γw cwm)

/-- The replica's fixed fields and slots (persistent; see the file header): `N` replicas, this
one `me`, the logger `lg`, the configuration `cfgp`, the table `tbl`, the channels, the peers'
writers `pws` (fixed once the connections are made), the slices `Alive`, `Latencies`. -/
def replica.isReplica (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me : w32)
    : IProp netDistGF :=
  iprop(∃ (lg cfgp tbl pc : Loc) (fr : Bool) (nid : w8) (ents : GMap w8 rpc.Pair')
      (γpc : ChanNames) (pwsl alsl latsl : GoSlice) (pws : List Loc) (cwm : GoMap),
    replica.fld r go!"Logger" ↦□ lg ∗ dlog.quiet lg ∗
    replica.fld r go!"N" ↦□ (W64 N) ∗ replica.fld r go!"Id" ↦□ me ∗
    replica.fld r go!"Config" ↦□ cfgp ∗ config.plain cfgp fr ∗
    replica.fld r go!"RPC" ↦□ tbl ∗ rpc.isTable tbl DFrac.discard nid ents ∗
    sp.tableOk γ γc γm ents ∗
    replica.fld r go!"ProposeChan" ↦□ pc ∗ isChanBag γpc pc (sp.proposeP γ) ∗
    replica.fld r go!"Shutdown" ↦□ false ∗ replica.fld r go!"LRead" ↦□ false ∗
    replica.fld r go!"Dt" ↦□ null ∗
    replica.fld r go!"PeerWriters" ↦□ pwsl ∗ pwsl ↦*□ pws ∗
    replica.fld r go!"Alive" ↦□ alsl ∗ replica.fld r go!"Latencies" ↦□ latsl ∗
    replica.fld r go!"ClientWriters" ↦□ cwm ∗
    ⌜pws.length = N ∧ 0 ≤ me.toInt ∧ me.toInt < N ∧ N ≤ 7⌝ ∗
    sync.isMutex (replica.fld r go!"M") (replica.lockInv γ γc γm γw me N pws alsl latsl cwm))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 1000000 in
instance replica.isReplica_persistent (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat)
    (me : w32) : Persistent (replica.isReplica r γ γc γm γw N me) := by
  unfold replica.isReplica; infer_instance

end defs

end Perennial.github_com.imdea_software.swiftpaxos
