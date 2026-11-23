/-
**Per-address protocols over the net extension** (proved, not trusted): the vocabulary
dsverify-lab's network kits reason in (its `NetConn` ghost vocabulary, `old/dsverify/harness/lean/Harness/
GooseLang/Ext/NetConn/Specs.lean`), as predicates over the extension's ghost state (`netEnd`,
`netDir`, `netPend`, `netLis`, `Ghost.lean`), with **laws**: for each `net` operation,
the update its one canonical spec (`Net/Spec/net/`) takes, built from the vocabulary, and what the
caller has after it. A kit proof calls the canonical spec and applies a law; there is no second
spec of a `net` function (`notes/dsverify-net-port-plan.md`, phase 4; `notes/decisions.md`, "The
kits' network vocabulary: a library of laws").

The vocabulary (`[π : NetProtoGS]`, the library's global ghost names, made once by
`netProto_alloc`):

* `Proto GF := Nat → List w8 → IProp GF`: what the bytes of one direction of the connection `cn`
  mean; `protoPrefix P cn W`: `W` is empty or a prefix of some `ext` with `□ P cn ext`.
* `addrTok a` (persistent): `a` is a valid address (`addrOk`, D20); what `Listen`, `Dial` and
  `Accept` need (`addrTok_ok`). `addrUnset a` (exclusive): `a`'s
  pending set, empty, its protocols not set; `addr_set_proto` (`addrs_set_proto`, every address of
  a list) sets them once: `addrProto a P Q` (persistent), `P` for what dialers write, `Q` for what
  acceptors write. Both from the extension's start resources (`addrs_start`).
* For the end `s` of `cn` (`false` the dialer's): `sendTok cn s P W` (the writer of the direction
  from `s`: it has written `W`, which meets `P` up to extension), `recvTok cn s P R` (the reader of
  the direction towards `s`: it has read `R`, which was written and meets `P` up to extension:
  `recvTok_proto`, `recvTok_sentLb`), `connEnd cn s Pout Pin W R` (both), `sentLb cn s W`
  (persistent: the direction from `s` was written at least `W`), `connFresh cn s` (exclusive, once
  per end: `connFresh_excl`), `connIs cn` (persistent: the connection is the library's; what
  `Close`, `CloseWrite`, the deadlines and the socket options need).
* `recvTokL cn s P R`: `recvTok` with its protocol fact one step later (`▷ protoPrefix`), what a
  `Read` gives (`read_au`): the fact comes out of an invariant. A later credit or any program step
  turns it back into `recvTok` (`recvTokL_elim`, `recvTokL_later`).
* `lisInv l a` (persistent): this node's listener `l` at `a`, shared between threads (the lab's
  persistent listener), for `accept_shared_au` and `lisClose_au`.
* D21, a listener at `la`, a wildcard (`":p"`, `"0.0.0.0:p"`, `"[::]:p"`) or a valid address:
  `lisUnset la` (exclusive), every valid address `la` takes (`lisAccepts`: every valid address with
  the port `p` for a wildcard) unset, from the start resources (`addrs_lis_start`, beside a list of
  single addresses); `lis_set_proto` sets one pair of protocols for all of them: `lisProto la P Q`
  (persistent), which gives each address's `addrProto a P Q` (`lisProto_addr`: a dialer dials any
  of them, `dial_au`) and the right to listen at `la` (`listen_lis_au`). In the model a wildcard
  listener takes a connection dialed to any valid address with its port (on any machine, D21:
  more than Linux, where it takes only its machine's), so its acceptor learns the protocols of the
  address the connection was dialed to, not that it was one of its machine's.

The laws: `dial_au` (`net.Dial.spec` and `net.DialTimeout.spec`'s update: the dialer's end and
tokens, the acceptor's deposited at the address), `accept_au` and `accept_shared_au`
(`Listener.Accept.spec_addrOk`, the canonical spec at a valid address: the acceptor's end and
tokens), `accept_lis_au` and `accept_lis_shared_au` (`Listener.Accept.spec`, for a wildcard
listener or any other: the same, for the address the connection was dialed to), `listen_au` and
`listen_lis_au` (`net.Listen.spec_addrOk`, `net.Listen.spec`), `write_acc` with `writeP`
(`Conn.Write.spec`'s writer predicate and accessor: each step's bytes extend `sendTok`, the whole
write meeting the protocol), `read_au` (`Conn.Read.spec`), `close_au`, `closeWrite_au`,
`deadline_au`, `sockopt_au`, `lisClose_au`.

**How it is built.** The connections' states are in one invariant (`regInv`, timeless): for each
connection `cn` the library knows, with its ghost names `γ` (a persistent entry `connElem cn γ`),
both ends' states (`netEnd`) and both directions' (`netDir`), with what each direction's writer
wrote (`W`, a monotone list: a half with the writer, a quarter here, a quarter at the address)
and its reader read (`R`), agreeing (`DirOk`, `Stream.lean`). The protocols are in each address's
invariant (`addrInvP a γa P Q`, allocated by `addr_set_proto`, with the protocols as its
statement's parameters, not saved predicates: a reader gets its protocol fact one later after the
write, not two), with the address's pending set (`netPend`), the deposits of the connections
pending there (the acceptor's tokens, timeless) and, for each connection dialed to it, its
directions' protocol facts. A new connection's entry needs its number fresh in the registry: an
entry holds the connection's directions, and a dial has their fresh resources (`netDir_excl`).

**What differs from the lab's.** Errors are the semantics' kinds (`closed | timeout | sys`, EOF a
read result: `ReadOutcome`), not the lab's codes; a `Write` is a loop of steps (D15), each one an
update `write_acc` builds, and `sendTok`'s exclusivity is what keeps the bytes contiguous in the
ghost state (Go's write lock, D25, is not needed for it: no kit writes on one end from two threads
without a lock, `notes/dsverify-net-port-plan.md`, phase 0); `addrTok` is persistent (`Listen` of
an address in use fails with a `sys` error here, instead of needing the token); a `Read`'s protocol fact is one step later
(`recvTokL`); an accepted connection may be one a failed dial abandoned (D16; its tokens are
deposited all the same, and its reader sees an empty, shut direction).
-/
module

public import GooseLang.Ext.Net.Stream
public import GooseLang.Ext.Net.Deploy
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.Token

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace Net

/-! ## Protocols -/

/-- A protocol: what the bytes of one direction of the connection `cn` mean. -/
abbrev Proto (GF : BundledGFunctors) := Nat → List w8 → IProp GF

section protos
variable {GF : BundledGFunctors}

/-- `W` is empty or a prefix of a sequence `ext` with `□ P cn ext`. -/
def protoPrefix (P : Proto GF) (cn : Nat) (W : List w8) : IProp GF :=
  iprop(⌜W = []⌝ ∨ ∃ ext, ⌜W <+: ext⌝ ∗ □ P cn ext)

instance protoPrefix_persistent (P : Proto GF) (cn : Nat) (W : List w8) :
    Persistent (protoPrefix P cn W) := by
  unfold protoPrefix; infer_instance

theorem protoPrefix_nil (P : Proto GF) (cn : Nat) : ⊢ protoPrefix P cn [] := by
  unfold protoPrefix; ileft; ipureintro; rfl

/-- A prefix of what meets a protocol up to extension meets it up to extension. -/
theorem protoPrefix_le {P : Proto GF} {cn : Nat} {W W' : List w8} (h : W' <+: W) :
    protoPrefix P cn W ⊢ protoPrefix P cn W' := by
  unfold protoPrefix
  iintro (%hW | ⟨%ext, %hext, #HP⟩)
  · ileft; ipureintro; subst hW; exact List.prefix_nil.mp h
  · iright; iexists ext; iframe HP; ipureintro; exact h.trans hext

theorem protoPrefix_of {P : Proto GF} {cn : Nat} {W ext : List w8} (h : W <+: ext) :
    □ P cn ext ⊢ protoPrefix P cn W := by
  unfold protoPrefix
  iintro #HP
  iright; iexists ext; iframe HP; ipureintro; exact h

/-- A protocol that holds of the empty stream and is closed under prefixes. -/
structure ProtoPrefixClosed (P : Proto GF) : Prop where
  nil : ∀ cn, ⊢ □ P cn []
  pre : ∀ cn (a b : List w8), a <+: b → □ P cn b ⊢ □ P cn a

/-- A pure protocol `p`, true of the empty stream and closed under prefixes. -/
theorem ProtoPrefixClosed.of_pure (p : Nat → List w8 → Prop) (hnil : ∀ cn, p cn [])
    (hpre : ∀ cn a b, a <+: b → p cn b → p cn a) :
    ProtoPrefixClosed (GF := GF) (fun cn bs => iprop(⌜p cn bs⌝)) where
  nil cn := by iintro !>; ipureintro; exact hnil cn
  pre cn a b h := by iintro #%Hb; iintro !>; ipureintro; exact hpre cn a b h Hb

/-- For a prefix-closed protocol, `protoPrefix` is the protocol itself. -/
theorem protoPrefix_closed {P : Proto GF} (hP : ProtoPrefixClosed P) (cn : Nat) (R : List w8) :
    protoPrefix P cn R ⊢ □ P cn R := by
  unfold protoPrefix
  iintro (%h | ⟨%ext, %h, #H⟩)
  · subst h; iapply hP.nil cn
  · iapply hP.pre cn R ext h $$ H

end protos

/-- The protocol of the direction from the end `s`: `Pd` the dialer's, `Pa` the acceptor's. -/
def sel {α : Type} (s : Bool) (Pd Pa : α) : α := if s then Pa else Pd

@[simp] theorem sel_false {α : Type} (Pd Pa : α) : sel false Pd Pa = Pd := rfl
@[simp] theorem sel_true {α : Type} (Pd Pa : α) : sel true Pd Pa = Pa := rfl

/-! ## Ghost names and namespaces -/

/-- The library's global ghost names: the registry of the connections' names. -/
class NetProtoGS where
  reg : GName

/-- The ghost names of a connection: its address `addr` and the name of that address's map of
connections (`am`); for each direction `s` (from the end `s`), the writer's monotone list `w s`
and the reader's ghost variable `r s`; the ends' fresh tokens `f s`. -/
structure ConnPNames where
  addr : GoString
  am : GName
  w0 : GName
  w1 : GName
  r0 : GName
  r1 : GName
  f0 : GName
  f1 : GName
deriving DecidableEq

def ConnPNames.enc (γ : ConnPNames) :=
  (γ.addr, γ.am, γ.w0, γ.w1, γ.r0, γ.r1, γ.f0, γ.f1)

instance ConnPNames.countable : Pos.Countable ConnPNames :=
  .ofInjective (fun γ => Pos.Countable.encode γ.enc) (fun a b h => by
    have h' := Pos.encode_inj h
    cases a; cases b; simp only [ConnPNames.enc, Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h'; rfl)

def ConnPNames.w (γ : ConnPNames) : Bool → GName
  | false => γ.w0
  | true => γ.w1

def ConnPNames.r (γ : ConnPNames) : Bool → GName
  | false => γ.r0
  | true => γ.r1

def ConnPNames.f (γ : ConnPNames) : Bool → GName
  | false => γ.f0
  | true => γ.f1

/-- The registry's invariant. -/
def regN : Namespace := nroot.@"netproto_reg"
/-- The invariant of the address `a`. -/
def addrN (a : GoString) : Namespace := (nroot.@"netproto_addr").@a
/-- The invariant of the shared listener `l`. -/
def lisN (l : w64) : Namespace := (nroot.@"netproto_lis").@l

theorem sub_ndot_mask (N : Namespace) (x y : String) {A : Type} [Pos.Countable A] (a : A)
    (h : x ≠ y) : (↑((N.@x).@a) : CoPset) ⊆ ⊤ \ ↑(N.@y) :=
  fun p hp => ndot_mask N x y h p (nclose_subseteq _ a p hp)

theorem ndot_sub_mask (N : Namespace) (x y : String) {A : Type} [Pos.Countable A] (a : A)
    (h : x ≠ y) : (↑(N.@y) : CoPset) ⊆ ⊤ \ ↑((N.@x).@a) := by
  intro p hp
  rw [LawfulSet.mem_diff]
  refine ⟨CoPset.mem_full, fun h' => ?_⟩
  have := ndot_mask N x y h p (nclose_subseteq _ a p h')
  rw [LawfulSet.mem_diff] at this
  exact this.2 hp

theorem addrN_regN (a : GoString) : (↑(addrN a) : CoPset) ⊆ ⊤ \ ↑regN :=
  sub_ndot_mask nroot "netproto_addr" "netproto_reg" a (by decide)

theorem regN_addrN (a : GoString) : (↑regN : CoPset) ⊆ ⊤ \ ↑(addrN a) :=
  ndot_sub_mask nroot "netproto_addr" "netproto_reg" a (by decide)

theorem lisN_addrN (l : w64) (a : GoString) : (↑(lisN l) : CoPset) ⊆ ⊤ \ ↑(addrN a) := by
  intro p hp
  rw [LawfulSet.mem_diff]
  refine ⟨CoPset.mem_full, fun h' => ?_⟩
  have h1 := nclose_subseteq _ l p hp
  have h2 := nclose_subseteq _ a p h'
  exact ndot_ne_disjoint nroot (show "netproto_lis" ≠ "netproto_addr" by decide) p ⟨h1, h2⟩

/-! ## The vocabulary -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF]

include Gg

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The network's ghost state. -/
abbrev NG : NetGS GF := extGlobalGS netExt (G := Gg)

/-- The writer's half of the monotone list `γ` of what was written. -/
def wHalf (γ : GName) (W : List w8) : IProp GF := monoListAuthOwn γ (1 : Qp).half W
/-- A quarter of it (the registry's, and the address's). -/
def wQ (γ : GName) (W : List w8) : IProp GF := monoListAuthOwn γ (1 : Qp).half.half W
/-- `W` was written, at least (persistent). -/
def wLb (γ : GName) (W : List w8) : IProp GF := monoListLbOwn γ W
/-- A half of the ghost variable `γ` of what was read. -/
def rHalf (γ : GName) (R : List w8) : IProp GF := ghostVar γ (1 : Qp).half R

instance wHalf_timeless γ W : Timeless (wHalf (Gg := Gg) γ W) := by unfold wHalf; infer_instance
instance wQ_timeless γ W : Timeless (wQ (Gg := Gg) γ W) := by unfold wQ; infer_instance
instance wLb_timeless γ W : Timeless (wLb (Gg := Gg) γ W) := by unfold wLb; infer_instance
instance wLb_persistent γ W : Persistent (wLb (Gg := Gg) γ W) := by unfold wLb; infer_instance
instance rHalf_timeless γ R : Timeless (rHalf (Gg := Gg) γ R) := by unfold rHalf; infer_instance

variable [π : NetProtoGS]

/-- The connection `cn` has the names `γ` (persistent). -/
def connElem (cn : Nat) (γ : ConnPNames) : IProp GF := ghostMapElem π.reg cn .discard γ

instance connElem_timeless cn γ : Timeless (connElem (Gg := Gg) cn γ) := by
  unfold connElem; infer_instance
instance connElem_persistent cn γ : Persistent (connElem (Gg := Gg) cn γ) := by
  unfold connElem; infer_instance

/-- The end `s`'s state. -/
def endSt (cn : Nat) (s : Bool) : IProp GF := iprop(∃ st, netEnd NG cn s st)

/-- The direction from the end `s`: its unread bytes, what its writer wrote (a quarter) and its
reader read (a half), agreeing. -/
def dirSt (cn : Nat) (γ : ConnPNames) (s : Bool) : IProp GF :=
  iprop(∃ (d : NetDir) (W R : List w8), netDir NG cn s d ∗ wQ (γ.w s) W ∗ rHalf (γ.r s) R ∗
    ⌜DirOk d W R⌝)

/-- A connection's state. -/
def connState (cn : Nat) (γ : ConnPNames) : IProp GF :=
  iprop(endSt cn false ∗ endSt cn true ∗ dirSt cn γ false ∗ dirSt cn γ true)

instance endSt_timeless cn s : Timeless (endSt (Gg := Gg) cn s) := by
  unfold endSt; infer_instance
instance dirSt_timeless cn γ s : Timeless (dirSt (Gg := Gg) cn γ s) := by
  unfold dirSt; infer_instance
instance connState_timeless cn γ : Timeless (connState (Gg := Gg) cn γ) := by
  unfold connState; infer_instance

/-- The registry: the connections the library knows, with their states. -/
def regInv : IProp GF :=
  iprop(∃ cm : GMap Nat ConnPNames, ghostMapAuth π.reg 1 cm ∗
    [∗map] cn ↦ γ ∈ cm, connState cn γ)

/-- The registry's invariant (persistent). -/
def regCtx : IProp GF := inv regN regInv

instance regCtx_persistent : Persistent (regCtx (Gg := Gg)) := by unfold regCtx; infer_instance

/-- The direction from the end `s` meets the protocol `P`: what was written (a quarter of the
writer's list) meets it up to extension. -/
def dirProto (cn : Nat) (γ : ConnPNames) (s : Bool) (P : Proto GF) : IProp GF :=
  iprop(∃ W, wQ (γ.w s) W ∗ protoPrefix P cn W)

/-- A connection dialed to an address with protocols `P` (dialers') and `Q` (acceptors'). -/
def protoSt (cn : Nat) (γ : ConnPNames) (P Q : Proto GF) : IProp GF :=
  iprop(dirProto cn γ false P ∗ dirProto cn γ true Q)

/-- The acceptor's share of the connection `cn` dialed to `a` (deposited by its dialer): its
names, its writer's half (nothing written) and its reader's (nothing read), its fresh token. -/
def pendRes (a : GoString) (γa : GName) (cn : Nat) : IProp GF :=
  iprop(∃ γ, connElem cn γ ∗ ghostMapElem γa cn .discard γ ∗ ⌜γ.addr = a ∧ γ.am = γa⌝ ∗
    wHalf (γ.w true) [] ∗ rHalf (γ.r false) [] ∗ token (γ.f true))

instance pendRes_timeless a γa cn : Timeless (pendRes (Gg := Gg) a γa cn) := by
  unfold pendRes; infer_instance

instance pendRes_map_timeless a γa S :
    Timeless ([∗map] cn ↦ _u ∈ setMap S, pendRes (Gg := Gg) a γa cn) :=
  BigSepM.bigSepM_timeless (fun _ => inferInstance)

instance connElem_map_timeless (cmA : GMap Nat ConnPNames) :
    Timeless ([∗map] cn ↦ γ ∈ cmA, connElem (Gg := Gg) cn γ) :=
  BigSepM.bigSepM_timeless (fun _ => inferInstance)

/-- The invariant of the address `a`, with protocols `P` and `Q`: its pending connections, each
with its acceptor's share, and the connections dialed to it (the map `γa`), each meeting the
protocols. -/
def addrInvP (a : GoString) (γa : GName) (P Q : Proto GF) : IProp GF :=
  iprop(∃ (S : GSet Nat) (cmA : GMap Nat ConnPNames), netPend NG a S ∗ ghostMapAuth γa 1 cmA ∗
    ([∗map] cn ↦ _u ∈ setMap S, pendRes a γa cn) ∗ ([∗map] cn ↦ γ ∈ cmA, connElem cn γ) ∗
    [∗map] cn ↦ γ ∈ cmA, protoSt cn γ P Q)

/-- `a` is a valid address (persistent). -/
def addrTok (a : GoString) : IProp GF := iprop(⌜addrOk a = true⌝)

instance addrTok_persistent a : Persistent (addrTok (GF := GF) a) := by
  unfold addrTok; infer_instance

/-- `a`'s protocols are not set: its pending set, empty (exclusive), and its listening token. -/
def addrUnset (a : GoString) : IProp GF := iprop(netPend NG a ∅ ∗ addrTok a ∗ netLisTok NG a)

/-- The namespace of the invariant of `a`'s listening token. -/
def lisTokN (a : GoString) : Namespace := (nroot.@"netproto_listok").@a

/-- The namespace of the invariant of the right to listen at `la` (`lisProto`). -/
def lisToksN (la : GoString) : Namespace := (nroot.@"netproto_listoks").@la

/-- Where `a`'s listening token is: in an invariant of its own (`addr_set_proto`), or in that of the
right to listen at an `la` that takes `a` (`lisProto la`, `lis_set_proto`: a wildcard). -/
def lisTokInv (a : GoString) : IProp GF :=
  iprop(inv (lisTokN a) (netLisTok NG a) ∨
    ∃ la, ⌜lisAccepts la a⌝ ∗ inv (lisToksN la) (lisToks NG la))

instance lisTokInv_persistent a : Persistent (lisTokInv (Gg := Gg) a) := by
  unfold lisTokInv; infer_instance

/-- `a`'s protocols: `P` for what its dialers write, `Q` for what its acceptors write, and its
listening token in an invariant (persistent: whoever has it may listen at `a`, `listen_au`). -/
def addrProto (a : GoString) (P Q : Proto GF) : IProp GF :=
  iprop(∃ γa, inv (addrN a) (addrInvP a γa P Q) ∗ lisTokInv a ∗ addrTok a ∗ regCtx)

instance addrProto_persistent a P Q : Persistent (addrProto (Gg := Gg) a P Q) := by
  unfold addrProto; infer_instance

/-- D21. The addresses a listener at `la` takes are unset (exclusive): for each valid address `la`
takes (`lisAccepts`: `la` itself if it is valid, every valid address with its port if it is a
wildcard), its pending set, empty, and its listening token. From the extension's start resources
(`addrs_lis_start`). -/
def lisUnset (la : GoString) : IProp GF :=
  [∗map] a ↦ _u ∈ addrSpace (), iprop(⌜lisAccepts la a⌝ → netPend NG a ∅ ∗ netLisTok NG a)

/-- D21. The protocols of every valid address a listener at `la` takes, the same for all: `P` for
what dialers write, `Q` for what acceptors write (each address's `addrProto`, `lisProto_addr`: a
dialer dials any of them as usual, `dial_au`), and the right to listen at `la` in an invariant
(`listen_lis_au`). Persistent. What a wildcard listener's `Accept` needs (`accept_lis_au`). -/
def lisProto (la : GoString) (P Q : Proto GF) : IProp GF :=
  iprop(□ (∀ a, ⌜addrOk a = true ∧ lisAccepts la a⌝ → addrProto a P Q) ∗
    inv (lisToksN la) (lisToks NG la) ∗ ⌜listenOk la = true⌝)

instance lisProto_persistent la P Q : Persistent (lisProto (Gg := Gg) la P Q) := by
  unfold lisProto; infer_instance

/-- The handle of the connection `cn` with names `γ`, dialed to an address with protocols `Pd`,
`Pa` (persistent). -/
def connH (cn : Nat) (γ : ConnPNames) (Pd Pa : Proto GF) : IProp GF :=
  iprop(connElem cn γ ∗ regCtx ∗ inv (addrN γ.addr) (addrInvP γ.addr γ.am Pd Pa) ∗
    ghostMapElem γ.am cn .discard γ)

instance connH_persistent cn γ Pd Pa : Persistent (connH (Gg := Gg) cn γ Pd Pa) := by
  unfold connH; infer_instance

/-- The connection `cn` is the library's (persistent). -/
def connIs (cn : Nat) : IProp GF := iprop(∃ γ, connElem cn γ ∗ regCtx)

instance connIs_persistent cn : Persistent (connIs (Gg := Gg) cn) := by
  unfold connIs; infer_instance

/-- The writer of the direction from the end `s` of `cn`: it has written `W`, protocol `P`. -/
def sendTok (cn : Nat) (s : Bool) (P : Proto GF) (W : List w8) : IProp GF :=
  iprop(∃ γ Pd Pa, connH cn γ Pd Pa ∗ ⌜sel s Pd Pa = P⌝ ∗ wHalf (γ.w s) W)

/-- The reader at the end `s` of `cn` (of the direction towards `s`), without its protocol fact:
it has read `R`, which was written, protocol `P`. -/
def recvCore (cn : Nat) (s : Bool) (P : Proto GF) (R : List w8) : IProp GF :=
  iprop(∃ γ Pd Pa, connH cn γ Pd Pa ∗ ⌜sel (!s) Pd Pa = P⌝ ∗ rHalf (γ.r (!s)) R ∗
    wLb (γ.w (!s)) R)

/-- The reader at the end `s` of `cn`: it has read `R`, which meets `P` up to extension. -/
def recvTok (cn : Nat) (s : Bool) (P : Proto GF) (R : List w8) : IProp GF :=
  iprop(recvCore cn s P R ∗ protoPrefix P cn R)

/-- `recvTok`, its protocol fact one step later (what a `Read` gives: `read_au`). -/
def recvTokL (cn : Nat) (s : Bool) (P : Proto GF) (R : List w8) : IProp GF :=
  iprop(recvCore cn s P R ∗ ▷ protoPrefix P cn R)

/-- The end `s` of `cn`: writing with `Pout` (written `W`), reading with `Pin` (read `R`). -/
def connEnd (cn : Nat) (s : Bool) (Pout Pin : Proto GF) (W R : List w8) : IProp GF :=
  iprop(sendTok cn s Pout W ∗ recvTok cn s Pin R)

/-- The direction from the end `s` of `cn` was written at least `W` (persistent). -/
def sentLb (cn : Nat) (s : Bool) (W : List w8) : IProp GF :=
  iprop(∃ γ, connElem cn γ ∗ wLb (γ.w s) W)

instance sentLb_persistent cn s W : Persistent (sentLb (Gg := Gg) cn s W) := by
  unfold sentLb; infer_instance

/-- The end `s` of `cn` is new: handed out once, by the dial or accept that made it (exclusive,
`connFresh_excl`; timeless). -/
def connFresh (cn : Nat) (s : Bool) : IProp GF :=
  iprop(∃ γ, connElem cn γ ∗ token (γ.f s))

instance connFresh_timeless cn s : Timeless (connFresh (Gg := Gg) cn s) := by
  unfold connFresh; infer_instance

end defs


/-! ## The laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF]
include Gg

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ### The writer's list, in three shares -/

theorem w_split (γ : GName) (W : List w8) :
    (monoListAuthOwn γ 1 W : IProp GF) ⊣⊢ wHalf (Gg := Gg) γ W ∗ wQ γ W ∗ wQ γ W := by
  unfold wHalf wQ
  have h1 : (monoListAuthOwn γ 1 W : IProp GF) ⊣⊢
      iprop(monoListAuthOwn γ (1 : Qp).half W ∗ monoListAuthOwn γ (1 : Qp).half W) := by
    conv => lhs; rw [← Qp.half_add_half 1]
    exact (monoListAuthOwn_fractional γ W).fractional _ _
  have h2 : (monoListAuthOwn γ (1 : Qp).half W : IProp GF) ⊣⊢
      iprop(monoListAuthOwn γ (1 : Qp).half.half W ∗ monoListAuthOwn γ (1 : Qp).half.half W) := by
    conv => lhs; rw [← Qp.half_add_half (1 : Qp).half]
    exact (monoListAuthOwn_fractional γ W).fractional _ _
  exact h1.trans (sep_congr_right h2)

theorem w_agree_hq (γ : GName) (W1 W2 : List w8) :
    ⊢ wHalf (Gg := Gg) γ W1 -∗ wQ γ W2 -∗ ⌜W1 = W2⌝ := by
  unfold wHalf wQ
  iintro H1 H2
  icases monoListAuthOwn_agree γ _ _ W1 W2 $$ H1 H2 with %h
  ipureintro; exact h.2

theorem w_agree_qq (γ : GName) (W1 W2 : List w8) :
    ⊢ wQ (Gg := Gg) γ W1 -∗ wQ γ W2 -∗ ⌜W1 = W2⌝ := by
  unfold wQ
  iintro H1 H2
  icases monoListAuthOwn_agree γ _ _ W1 W2 $$ H1 H2 with %h
  ipureintro; exact h.2

theorem w_update (γ : GName) (W x : List w8) :
    ⊢ wHalf (Gg := Gg) γ W -∗ wQ γ W -∗ wQ γ W ==∗
      wHalf γ (W ++ x) ∗ wQ γ (W ++ x) ∗ wQ γ (W ++ x) := by
  iintro H1 H2 H3
  ihave H := (w_split (Gg := Gg) γ W).2 $$ [H1 H2 H3]
  · iframe H1 H2 H3
  imod monoListAuthOwn_update_app x $$ H with ⟨H, -⟩
  imodintro
  iapply (w_split (Gg := Gg) γ (W ++ x)).1 $$ H

theorem wQ_lb (γ : GName) (W : List w8) : wQ (Gg := Gg) γ W ⊢ wLb γ W := by
  unfold wQ wLb; exact monoListLbOwn_get γ _ W

theorem wHalf_lb (γ : GName) (W : List w8) : wHalf (Gg := Gg) γ W ⊢ wLb γ W := by
  unfold wHalf wLb; exact monoListLbOwn_get γ _ W

theorem wLb_le (γ : GName) {W : List w8} (W' : List w8) (h : W' <+: W) :
    wLb (Gg := Gg) γ W ⊢ wLb γ W' := by
  unfold wLb; exact monoListLbOwn_le W' h

theorem wLb_nil (γ : GName) : ⊢ |==> wLb (Gg := Gg) γ [] := by
  unfold wLb; exact monoListLbOwn_nil γ

theorem wHalf_wLb_prefix (γ : GName) (W W0 : List w8) :
    ⊢ wHalf (Gg := Gg) γ W -∗ wLb γ W0 -∗ ⌜W0 <+: W⌝ := by
  unfold wHalf wLb
  iintro Ha Hl
  icases mono_list_auth_lb_valid γ _ W W0 $$ Ha Hl with %H
  ipureintro; exact H.2

theorem w_alloc : ⊢ |==> ∃ γ, wHalf (Gg := Gg) γ [] ∗ wQ γ [] ∗ wQ γ [] := by
  imod mono_list_own_alloc (GF := GF) ([] : List w8) with ⟨%γ, H, -⟩
  imodintro
  iexists γ
  iapply (w_split (Gg := Gg) γ []).1 $$ H

theorem r_alloc : ⊢ |==> ∃ γ, rHalf (Gg := Gg) γ [] ∗ rHalf γ [] := by
  imod ghostVar_alloc (GF := GF) ([] : List w8) with ⟨%γ, H⟩
  icases (ghostVar_split_half γ 1 ([] : List w8)).mp $$ H with ⟨H1, H2⟩
  imodintro
  iexists γ
  unfold rHalf
  iframe H1 H2

theorem r_agree (γ : GName) (R1 R2 : List w8) :
    ⊢ rHalf (Gg := Gg) γ R1 -∗ rHalf γ R2 -∗ ⌜R1 = R2⌝ := by
  unfold rHalf
  iintro H1 H2
  iapply ghostVar_agree $$ H1 H2

theorem r_update (γ : GName) (R1 R2 R : List w8) :
    ⊢ rHalf (Gg := Gg) γ R1 -∗ rHalf γ R2 ==∗ rHalf γ R ∗ rHalf γ R := by
  unfold rHalf
  iintro H1 H2
  iapply ghostVar_update_halves $$ H1 H2

/-! ### The registry, the addresses -/

/-- The library's ghost state: an empty registry. -/
theorem netProto_alloc (E : CoPset) : ⊢ |={E}=> ∃ π : NetProtoGS, regCtx (Gg := Gg) (π := π) := by
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := ConnPNames) with ⟨%γ, H⟩
  imod inv_alloc regN E (regInv (Gg := Gg) (π := ⟨γ⟩)) $$ [H] with #Hinv
  · inext
    unfold regInv
    iexists ∅
    iframe H
    iapply BigSepM.bigSepM_empty.2
    iempintro
  imodintro
  iexists ⟨γ⟩
  unfold regCtx
  iexact Hinv

theorem addrUnset_tok (a : GoString) : addrUnset (Gg := Gg) a ⊢ addrTok a := by
  unfold addrUnset; iintro ⟨-, $, -⟩

theorem addrProto_tok (a : GoString) (P Q : Proto GF) [NetProtoGS] :
    addrProto (Gg := Gg) a P Q ⊢ addrTok a := by
  unfold addrProto; iintro ⟨%γa, -, -, $, -⟩

/-- The protocols of an address `la` takes, from `la`'s. -/
theorem lisProto_addr [NetProtoGS] (la a : GoString) (P Q : Proto GF) (hok : addrOk a = true)
    (hacc : lisAccepts la a) : lisProto (Gg := Gg) la P Q ⊢ addrProto a P Q := by
  unfold lisProto
  iintro ⟨#H, -, -⟩
  iapply H
  ipureintro; exact ⟨hok, hacc⟩

theorem lisProto_ok [NetProtoGS] (la : GoString) (P Q : Proto GF) :
    lisProto (Gg := Gg) la P Q ⊢ ⌜listenOk la = true⌝ := by
  unfold lisProto; iintro ⟨-, -, $⟩

theorem addrProto_regCtx (a : GoString) (P Q : Proto GF) [NetProtoGS] :
    addrProto (Gg := Gg) a P Q ⊢ regCtx := by
  unfold addrProto; iintro ⟨%γa, -, -, -, $⟩

/-- `Listen` of `a` (`net.Listen.spec`'s update): its listening token, given at the step and put
back. -/
theorem listen_au (a : GoString) (P Q : Proto GF) [NetProtoGS] :
    addrProto (Gg := Gg) a P Q ⊢ |={⊤,∅}=> netLisTok NG a ∗ (netLisTok NG a ={∅,⊤}=∗ True) := by
  unfold addrProto lisTokInv addrTok
  iintro ⟨%γa, -, #Htok, %Hok, -⟩
  icases Htok with (#Htok | ⟨%la, %Hacc, #Htok⟩)
  · iinv Htok with >Ht Hclose
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    iframe Ht
    iintro Ht
    imod Hmask
    imod Hclose $$ [Ht] with -
    · inext; iexact Ht
    imodintro
    itrivial
  · -- the token is in the invariant of `la`'s right to listen
    iinv Htok with >Ht Hclose
    have hl : PartialMap.get? (addrSpace ()) a = some () := by
      rw [gmap_get?_eq]; exact addrSpace_lookup_ok () Hok
    unfold lisToks
    icases (BigSepM.bigSepM_lookup_acc hl).1 $$ Ht with ⟨Ha, Hrest⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    isplitl [Ha]
    · iapply Ha; ipureintro; exact Hacc
    iintro Ht
    imod Hmask
    imod Hclose $$ [Ht Hrest] with -
    · inext
      iapply Hrest
      iintro %_
      iexact Ht
    imodintro
    itrivial

/-- `Listen` of `la` (`net.Listen.spec`'s update, D21): the right to listen at `la`, given at the
step and put back. -/
theorem listen_lis_au (la : GoString) (P Q : Proto GF) [NetProtoGS] :
    lisProto (Gg := Gg) la P Q ⊢ |={⊤,∅}=> lisToks NG la ∗ (lisToks NG la ={∅,⊤}=∗ True) := by
  unfold lisProto
  iintro ⟨-, #Htok, -⟩
  iinv Htok with >Ht Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iframe Ht
  iintro Ht
  imod Hmask
  imod Hclose $$ [Ht] with -
  · inext; iexact Ht
  imodintro
  itrivial

/-- `a` is valid: what `net.Listen.spec`, `net.Dial.spec` and `Listener.Accept.spec` need. -/
theorem addrTok_ok (a : GoString) : addrTok (GF := GF) a ⊢ ⌜addrOk a = true⌝ := by
  unfold addrTok; iintro $

/-- Set the protocols of the address `a`, once, from its pending set (empty) and the invariant its
listening token is in. -/
theorem addr_set_proto_tok [NetProtoGS] (E : CoPset) (a : GoString) (P Q : Proto GF) :
    ⊢ regCtx (Gg := Gg) -∗ netPend NG a ∅ -∗ addrTok a -∗ lisTokInv a ={E}=∗ addrProto a P Q := by
  iintro #Hreg Hp #Ht #Htok
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := ConnPNames) with ⟨%γa, Ha⟩
  imod inv_alloc (addrN a) E (addrInvP (Gg := Gg) a γa P Q) $$ [Hp Ha] with #Hinv
  · inext
    unfold addrInvP
    iexists ∅, ∅
    iframe Hp Ha
    isplitl
    · iapply BigSepM.bigSepM_empty.2; iempintro
    isplitl
    · iapply BigSepM.bigSepM_empty.2; iempintro
    · iapply BigSepM.bigSepM_empty.2; iempintro
  imodintro
  unfold addrProto
  iexists γa
  iframe Hinv Htok Ht Hreg

/-- Set the protocols of an address, once: `P` for what its dialers write, `Q` for what its
acceptors write. -/
theorem addr_set_proto [NetProtoGS] (E : CoPset) (a : GoString) (P Q : Proto GF) :
    ⊢ regCtx (Gg := Gg) -∗ addrUnset a ={E}=∗ addrProto a P Q := by
  unfold addrUnset
  iintro #Hreg ⟨Hp, #Ht, Htk⟩
  imod inv_alloc (lisTokN a) E (netLisTok (NG (Gg := Gg)) a) $$ [Htk] with #Htok
  · inext; iexact Htk
  iapply addr_set_proto_tok E a P Q $$ Hreg Hp Ht
  unfold lisTokInv
  ileft; iexact Htok

/-- D21. Set the protocols of every valid address a listener at `la` takes, once, the same for all:
`P` for what its dialers write, `Q` for what its acceptors write. -/
theorem lis_set_proto [NetProtoGS] (E : CoPset) (la : GoString) (P Q : Proto GF)
    (hla : listenOk la = true) :
    ⊢ regCtx (Gg := Gg) -∗ lisUnset la ={E}=∗ lisProto la P Q := by
  iintro #Hreg Hu
  unfold lisUnset
  ihave ⟨Hp, Ht⟩ : ([∗map] a ↦ _u ∈ addrSpace (),
      iprop(⌜lisAccepts la a⌝ → netPend (NG (Gg := Gg)) a ∅)) ∗ lisToks (NG (Gg := Gg)) la $$ [Hu]
  · unfold lisToks
    rw [← BigSepM.bigSepM_sep_eq]
    iapply BigSepM.bigSepM_mono ?_ $$ Hu
    intro k v _
    iintro H
    by_cases hp : lisAccepts la k
    · ihave ⟨Hp, Ht⟩ := H $$ %hp
      isplitl [Hp]
      · iintro %_; iexact Hp
      · iintro %_; iexact Ht
    · isplitl []
      · iintro %h; exact absurd h hp
      · iintro %h; exact absurd h hp
  imod inv_alloc (lisToksN la) E (lisToks (NG (Gg := Gg)) la) $$ [Ht] with #Htok
  · inext; iexact Ht
  ihave Hps : [∗map] a ↦ _u ∈ addrSpace (), |={E}=>
      iprop(⌜addrOk a = true ∧ lisAccepts la a⌝ → addrProto (Gg := Gg) a P Q) $$ [Hp]
  · iapply BigSepM.bigSepM_impl $$ Hp
    imodintro
    iintro %k %v %hk H
    by_cases hp : lisAccepts la k
    · have hok : addrOk k = true := by
        have := addrSpace_lookup_isSome () k
        rw [← gmap_get?_eq, hk] at this; exact this.symm
      ihave Hp := H $$ %hp
      imod addr_set_proto_tok E k P Q $$ Hreg Hp [] [] with #Hk
      · unfold addrTok; ipureintro; exact hok
      · unfold lisTokInv; iright; iexists la; iframe Htok; ipureintro; exact hp
      imodintro
      iintro %_
      iexact Hk
    · imodintro
      iintro %h; exact absurd h.2 hp
  imod BigSepM.bigSepM_fupd E _ _ $$ Hps with #Hps
  imodintro
  unfold lisProto
  iframe Htok
  isplitl
  · imodintro
    iintro %a %ha
    have hl : PartialMap.get? (addrSpace ()) a = some () := by
      rw [gmap_get?_eq]; exact addrSpace_lookup_ok () ha.1
    ihave H := BigSepM.bigSepM_lookup hl $$ Hps
    iapply H
    ipureintro; exact ha
  · ipureintro; exact hla

/-- Set the protocols of every address of a list, `P a` and `Q a` for the address `a`. -/
theorem addrs_set_proto [NetProtoGS] (E : CoPset) (P Q : GoString → Proto GF) :
    ∀ addrs : List GoString,
    ⊢ regCtx (Gg := Gg) -∗ ([∗list] a ∈ addrs, addrUnset a) ={E}=∗
      [∗list] a ∈ addrs, addrProto a (P a) (Q a)
  | [] => by
    iintro - -
    imodintro
    iapply BigSepL.bigSepL_nil.2; iempintro
  | a :: addrs => by
    iintro #Hreg Hs
    icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨Hu, Hs⟩
    imod addr_set_proto E a (P a) (Q a) $$ Hreg Hu with #Hp
    imod addrs_set_proto E P Q addrs $$ Hreg Hs with Hps
    imodintro
    iapply BigSepL.bigSepL_cons.2
    iframe Hp Hps

/-! ### Simple laws of the tokens -/

section tokens
variable [NetProtoGS]

theorem connElem_agree (cn : Nat) (γ γ' : ConnPNames) :
    ⊢ connElem (Gg := Gg) cn γ -∗ connElem cn γ' -∗ ⌜γ = γ'⌝ := by
  unfold connElem
  iintro H1 H2
  iapply ghostMapElem_agree $$ H1 H2

/-- An end is new at most once. -/
theorem connFresh_excl (cn : Nat) (s : Bool) :
    connFresh (Gg := Gg) cn s ∗ connFresh cn s ⊢ (False : IProp GF) := by
  unfold connFresh
  iintro ⟨⟨%γ, He, Ht⟩, ⟨%γ', He', Ht'⟩⟩
  icases connElem_agree cn γ γ' $$ He He' with %h
  subst h
  iapply token_exclusive $$ Ht Ht'

theorem sendTok_connIs (cn : Nat) (s : Bool) (P : Proto GF) (W : List w8) :
    sendTok (Gg := Gg) cn s P W ⊢ connIs cn := by
  unfold sendTok connH connIs
  iintro ⟨%γ, %Pd, %Pa, ⟨#He, #Hr, -⟩, -⟩
  iexists γ
  iframe He Hr

theorem recvTok_connIs (cn : Nat) (s : Bool) (P : Proto GF) (R : List w8) :
    recvTok (Gg := Gg) cn s P R ⊢ connIs cn := by
  unfold recvTok recvCore connH connIs
  iintro ⟨⟨%γ, %Pd, %Pa, ⟨#He, #Hr, -⟩, -⟩, -⟩
  iexists γ
  iframe He Hr

/-- What a reader has read meets its protocol, up to extension. -/
theorem recvTok_proto (cn : Nat) (s : Bool) (P : Proto GF) (R : List w8) :
    recvTok (Gg := Gg) cn s P R ⊢ recvTok cn s P R ∗ protoPrefix P cn R := by
  unfold recvTok
  iintro ⟨H, #Hp⟩
  iframe H Hp

/-- For a prefix-closed protocol, what a reader has read meets it. -/
theorem recvTok_proto_closed {P : Proto GF} (hP : ProtoPrefixClosed P) (cn : Nat) (s : Bool)
    (R : List w8) : recvTok (Gg := Gg) cn s P R ⊢ recvTok cn s P R ∗ □ P cn R := by
  unfold recvTok
  iintro ⟨H, #Hp⟩
  iframe H Hp
  iapply protoPrefix_closed hP $$ Hp

/-- The bytes written so far (persistent, for the peer's arguments). -/
theorem sendTok_sentLb (cn : Nat) (s : Bool) (P : Proto GF) (W : List w8) :
    sendTok (Gg := Gg) cn s P W ⊢ sendTok cn s P W ∗ sentLb cn s W := by
  unfold sendTok sentLb connH
  iintro ⟨%γ, %Pd, %Pa, ⟨#He, #Hr, #Hi, #Hm⟩, %hP, Hw⟩
  ihave #Hlb := wHalf_lb (γ.w s) W $$ Hw
  isplitl [Hw]
  · iexists γ, Pd, Pa
    iframe He Hr Hi Hm Hw
    ipureintro; exact hP
  · iexists γ
    iframe He Hlb

/-- What a reader has read was written. -/
theorem recvTok_sentLb (cn : Nat) (s : Bool) (P : Proto GF) (R : List w8) :
    recvTok (Gg := Gg) cn s P R ⊢ sentLb cn (!s) R := by
  unfold recvTok recvCore sentLb connH
  iintro ⟨⟨%γ, %Pd, %Pa, ⟨#He, -⟩, -, -, #Hlb⟩, -⟩
  iexists γ
  iframe He Hlb

/-- The writer has written every lower bound of what it wrote. -/
theorem sendTok_sentLb_prefix (cn : Nat) (s : Bool) (P : Proto GF) (W W0 : List w8) :
    ⊢ sendTok (Gg := Gg) cn s P W -∗ sentLb cn s W0 -∗ ⌜W0 <+: W⌝ := by
  unfold sendTok sentLb connH
  iintro ⟨%γ, %Pd, %Pa, ⟨#He, -⟩, -, Hw⟩ ⟨%γ', #He', #Hlb⟩
  icases connElem_agree cn γ γ' $$ He He' with %h
  subst h
  iapply wHalf_wLb_prefix $$ Hw Hlb

theorem recvTok_L (cn : Nat) (s : Bool) (P : Proto GF) (R : List w8) :
    recvTok (Gg := Gg) cn s P R ⊢ recvTokL cn s P R := by
  unfold recvTok recvTokL
  iintro ⟨H, #Hp⟩
  iframe H
  inext
  iexact Hp

/-- What a reader has read meets its protocol, up to extension, one step later (`recvTokL`'s
protocol fact is under a later; dsv-bufio, review C2 on #24: with `bufio.ownBufReader_fact`, the
protocol fact of what a `*bufio.Reader` over a connection has returned, `net.connReader_proto`). -/
theorem recvTokL_proto (cn : Nat) (s : Bool) (P : Proto GF) (R : List w8) :
    recvTokL (Gg := Gg) cn s P R ⊢ recvTokL cn s P R ∗ ▷ protoPrefix P cn R := by
  unfold recvTokL
  iintro ⟨H, #Hp⟩
  iframe H Hp

/-- `recvTokL` is `recvTok` one step later: a program step makes it `recvTok`. -/
theorem recvTokL_later (cn : Nat) (s : Bool) (P : Proto GF) (R : List w8) :
    recvTokL (Gg := Gg) cn s P R ⊢ ▷ recvTok cn s P R := by
  unfold recvTokL recvTok
  iintro ⟨H, Hp⟩
  inext
  iframe H Hp

end tokens


/-! ### Opening a connection's state -/

section access
variable [NetProtoGS]

instance regInv_timeless : Timeless (regInv (Gg := Gg)) := by
  unfold regInv
  have : ∀ cm : GMap Nat ConnPNames, Timeless ([∗map] cn ↦ γ ∈ cm, connState (Gg := Gg) cn γ) :=
    fun _ => BigSepM.bigSepM_timeless (fun _ => inferInstance)
  infer_instance

theorem connState_acc (cn : Nat) (γ : ConnPNames) (se sd : Bool) :
    connState (Gg := Gg) cn γ ⊣⊢
      endSt cn se ∗ dirSt cn γ sd ∗ (endSt cn (!se) ∗ dirSt cn γ (!sd)) := by
  unfold connState
  cases se <;> cases sd <;> simp only [Bool.not_false, Bool.not_true] <;> constructor <;>
    iintro ⟨H1, H2, H3, H4⟩ <;> iframe

theorem protoSt_acc (cn : Nat) (γ : ConnPNames) (P Q : Proto GF) (s : Bool) :
    protoSt (Gg := Gg) cn γ P Q ⊣⊢
      dirProto cn γ s (sel s P Q) ∗ dirProto cn γ (!s) (sel (!s) P Q) := by
  unfold protoSt
  cases s <;> simp only [Bool.not_false, Bool.not_true, sel_false, sel_true] <;> constructor <;>
    iintro ⟨H1, H2⟩ <;> iframe

/-- Open the registry at the connection `cn` (names `γ`): the end `se`'s state and the direction
`sd`'s, and the way back. -/
theorem reg_open (cn : Nat) (γ : ConnPNames) (se sd : Bool) :
    ⊢ regCtx (Gg := Gg) -∗ connElem cn γ -∗
      |={⊤, ⊤ \ ↑regN}=> ∃ st d W R, netEnd NG cn se st ∗ netDir NG cn sd d ∗ wQ (γ.w sd) W ∗
        rHalf (γ.r sd) R ∗ ⌜DirOk d W R⌝ ∗
        ∀ st' d' W' R', netEnd NG cn se st' -∗ netDir NG cn sd d' -∗ wQ (γ.w sd) W' -∗
          rHalf (γ.r sd) R' -∗ ⌜DirOk d' W' R'⌝ ={⊤ \ ↑regN, ⊤}=∗ True := by
  iintro #Hreg #He
  unfold regCtx
  iinv Hreg with Hi Hclose
  unfold regInv
  icases Hi with ⟨%cm, >Ha, >Hcs⟩
  unfold connElem
  icases ghost_map_lookup $$ Ha He with %hl
  ihave ⟨Hc, Hcs⟩ := (BigSepM.bigSepM_lookup_acc (show PartialMap.get? cm cn = some γ from hl)).1
    $$ Hcs
  icases (connState_acc cn γ se sd).1 $$ Hc with ⟨He1, Hd1, Hrest⟩
  unfold endSt dirSt
  icases He1 with ⟨%st, Hend⟩
  icases Hd1 with ⟨%d, %W, %R, Hdir, HwQ, Hr, %Hok⟩
  imodintro
  iexists st, d, W, R
  iframe Hend Hdir HwQ Hr
  isplitr
  · ipureintro; exact Hok
  iintro %st' %d' %W' %R' Hend Hdir HwQ Hr %Hok'
  imod Hclose $$ [Ha Hcs Hrest Hend Hdir HwQ Hr]
  · inext
    iexists cm
    iframe Ha
    iapply Hcs
    iapply (connState_acc cn γ se sd).2
    unfold endSt dirSt
    iframe Hrest
    isplitl [Hend]
    · iexists st'; iexact Hend
    · iexists d', W', R'
      iframe Hdir HwQ Hr
      ipureintro; exact Hok'
  imodintro
  itrivial

end access


section access2
variable [NetProtoGS]

/-- Open the address `a`'s invariant at the connection `cn` (names `γ`): the protocol fact of the
direction `s` (one step later), and the way back. -/
theorem addr_open (E : CoPset) (a : GoString) (γa : GName) (P Q : Proto GF) (cn : Nat)
    (γ : ConnPNames) (s : Bool) (hE : (↑(addrN a) : CoPset) ⊆ E) :
    ⊢ inv (addrN a) (addrInvP (Gg := Gg) a γa P Q) -∗ ghostMapElem γa cn .discard γ -∗
      |={E, E \ ↑(addrN a)}=> ∃ W, wQ (γ.w s) W ∗ ▷ protoPrefix (sel s P Q) cn W ∗
        ∀ W', wQ (γ.w s) W' -∗ ▷ protoPrefix (sel s P Q) cn W' ={E \ ↑(addrN a), E}=∗ True := by
  iintro #Hai #Hm
  iinv Hai with Hj Hclose
  unfold addrInvP
  icases Hj with ⟨%S, %cmA, >Hp, >HaA, >Hdeps, >Hes, Hps⟩
  icases ghost_map_lookup $$ HaA Hm with %hlA
  ihave Hps := BigSepM.bigSepM_later.1 $$ Hps
  ihave ⟨Hpc, Hps⟩ := (BigSepM.bigSepM_lookup_acc
    (show PartialMap.get? cmA cn = some γ from hlA)).1 $$ Hps
  ihave Hpc := later_mono (protoSt_acc cn γ P Q s).1 $$ Hpc
  icases Hpc with ⟨Hdp, Hdp'⟩
  unfold dirProto
  icases Hdp with ⟨%W, >Hw, Hpp⟩
  imodintro
  iexists W
  iframe Hw Hpp
  iintro %W' Hw Hpp
  ihave Hpc : ▷ protoSt cn γ P Q $$ [Hw Hpp Hdp']
  · inext
    iapply (protoSt_acc cn γ P Q s).2
    unfold dirProto
    iframe Hdp'
    iexists W'
    iframe Hw Hpp
  ihave Hps := Hps $$ Hpc
  ihave Hps := BigSepM.bigSepM_later.2 $$ Hps
  imod Hclose $$ [Hp HaA Hdeps Hes Hps] with -
  · inext
    iexists S, cmA
    iframe Hp HaA Hdeps Hes Hps
  imodintro
  itrivial

/-! ### `Write` -/

/-- The writer predicate of `net.Conn.Write.spec` (`w`: the bytes this call wrote so far) for a
writer that had written `W0`: its `sendTok`. -/
def writeP (cn : Nat) (s : Bool) (P : Proto GF) (W0 : List w8) (w : List w8)
    (_res : Option NetErr) : IProp GF :=
  sendTok (Gg := Gg) cn s P (W0 ++ w)

theorem writeP_init (cn : Nat) (s : Bool) (P : Proto GF) (W0 : List w8) :
    sendTok (Gg := Gg) cn s P W0 ⊢ writeP cn s P W0 [] none := by
  unfold writeP; rw [List.append_nil]

/-- The accessor `net.Conn.Write.spec` takes, for `writeP`, given the protocol of everything the
writer will have written (`□ P cn (W0 ++ bs)`): each step's bytes extend the writer's `sendTok`
(and what the connection's direction holds), meeting the protocol up to extension. -/
theorem write_acc (cn : Nat) (s : Bool) (P : Proto GF) (W0 bs : List w8) :
    □ P cn (W0 ++ bs) ⊢
      □ (∀ (w rs : List w8), ⌜w ++ rs = bs⌝ -∗ writeP (Gg := Gg) cn s P W0 w none -∗
        |={⊤,∅}=> ∃ st0 d, netEnd NG cn s st0 ∗ netDir NG cn s d ∗
          ∀ k res d', ⌜WriteOutcome st0 d rs k res d'⌝ -∗ netEnd NG cn s st0 -∗
            netDir NG cn s d' ={∅,⊤}=∗ writeP cn s P W0 (w ++ rs.take k) res) := by
  iintro #HP
  imodintro
  iintro %w %rs %hw Htok
  unfold writeP sendTok connH
  icases Htok with ⟨%γ, %Pd, %Pa, ⟨#He, #Hreg, #Hai, #Hm⟩, %hP, Hw⟩
  imod reg_open cn γ s s $$ Hreg He with ⟨%st, %d, %W, %R, Hend, Hdir, HwQ, Hr, %Hok, Hcl⟩
  imod addr_open (⊤ \ ↑regN) γ.addr γ.am Pd Pa cn γ s (addrN_regN γ.addr) $$ Hai Hm
    with ⟨%W2, HwQ2, Hpp, Hcl2⟩
  icases w_agree_hq (γ.w s) _ _ $$ Hw HwQ with %h1
  icases w_agree_hq (γ.w s) _ _ $$ Hw HwQ2 with %h2
  subst h1 h2
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, d
  iframe Hend Hdir
  iintro %k %res %d' %Hwo Hend Hdir
  imod Hmask
  imod w_update (γ.w s) (W0 ++ w) (rs.take k) $$ Hw HwQ HwQ2 with ⟨Hw, HwQ, HwQ2⟩
  ihave Hpp' : ▷ protoPrefix (sel s Pd Pa) cn (W0 ++ w ++ rs.take k) $$ []
  · inext
    rw [hP]
    iapply protoPrefix_of ?_ $$ HP
    rw [← hw, List.append_assoc]
    exact (List.prefix_append_right_inj W0).2
      ((List.prefix_append_right_inj w).2 (List.take_prefix k rs))
  imod Hcl2 $$ HwQ2 Hpp' with -
  imod Hcl $$ Hend Hdir HwQ Hr [] with -
  · ipureintro; exact dirOk_write Hok Hwo
  imodintro
  iexists γ, Pd, Pa
  rw [← List.append_assoc]
  iframe He Hreg Hai Hm Hw
  ipureintro; exact hP

/-! ### `Read` -/

/-- The update `net.Conn.Read.spec` takes, for a reader with `recvTokL` (or `recvTok`, `recvTok_L`):
its result `r`'s bytes extend what it has read, and were written; their protocol fact is one step
later. The outcome is one at the reader's end (for `readOutcome_got_le`, ...). -/
theorem read_au (cn : Nat) (s : Bool) (P : Proto GF) (R : List w8) (n : Nat) :
    recvTokL (Gg := Gg) cn s P R ⊢
      |={⊤,∅}=> ∃ st d, netEnd NG cn s st ∗ netDir NG cn (!s) d ∗
        ∀ r d', ⌜ReadOutcome st d n r d'⌝ -∗ netEnd NG cn s st -∗ netDir NG cn (!s) d' ={∅,⊤}=∗
          recvTokL cn s P (R ++ r.got) ∗ ⌜∃ st d d', ReadOutcome st d n r d'⌝ := by
  unfold recvTokL recvCore connH
  iintro ⟨⟨%γ, %Pd, %Pa, ⟨#He, #Hreg, #Hai, #Hm⟩, %hP, Hr, #Hlb⟩, -⟩
  imod reg_open cn γ s (!s) $$ Hreg He with ⟨%st, %d, %W, %R0, Hend, Hdir, HwQ, Hr0, %Hok, Hcl⟩
  imod addr_open (⊤ \ ↑regN) γ.addr γ.am Pd Pa cn γ (!s) (addrN_regN γ.addr) $$ Hai Hm
    with ⟨%W2, HwQ2, Hpp, Hcl2⟩
  icases w_agree_qq (γ.w (!s)) _ _ $$ HwQ HwQ2 with %h1
  icases r_agree (γ.r (!s)) _ _ $$ Hr Hr0 with %h2
  subst h1 h2
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, d
  iframe Hend Hdir
  iintro %r %d' %Hro Hend Hdir
  imod Hmask
  have Hok' := dirOk_read Hok Hro
  imod r_update (γ.r (!s)) _ _ (R ++ r.got) $$ Hr Hr0 with ⟨Hr, Hr0⟩
  ihave #Hlb' := wQ_lb (γ.w (!s)) W $$ HwQ
  ihave #Hlb' := wLb_le (γ.w (!s)) (R ++ r.got) (dirOk_prefix Hok') $$ Hlb'
  ihave #Hpp' : ▷ protoPrefix (sel (!s) Pd Pa) cn (R ++ r.got) $$ [Hpp]
  · iapply later_mono (protoPrefix_le (dirOk_prefix Hok'))
    iexact Hpp
  imod Hcl2 $$ HwQ2 Hpp with -
  imod Hcl $$ Hend Hdir HwQ Hr0 [] with -
  · ipureintro; exact Hok'
  imodintro
  isplitl [Hr]
  · isplitl [Hr]
    · iexists γ, Pd, Pa
      iframe He Hreg Hai Hm Hr Hlb'
      ipureintro; exact hP
    · rw [← hP]; iexact Hpp'
  · ipureintro; exact ⟨st, d, d', Hro⟩

end access2


section dialAccept
variable [NetProtoGS]

/-! ### A new connection -/

/-- A connection the registry has is not one a dial has the fresh direction of. -/
theorem reg_fresh (cm : GMap Nat ConnPNames) (cn : Nat) (d : NetDir) :
    ⊢ ([∗map] k ↦ γ ∈ cm, connState (Gg := Gg) k γ) -∗ netDir NG cn true d -∗
      ⌜PartialMap.get? cm cn = none⌝ := by
  iintro Hcs Hd
  cases h : PartialMap.get? cm cn with
  | none => ipureintro; rfl
  | some γ =>
    iexfalso
    ihave Hc := BigSepM.bigSepM_lookup h $$ Hcs
    icases (connState_acc cn γ true true).1 $$ Hc with ⟨-, Hd', -⟩
    unfold dirSt
    icases Hd' with ⟨%d', %W, %R, Hd', -⟩
    iapply netDir_excl $$ Hd Hd'

/-- A connection the registry does not have is not in an address's map of connections. -/
theorem addr_fresh (cm cmA : GMap Nat ConnPNames) (cn : Nat)
    (h : PartialMap.get? cm cn = none) :
    ⊢ ghostMapAuth NetProtoGS.reg 1 cm -∗ ([∗map] k ↦ γ ∈ cmA, connElem (Gg := Gg) k γ) -∗
      ⌜PartialMap.get? cmA cn = none⌝ := by
  iintro Ha Hes
  cases hA : PartialMap.get? cmA cn with
  | none => ipureintro; rfl
  | some γ =>
    ihave He := BigSepM.bigSepM_lookup hA $$ Hes
    unfold connElem
    icases ghost_map_lookup $$ Ha He with %hl
    rw [gmap_get?_eq] at h
    rw [h] at hl
    cases hl

/-- A new connection `cn` dialed to `a` (its dialer's end state `st0` and direction `d0`, the
acceptor's fresh), in the registry and in the address's map: its names, its states, its protocol
facts (nothing written), the acceptor's share deposited, and the dialer's share. -/
theorem conn_register (a : GoString) (γa : GName) (P Q : Proto GF) (cn : Nat)
    (cm cmA : GMap Nat ConnPNames) (S : GSet Nat) (st0 : NetEnd) (d0 : NetDir)
    (hd0 : DirOk d0 [] []) (hcS : cn ∉ S) :
    ⊢ ghostMapAuth NetProtoGS.reg 1 cm -∗ ([∗map] k ↦ γ ∈ cm, connState (Gg := Gg) k γ) -∗
      ghostMapAuth γa 1 cmA -∗ ([∗map] k ↦ γ ∈ cmA, connElem k γ) -∗
      ([∗map] k ↦ _u ∈ setMap S, pendRes a γa k) -∗
      netEnd NG cn false st0 -∗ netDir NG cn false d0 -∗ netFresh NG cn true ==∗
      ∃ γ, ⌜γ.addr = a ∧ γ.am = γa⌝ ∗
        (∃ cm' : GMap Nat ConnPNames, ghostMapAuth NetProtoGS.reg 1 cm' ∗
          [∗map] k ↦ γ ∈ cm', connState k γ) ∗
        ghostMapAuth γa 1 (PartialMap.insert cmA cn γ) ∗
        ([∗map] k ↦ γ ∈ PartialMap.insert cmA cn γ, connElem k γ) ∗
        ([∗map] k ↦ _u ∈ setMap (S ∪ {[cn]}), pendRes a γa k) ∗
        ⌜PartialMap.get? cmA cn = none⌝ ∗ protoSt cn γ P Q ∗
        connElem cn γ ∗ ghostMapElem γa cn .discard γ ∗ wHalf (γ.w false) [] ∗
        rHalf (γ.r true) [] ∗ wLb (γ.w true) [] ∗ token (γ.f false) := by
  iintro Ha Hcs HaA Hes Hdeps Hend0 Hdir0 Hfa
  unfold netFresh
  icases Hfa with ⟨Hend1, Hdir1⟩
  icases reg_fresh cm cn NetDir.fresh $$ Hcs Hdir1 with %hcm
  icases addr_fresh cm cmA cn hcm $$ Ha Hes with %hcmA
  imod w_alloc (Gg := Gg) with ⟨%w0, Hw0, Hw0a, Hw0b⟩
  imod w_alloc (Gg := Gg) with ⟨%w1, Hw1, Hw1a, Hw1b⟩
  imod r_alloc (Gg := Gg) with ⟨%r0, Hr0, Hr0a⟩
  imod r_alloc (Gg := Gg) with ⟨%r1, Hr1, Hr1a⟩
  imod token_alloc (GF := GF) with ⟨%f0, Hf0⟩
  imod token_alloc (GF := GF) with ⟨%f1, Hf1⟩
  obtain ⟨γ, hw0, hw1, hr0, hr1, hf0, hf1, hga, hgam⟩ : ∃ γ : ConnPNames, γ.w false = w0 ∧
      γ.w true = w1 ∧ γ.r false = r0 ∧ γ.r true = r1 ∧ γ.f false = f0 ∧ γ.f true = f1 ∧
      γ.addr = a ∧ γ.am = γa :=
    ⟨⟨a, γa, w0, w1, r0, r1, f0, f1⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  subst hw0 hw1 hr0 hr1 hf0 hf1
  imod ghost_map_insert_persist (V := ConnPNames) (γ := NetProtoGS.reg) cn γ
    (by rw [← gmap_get?_eq]; exact hcm)
    $$ Ha with ⟨Ha, #He⟩
  imod ghost_map_insert_persist (V := ConnPNames) (γ := γa) cn γ
    (by rw [← gmap_get?_eq]; exact hcmA)
    $$ HaA with ⟨HaA, #Hm⟩
  imod wLb_nil (Gg := Gg) (γ.w true) with #Hlb1
  imodintro
  iexists γ
  isplitr
  · ipureintro; exact ⟨hga, hgam⟩
  isplitl [Ha Hcs Hend0 Hdir0 Hend1 Hdir1 Hw0a Hr0 Hw1a Hr1]
  · iexists PartialMap.insert cm cn γ
    iframe Ha
    iapply (BigSepM.bigSepM_insert hcm).2
    iframe Hcs
    unfold connState endSt dirSt
    isplitl [Hend0]
    · iexists st0; iexact Hend0
    isplitl [Hend1]
    · iexists NetEnd.fresh; iexact Hend1
    isplitl [Hdir0 Hw0a Hr0]
    · iexists d0, [], []
      iframe Hdir0 Hw0a Hr0
      ipureintro; exact hd0
    · iexists NetDir.fresh, [], []
      iframe Hdir1 Hw1a Hr1
      ipureintro; exact dirOk_fresh
  iframe HaA
  isplitl [Hes]
  · iapply (BigSepM.bigSepM_insert hcmA).2
    iframe Hes
    unfold connElem
    iexact He
  isplitl [Hdeps Hw1 Hr0a Hf1]
  · rw [setMap_insert]
    iapply (BigSepM.bigSepM_insert (setMap_lookup_none hcS)).2
    iframe Hdeps
    unfold pendRes
    iexists γ
    unfold connElem
    iframe He Hm Hw1 Hr0a Hf1
    ipureintro; exact ⟨hga, hgam⟩
  isplitr
  · ipureintro; exact hcmA
  isplitl [Hw0b Hw1b]
  · unfold protoSt dirProto
    isplitl [Hw0b]
    · iexists []; iframe Hw0b; iapply protoPrefix_nil
    · iexists []; iframe Hw1b; iapply protoPrefix_nil
  unfold connElem
  iframe He Hm Hw0 Hr1a Hlb1 Hf0

/-! ### `Dial` -/

/-- The update `net.Dial.spec` (and `net.DialTimeout.spec`) takes, with `Qfail := True`, for an
address with protocols `P` and `Q`: a new connection's dialer gets its end's tokens (writing with
`P`, reading with `Q`) and its fresh token; its acceptor's are deposited at the address (also when
the dial fails and leaves the connection pending, abandoned: D16). The validity the spec needs
is in `addrProto` (`addrProto_tok`). -/
theorem dial_au (a : GoString) (P Q : Proto GF) :
    addrProto (Gg := Gg) a P Q ⊢
      |={⊤,∅}=> ∃ S, netPend NG a S ∗
        ∀ cn, ⌜cn ∉ S⌝ -∗ netPend NG a (S ∪ {[cn]}) -∗ netConnAt NG cn a -∗
          netFresh NG cn true -∗
          ((netFresh NG cn false ={∅,⊤}=∗ connEnd cn false P Q [] [] ∗ connFresh cn false) ∧
           (netEnd NG cn false { NetEnd.fresh with closed := true } -∗
            netDir NG cn false ⟨[], .fin⟩ ={∅,⊤}=∗ True)) := by
  unfold addrProto
  iintro ⟨%γa, #Hai, -, #Ht, #Hreg⟩
  iinv Hai with Hj Hclose
  iunfold addrInvP at Hj
  icases Hj with ⟨%S, %cmA, >Hp, >HaA, >Hdeps, >Hes, Hps⟩
  unfold regCtx
  iinv Hreg with Hi Hclose'
  · exact ⟨regN_addrN a, trivial⟩
  iunfold regInv at Hi
  icases Hi with ⟨%cm, >Ha, >Hcs⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists S
  iframe Hp
  iintro %cn %HcS Hp #Hat Hfa
  isplit
  · iintro Hfd
    imod Hmask
    iunfold netFresh at Hfd
    icases Hfd with ⟨Hend0, Hdir0⟩
    imod conn_register a γa P Q cn cm cmA S NetEnd.fresh NetDir.fresh dirOk_fresh HcS
      $$ Ha Hcs HaA Hes Hdeps Hend0 Hdir0 Hfa
      with ⟨%γ, %hγ, Hreg', HaA, Hes, Hdeps, %hcmA, Hpst, #He, #Hm, Hw0, Hr1, #Hlb1, Hf0⟩
    obtain ⟨hγa, hγm⟩ := hγ
    imod Hclose' $$ [Hreg'] with -
    · inext; unfold regInv; iexact Hreg'
    imod Hclose $$ [Hp HaA Hes Hdeps Hps Hpst] with -
    · inext
      unfold addrInvP
      iexists S ∪ {[cn]}, PartialMap.insert cmA cn γ
      iframe Hp HaA Hes Hdeps
      iapply (BigSepM.bigSepM_insert hcmA).2
      iframe Hpst Hps
    imodintro
    unfold connEnd sendTok recvTok recvCore connFresh connH regCtx
    simp only [Bool.not_false]
    subst hγa hγm
    isplitl [Hw0 Hr1]
    · isplitl [Hw0]
      · iexists γ, P, Q
        iframe He Hreg Hai Hm Hw0
        ipureintro; rfl
      · isplitl [Hr1]
        · iexists γ, P, Q
          iframe He Hreg Hai Hm Hr1 Hlb1
          ipureintro; rfl
        · iapply protoPrefix_nil
    · iexists γ
      iframe He Hf0
  · iintro Hend0 Hdir0
    imod Hmask
    imod conn_register a γa P Q cn cm cmA S _ _ dirOk_abandoned HcS
      $$ Ha Hcs HaA Hes Hdeps Hend0 Hdir0 Hfa
      with ⟨%γ, %-, Hreg', HaA, Hes, Hdeps, %hcmA, Hpst, -⟩
    imod Hclose' $$ [Hreg'] with -
    · inext; unfold regInv; iexact Hreg'
    imod Hclose $$ [Hp HaA Hes Hdeps Hps Hpst] with -
    · inext
      unfold addrInvP
      iexists S ∪ {[cn]}, PartialMap.insert cmA cn γ
      iframe Hp HaA Hes Hdeps
      iapply (BigSepM.bigSepM_insert hcmA).2
      iframe Hpst Hps
    imodintro
    itrivial

/-! ### `Accept` -/

/-- The acceptor's share of a pending connection, as its end's tokens. -/
theorem pendRes_take (a : GoString) (γa : GName) (P Q : Proto GF) (cn : Nat) :
    ⊢ inv (addrN a) (addrInvP (Gg := Gg) a γa P Q) -∗ regCtx -∗ pendRes a γa cn ==∗
      connEnd cn true Q P [] [] ∗ connFresh cn true := by
  iintro #Hai #Hreg Hd
  unfold pendRes
  icases Hd with ⟨%γ, #He, #Hm, %hγ, Hw1, Hr0, Hf1⟩
  obtain ⟨hγa, hγm⟩ := hγ
  imod wLb_nil (Gg := Gg) (γ.w false) with #Hlb0
  imodintro
  unfold connEnd sendTok recvTok recvCore connFresh connH
  simp only [Bool.not_true]
  subst hγa hγm
  isplitl [Hw1 Hr0]
  · isplitl [Hw1]
    · iexists γ, P, Q
      iframe He Hreg Hai Hm Hw1
      ipureintro; rfl
    · isplitl [Hr0]
      · iexists γ, P, Q
        iframe He Hreg Hai Hm Hr0 Hlb0
        ipureintro; rfl
      · iapply protoPrefix_nil
  · iexists γ
    iframe He Hf1

/-- The update for a connection dialed to the address `a` (protocols `P`, `Q`) accepted by this
node's listener `l` at `la`, which the thread owns (`netLis`): a failure gives the listener back;
a connection, the listener and the acceptor's end's tokens (writing with `Q`, reading with `P`) and
its fresh token. -/
theorem accept_au_at (la a : GoString) (P Q : Proto GF) (hL : NetLocalGS GF) (l : w64)
    (o : Bool) :
    ⊢ addrProto (Gg := Gg) a P Q -∗ netLis hL l la o -∗
      |={⊤,∅}=> ∃ o' S, netLis hL l la o' ∗ netPend NG a S ∗
        ((netLis hL l la o' -∗ netPend NG a S ={∅,⊤}=∗ netLis hL l la o) ∧
          (⌜o' = true⌝ -∗ ∀ cn, ⌜cn ∈ S⌝ -∗ netLis hL l la o' -∗ netPend NG a (S \ {[cn]}) -∗
            netConnAt NG cn a ={∅,⊤}=∗
              netLis hL l la o ∗ connEnd cn true Q P [] [] ∗ connFresh cn true)) := by
  unfold addrProto
  iintro ⟨%γa, #Hai, -, #Ht, #Hreg⟩ Hl
  iinv Hai with Hj Hclose
  iunfold addrInvP at Hj
  icases Hj with ⟨%S, %cmA, >Hp, >HaA, >Hdeps, >Hes, Hps⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists o, S
  iframe Hl Hp
  isplit
  · iintro Hl Hp
    imod Hmask
    imod Hclose $$ [Hp HaA Hdeps Hes Hps] with -
    · inext
      unfold addrInvP
      iexists S, cmA
      iframe Hp HaA Hdeps Hes Hps
    imodintro
    iexact Hl
  · iintro %ho %cn %HcS Hl Hp #Hat
    imod Hmask
    have hl : PartialMap.get? (setMap S) cn = some () := by
      rw [gmap_get?_eq]; exact (GMap.elem_of_gset _ _).1 HcS
    icases (BigSepM.bigSepM_delete hl).1 $$ Hdeps with ⟨Hd, Hdeps⟩
    rw [setMap_delete]
    imod Hclose $$ [Hp HaA Hdeps Hes Hps] with -
    · inext
      unfold addrInvP
      iexists S \ {[cn]}, cmA
      iframe Hp HaA Hdeps Hes Hps
    imod pendRes_take a γa P Q cn $$ Hai Hreg Hd with ⟨Hc, Hf⟩
    imodintro
    iframe Hl Hc Hf

/-- The update `net.Listener.Accept.spec_addrOk` takes, for this node's listener `l` at the
address `a` (protocols `P`, `Q`), which the thread owns (`netLis`), with `Qfail _ := netLis hL l a o`:
a failure gives the listener back; a connection, the listener and the acceptor's end's tokens
(writing with `Q`, reading with `P`) and its fresh token. -/
theorem accept_au (a : GoString) (P Q : Proto GF) (hL : NetLocalGS GF) (l : w64) (o : Bool) :
    ⊢ addrProto (Gg := Gg) a P Q -∗ netLis hL l a o -∗
      |={⊤,∅}=> ∃ o' S, netLis hL l a o' ∗ netPend NG a S ∗
        ((netLis hL l a o' -∗ netPend NG a S ={∅,⊤}=∗ netLis hL l a o) ∧
          (⌜o' = true⌝ -∗ ∀ cn, ⌜cn ∈ S⌝ -∗ netLis hL l a o' -∗ netPend NG a (S \ {[cn]}) -∗
            netConnAt NG cn a ={∅,⊤}=∗
              netLis hL l a o ∗ connEnd cn true Q P [] [] ∗ connFresh cn true)) :=
  accept_au_at a a P Q hL l o

/-- D21. The updates `net.Listener.Accept.spec` takes, for this node's listener `l` at `la` (a
wildcard, or a valid address), which the thread owns (`netLis`), from the protocols of the
addresses `la` takes (`lisProto`), with `Qfail _ := netLis hL l la o` and `Qok a cn` the listener,
the acceptor's end's tokens of `cn` (dialed to `a`: writing with `Q`, reading with `P`) and its
fresh token. -/
theorem accept_lis_au (la : GoString) (P Q : Proto GF) (hL : NetLocalGS GF) (l : w64) (o : Bool) :
    ⊢ lisProto (Gg := Gg) la P Q -∗ netLis hL l la o -∗
      ((|={⊤,∅}=> ∃ o', netLis hL l la o' ∗ (netLis hL l la o' ={∅,⊤}=∗ netLis hL l la o)) ∧
        ∀ a, ⌜addrOk a = true ∧ lisAccepts la a⌝ -∗
          |={⊤,∅}=> ∃ o' S, netLis hL l la o' ∗ netPend NG a S ∗
            (⌜o' = true⌝ -∗ ∀ cn, ⌜cn ∈ S⌝ -∗ netLis hL l la o' -∗ netPend NG a (S \ {[cn]}) -∗
              netConnAt NG cn a ={∅,⊤}=∗
                netLis hL l la o ∗ connEnd cn true Q P [] [] ∗ connFresh cn true)) := by
  iintro #Hp Hl
  isplit
  · iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    iexists o
    iframe Hl
    iintro Hl
    imod Hmask
    imodintro
    iexact Hl
  · iintro %a %ha
    ihave #Ha := lisProto_addr la a P Q ha.1 ha.2 $$ Hp
    imod accept_au_at la a P Q hL l o $$ Ha Hl with ⟨%o', %S, Hl, Hpend, -, Hk⟩
    imodintro
    iexists o', S
    iframe Hl Hpend Hk

/-! ### A listener shared between threads -/

/-- This node's listener `l` at `a`, shared (persistent): what `accept_shared_au` and
`lisClose_au` need. -/
def lisInv (hL : NetLocalGS GF) (l : w64) (a : GoString) : IProp GF :=
  inv (lisN l) (∃ o, netLis hL l a o)

instance lisInv_persistent hL l a : Persistent (lisInv (Gg := Gg) hL l a) := by
  unfold lisInv; infer_instance

theorem lisInv_alloc (E : CoPset) (hL : NetLocalGS GF) (l : w64) (a : GoString) (o : Bool) :
    ⊢ netLis hL l a o ={E}=∗ lisInv (Gg := Gg) hL l a := by
  iintro Hl
  unfold lisInv
  iapply inv_alloc
  inext
  iexists o
  iexact Hl

/-- The update for a connection dialed to the address `a` (protocols `P`, `Q`) accepted by the
shared listener `l` at `la` (`Qfail _ := True`): a connection gives the acceptor's end's tokens and
its fresh token. -/
theorem accept_shared_au_at (la a : GoString) (P Q : Proto GF) (hL : NetLocalGS GF) (l : w64) :
    ⊢ addrProto (Gg := Gg) a P Q -∗ lisInv hL l la -∗
      |={⊤,∅}=> ∃ o S, netLis hL l la o ∗ netPend NG a S ∗
        ((netLis hL l la o -∗ netPend NG a S ={∅,⊤}=∗ True) ∧
          (⌜o = true⌝ -∗ ∀ cn, ⌜cn ∈ S⌝ -∗ netLis hL l la o -∗ netPend NG a (S \ {[cn]}) -∗
            netConnAt NG cn a ={∅,⊤}=∗ connEnd cn true Q P [] [] ∗ connFresh cn true)) := by
  unfold addrProto
  iintro ⟨%γa, #Hai, -, #Ht, #Hreg⟩ #Hli
  iinv Hai with Hj Hclose
  iunfold addrInvP at Hj
  icases Hj with ⟨%S, %cmA, >Hp, >HaA, >Hdeps, >Hes, Hps⟩
  unfold lisInv
  iinv Hli with Hk Hclose'
  · exact ⟨lisN_addrN l a, trivial⟩
  icases Hk with ⟨%o, >Hl⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists o, S
  iframe Hl Hp
  isplit
  · iintro Hl Hp
    imod Hmask
    imod Hclose' $$ [Hl] with -
    · inext; iexists o; iexact Hl
    imod Hclose $$ [Hp HaA Hdeps Hes Hps] with -
    · inext
      unfold addrInvP
      iexists S, cmA
      iframe Hp HaA Hdeps Hes Hps
    imodintro
    itrivial
  · iintro %ho %cn %HcS Hl Hp #Hat
    imod Hmask
    imod Hclose' $$ [Hl] with -
    · inext; iexists o; iexact Hl
    have hl : PartialMap.get? (setMap S) cn = some () := by
      rw [gmap_get?_eq]; exact (GMap.elem_of_gset _ _).1 HcS
    icases (BigSepM.bigSepM_delete hl).1 $$ Hdeps with ⟨Hd, Hdeps⟩
    rw [setMap_delete]
    imod Hclose $$ [Hp HaA Hdeps Hes Hps] with -
    · inext
      unfold addrInvP
      iexists S \ {[cn]}, cmA
      iframe Hp HaA Hdeps Hes Hps
    imod pendRes_take a γa P Q cn $$ Hai Hreg Hd with ⟨Hc, Hf⟩
    imodintro
    iframe Hc Hf

/-- The update `net.Listener.Accept.spec_addrOk` takes for a shared listener at the address `a`
(`Qfail _ := True`): a connection gives the acceptor's end's tokens and its fresh token. -/
theorem accept_shared_au (a : GoString) (P Q : Proto GF) (hL : NetLocalGS GF) (l : w64) :
    ⊢ addrProto (Gg := Gg) a P Q -∗ lisInv hL l a -∗
      |={⊤,∅}=> ∃ o S, netLis hL l a o ∗ netPend NG a S ∗
        ((netLis hL l a o -∗ netPend NG a S ={∅,⊤}=∗ True) ∧
          (⌜o = true⌝ -∗ ∀ cn, ⌜cn ∈ S⌝ -∗ netLis hL l a o -∗ netPend NG a (S \ {[cn]}) -∗
            netConnAt NG cn a ={∅,⊤}=∗ connEnd cn true Q P [] [] ∗ connFresh cn true)) :=
  accept_shared_au_at a a P Q hL l

/-- D21. The updates `net.Listener.Accept.spec` takes for a shared listener at `la` (a wildcard, or a
valid address), from the protocols of the addresses `la` takes (`lisProto`; `Qfail _ := True`, and
`Qok a cn` the acceptor's end's tokens of `cn`, dialed to `a`, and its fresh token). -/
theorem accept_lis_shared_au (la : GoString) (P Q : Proto GF) (hL : NetLocalGS GF) (l : w64) :
    ⊢ lisProto (Gg := Gg) la P Q -∗ lisInv hL l la -∗
      ((|={⊤,∅}=> ∃ o, netLis hL l la o ∗ (netLis hL l la o ={∅,⊤}=∗ True)) ∧
        ∀ a, ⌜addrOk a = true ∧ lisAccepts la a⌝ -∗
          |={⊤,∅}=> ∃ o S, netLis hL l la o ∗ netPend NG a S ∗
            (⌜o = true⌝ -∗ ∀ cn, ⌜cn ∈ S⌝ -∗ netLis hL l la o -∗ netPend NG a (S \ {[cn]}) -∗
              netConnAt NG cn a ={∅,⊤}=∗ connEnd cn true Q P [] [] ∗ connFresh cn true)) := by
  iintro #Hp #Hli
  isplit
  · unfold lisInv
    iinv Hli with Hk Hclose
    icases Hk with ⟨%o, >Hl⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    iexists o
    iframe Hl
    iintro Hl
    imod Hmask
    imod Hclose $$ [Hl] with -
    · inext; iexists o; iexact Hl
    imodintro
    itrivial
  · iintro %a %ha
    ihave #Ha := lisProto_addr la a P Q ha.1 ha.2 $$ Hp
    imod accept_shared_au_at la a P Q hL l $$ Ha Hli with ⟨%o, %S, Hl, Hpend, -, Hk⟩
    imodintro
    iexists o, S
    iframe Hl Hpend Hk

/-- The update `net.Listener.Close.spec` takes for a shared listener (`Q _ := True`). -/
theorem lisClose_au (hL : NetLocalGS GF) (l : w64) (a : GoString) :
    ⊢ lisInv (Gg := Gg) hL l a -∗
      |={⊤,∅}=> ∃ o, netLis hL l a o ∗
        ∀ res, ⌜LisCloseOutcome o res false⌝ -∗ netLis hL l a false ={∅,⊤}=∗ True := by
  iintro #Hli
  unfold lisInv
  iinv Hli with Hk Hclose
  icases Hk with ⟨%o, >Hl⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists o
  iframe Hl
  iintro %res %- Hl
  imod Hmask
  imod Hclose $$ [Hl] with -
  · inext; iexists false; iexact Hl
  imodintro
  itrivial

end dialAccept

/-! ### The end's other operations -/

section ends
variable [NetProtoGS]

/-- The update `net.Conn.Close.spec` takes (`Q res`: an outcome of the close). -/
theorem close_au (cn : Nat) (s : Bool) :
    connIs (Gg := Gg) cn ⊢
      |={⊤,∅}=> ∃ st d, netEnd NG cn s st ∗ netDir NG cn s d ∗
        ∀ res st' d', ⌜CloseOutcome st d res st' d'⌝ -∗ netEnd NG cn s st' -∗
          netDir NG cn s d' ={∅,⊤}=∗ ⌜∃ st d, CloseOutcome st d res st' d'⌝ := by
  unfold connIs
  iintro ⟨%γ, #He, #Hreg⟩
  imod reg_open cn γ s s $$ Hreg He with ⟨%st, %d, %W, %R, Hend, Hdir, HwQ, Hr, %Hok, Hcl⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, d
  iframe Hend Hdir
  iintro %res %st' %d' %Hc Hend Hdir
  imod Hmask
  imod Hcl $$ Hend Hdir HwQ Hr [] with -
  · ipureintro; exact dirOk_close Hok Hc
  imodintro
  ipureintro; exact ⟨st, d, Hc⟩

/-- The update `net.TCPConn.CloseWrite.spec` takes (`Q res`: an outcome of it). -/
theorem closeWrite_au (cn : Nat) (s : Bool) :
    connIs (Gg := Gg) cn ⊢
      |={⊤,∅}=> ∃ st d, netEnd NG cn s st ∗ netDir NG cn s d ∗
        ∀ res d', ⌜CloseWriteOutcome st d res d'⌝ -∗ netEnd NG cn s st -∗
          netDir NG cn s d' ={∅,⊤}=∗ ⌜∃ d, CloseWriteOutcome st d res d'⌝ := by
  unfold connIs
  iintro ⟨%γ, #He, #Hreg⟩
  imod reg_open cn γ s s $$ Hreg He with ⟨%st, %d, %W, %R, Hend, Hdir, HwQ, Hr, %Hok, Hcl⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, d
  iframe Hend Hdir
  iintro %res %d' %Hc Hend Hdir
  imod Hmask
  imod Hcl $$ Hend Hdir HwQ Hr [] with -
  · ipureintro; exact dirOk_closeWrite Hok Hc
  imodintro
  ipureintro; exact ⟨d, Hc⟩

/-- The update `net.Conn.SetDeadline.spec` takes (and the read and write deadlines': kind `k`). -/
theorem deadline_au (cn : Nat) (s : Bool) (k : w64) (set : Bool) :
    connIs (Gg := Gg) cn ⊢
      |={⊤,∅}=> ∃ st, netEnd NG cn s st ∗
        ∀ res st', ⌜DeadlineOutcome st k set res st'⌝ -∗ netEnd NG cn s st' ={∅,⊤}=∗
          ⌜∃ st, DeadlineOutcome st k set res st'⌝ := by
  unfold connIs
  iintro ⟨%γ, #He, #Hreg⟩
  imod reg_open cn γ s s $$ Hreg He with ⟨%st, %d, %W, %R, Hend, Hdir, HwQ, Hr, %Hok, Hcl⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st
  iframe Hend
  iintro %res %st' %Hc Hend
  imod Hmask
  imod Hcl $$ Hend Hdir HwQ Hr [] with -
  · ipureintro; exact Hok
  imodintro
  ipureintro; exact ⟨st, Hc⟩

/-- The update a socket option's spec takes (`TCPConn.SetKeepAlive.spec`, ...: validity `v`). -/
theorem sockopt_au (cn : Nat) (s : Bool) (v : Option Bool) :
    connIs (Gg := Gg) cn ⊢
      |={⊤,∅}=> ∃ st, netEnd NG cn s st ∗
        ∀ res, ⌜SockOptOutcome st v res⌝ -∗ netEnd NG cn s st ={∅,⊤}=∗
          ⌜∃ st, SockOptOutcome st v res⌝ := by
  unfold connIs
  iintro ⟨%γ, #He, #Hreg⟩
  imod reg_open cn γ s s $$ Hreg He with ⟨%st, %d, %W, %R, Hend, Hdir, HwQ, Hr, %Hok, Hcl⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st
  iframe Hend
  iintro %res %Hc Hend
  imod Hmask
  imod Hcl $$ Hend Hdir HwQ Hr [] with -
  · ipureintro; exact Hok
  imodintro
  ipureintro; exact ⟨st, Hc⟩

end ends



end laws

/-! ### The start: every valid address unset -/

section start

variable {GF : BundledGFunctors}

/-- Take the entries of the keys `l` (distinct) out of a big separating conjunction over a map. -/
theorem bigSepM_take_list {V : Type} (Φ : GoString → V → IProp GF) (f : GoString → V) :
    ∀ (m : GMap GoString V) (l : List GoString), l.Nodup → (∀ a ∈ l, m !! a = some (f a)) →
      ([∗map] a ↦ v ∈ m, Φ a v) ⊢ [∗list] a ∈ l, Φ a (f a)
  | _, [], _, _ => by
    iintro -
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | m, a :: l, hnd, hs => by
    have hv : PartialMap.get? m a = some (f a) := by
      rw [gmap_get?_eq]; exact hs a List.mem_cons_self
    have hl : ∀ b ∈ l, (Std.delete m a) !! b = some (f b) := by
      intro b hb
      have hne : a ≠ b := fun e => (List.nodup_cons.1 hnd).1 (e ▸ hb)
      show (GMap.delete a m) !! b = some (f b)
      rw [GMap.lookup_delete_ne _ hne]
      exact hs b (List.mem_cons_of_mem _ hb)
    iintro Hm
    icases (BigSepM.bigSepM_delete (Φ := Φ) hv).1 $$ Hm with ⟨Ha, Hm⟩
    iapply BigSepL.bigSepL_cons.2
    iframe Ha
    iapply bigSepM_take_list Φ f _ l (List.nodup_cons.1 hnd).2 hl $$ Hm

variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} [Gg : GooseGlobalGS hlc GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The extension's start resources: every address of a list of distinct valid addresses,
unset. -/
theorem addrs_start (g : NetGlobal) (addrs : List GoString) (hnd : addrs.Nodup)
    (hok : ∀ a ∈ addrs, addrOk a = true) :
    netStart (NG (Gg := Gg)) g ⊢ [∗list] a ∈ addrs, addrUnset (Gg := Gg) a := by
  unfold netStart
  iintro ⟨Hpends, Htoks⟩
  ihave Hpends := bigSepM_take_list (fun a S => netPend (NG (Gg := Gg)) a S) (fun _ => ∅)
    pendInit addrs hnd (fun a ha => addrSpace_lookup_ok _ (hok a ha)) $$ Hpends
  ihave Htoks := bigSepM_take_list (fun a _ => netLisTok (NG (Gg := Gg)) a) (fun _ => ())
    (addrSpace ()) addrs hnd (fun a ha => addrSpace_lookup_ok _ (hok a ha)) $$ Htoks
  ihave Hb : ([∗list] a ∈ addrs, iprop(netPend (NG (Gg := Gg)) a ∅ ∗
      netLisTok (NG (Gg := Gg)) a)) $$ [Hpends Htoks]
  · iapply BigSepL.bigSepL_sep_eqv.2
    iframe Hpends Htoks
  iapply BigSepL.bigSepL_mono (Φ := fun _ a => iprop(netPend (NG (Gg := Gg)) a ∅ ∗
    netLisTok (NG (Gg := Gg)) a)) ?_ $$ Hb
  intro k a hk
  unfold addrUnset addrTok
  iintro ⟨Hp, Ht⟩
  iframe Hp Ht
  ipureintro
  exact hok a (List.mem_of_getElem? hk)

/-- The valid addresses `q` holds of, unset: their pending sets, empty, and their listening
tokens. -/
def unsetWhere (q : GoString → Prop) : IProp GF :=
  [∗map] a ↦ _u ∈ addrSpace (),
    iprop(⌜q a⌝ → netPend (NG (Gg := Gg)) a ∅ ∗ netLisTok (NG (Gg := Gg)) a)

/-- The extension's start resources: every valid address unset. -/
theorem start_unset (g : NetGlobal) :
    netStart (NG (Gg := Gg)) g ⊢ unsetWhere (Gg := Gg) (fun _ => True) := by
  unfold netStart unsetWhere
  iintro ⟨Hpends, Htoks⟩
  ihave Hp : ([∗map] a ↦ _u ∈ addrSpace (), netPend (NG (Gg := Gg)) a ∅) $$ [Hpends]
  · ihave ⟨Hp, -⟩ := BigSepM.bigSepM_impl_strong (Φ := fun a S => netPend (NG (Gg := Gg)) a S)
      (Ψ := fun a (_ : Unit) => netPend (NG (Gg := Gg)) a ∅) (m₁ := pendInit)
      (m₂ := addrSpace ()) $$ [Hpends]
    · isplitl [Hpends]
      · iexact Hpends
      imodintro
      iintro %k %y
      by_cases hok : addrOk k = true
      · have hp : PartialMap.get? pendInit k = some ∅ := by
          rw [gmap_get?_eq]; exact addrSpace_lookup_ok ∅ hok
        rw [hp]
        simp only [Option.elim]
        iintro H %_
        iexact H
      · iintro - %hk
        have := addrSpace_lookup_isSome () k
        rw [← gmap_get?_eq, hk] at this
        exact absurd this.symm hok
    iexact Hp
  ihave Hb : ([∗map] a ↦ _u ∈ addrSpace (),
      iprop(netPend (NG (Gg := Gg)) a ∅ ∗ netLisTok (NG (Gg := Gg)) a)) $$ [Hp Htoks]
  · rw [BigSepM.bigSepM_sep_eq]
    iframe Hp Htoks
  iapply BigSepM.bigSepM_mono ?_ $$ Hb
  intro k v _
  iintro H %_
  iexact H

theorem unsetWhere_mono {q q' : GoString → Prop} (h : ∀ a, q' a → q a) :
    unsetWhere (Gg := Gg) q ⊢ unsetWhere (Gg := Gg) q' := by
  unfold unsetWhere
  apply BigSepM.bigSepM_mono
  intro k v _
  iintro H %hq
  iapply H
  ipureintro; exact h k hq

/-- Split the unset addresses by `p`. -/
theorem unsetWhere_split (q p : GoString → Prop) :
    unsetWhere (Gg := Gg) q ⊢
      unsetWhere (Gg := Gg) (fun a => q a ∧ ¬ p a) ∗ unsetWhere (Gg := Gg) (fun a => q a ∧ p a) := by
  unfold unsetWhere
  rw [← BigSepM.bigSepM_sep_eq]
  apply BigSepM.bigSepM_mono
  intro k v _
  iintro H
  by_cases hp : p k
  · isplitl []
    · iintro %h; exact absurd hp h.2
    · iintro %h; iapply H; ipureintro; exact h.1
  · isplitl [H]
    · iintro %h; iapply H; ipureintro; exact h.1
    · iintro %h; exact absurd h.2 hp

/-- Take out of the unset addresses those of the listeners at `las`, which take no address in
common (`lisUnset`). -/
theorem unsetWhere_lis : ∀ (las : List GoString) (q : GoString → Prop),
    (∀ la ∈ las, ∀ a, lisAccepts la a → q a) →
    las.Pairwise (fun l1 l2 => ∀ a, lisAccepts l1 a → ¬ lisAccepts l2 a) →
    unsetWhere (Gg := Gg) q ⊢ ([∗list] la ∈ las, lisUnset (Gg := Gg) la) ∗
      unsetWhere (Gg := Gg) (fun a => q a ∧ ∀ la ∈ las, ¬ lisAccepts la a)
  | [], q, _, _ => by
    iintro H
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    · iapply unsetWhere_mono (fun a h => h.1) $$ H
  | la :: las, q, hq, hpw => by
    iintro H
    icases unsetWhere_split q (lisAccepts la) $$ H with ⟨Hrest, Hla⟩
    have hq' : ∀ la' ∈ las, ∀ a, lisAccepts la' a → q a ∧ ¬ lisAccepts la a := by
      intro la' hla' a ha
      refine ⟨hq la' (List.mem_cons_of_mem _ hla') a ha, fun h => ?_⟩
      exact (List.pairwise_cons.1 hpw).1 la' hla' a h ha
    icases unsetWhere_lis las _ hq' (List.pairwise_cons.1 hpw).2 $$ Hrest with ⟨Hlas, Hrest⟩
    isplitl [Hla Hlas]
    · iapply BigSepL.bigSepL_cons.2
      isplitl [Hla]
      · unfold unsetWhere lisUnset
        iapply BigSepM.bigSepM_mono ?_ $$ Hla
        intro k v _
        iintro H %ha
        iapply H
        ipureintro; exact ⟨hq la List.mem_cons_self k ha, ha⟩
      · iexact Hlas
    · iapply unsetWhere_mono ?_ $$ Hrest
      intro a ⟨hqa, hall⟩
      exact ⟨⟨hqa, hall la List.mem_cons_self⟩, fun la' h => hall la' (List.mem_cons_of_mem _ h)⟩

/-- The extension's start resources: every address of a list of distinct valid addresses, unset,
and the addresses of each listener of a list (wildcards, or valid addresses), unset (`lisUnset`), if
no two of the listeners take an address in common and none takes an address of the list. -/
theorem addrs_lis_start (g : NetGlobal) (addrs las : List GoString) (hnd : addrs.Nodup)
    (hok : ∀ a ∈ addrs, addrOk a = true)
    (hlas : las.Pairwise (fun l1 l2 => ∀ a, lisAccepts l1 a → ¬ lisAccepts l2 a))
    (hdisj : ∀ a ∈ addrs, ∀ la ∈ las, ¬ lisAccepts la a) :
    netStart (NG (Gg := Gg)) g ⊢
      ([∗list] a ∈ addrs, addrUnset (Gg := Gg) a) ∗ [∗list] la ∈ las, lisUnset (Gg := Gg) la := by
  iintro H
  ihave H := start_unset g $$ H
  icases unsetWhere_lis las (fun _ => True) (fun _ _ _ _ => trivial) hlas $$ H with ⟨Hlas, H⟩
  iframe Hlas
  unfold unsetWhere
  ihave H := bigSepM_take_list (fun a (_ : Unit) => iprop(⌜True ∧ ∀ la ∈ las, ¬ lisAccepts la a⌝ →
      netPend (NG (Gg := Gg)) a ∅ ∗ netLisTok (NG (Gg := Gg)) a)) (fun _ => ())
    (addrSpace ()) addrs hnd (fun a ha => addrSpace_lookup_ok _ (hok a ha)) $$ H
  iapply BigSepL.bigSepL_mono (Φ := fun _ a => iprop(⌜True ∧ ∀ la ∈ las, ¬ lisAccepts la a⌝ →
      netPend (NG (Gg := Gg)) a ∅ ∗ netLisTok (NG (Gg := Gg)) a)) ?_ $$ H
  intro k a hk
  have ha := List.mem_of_getElem? hk
  have hq : True ∧ ∀ la ∈ las, ¬ lisAccepts la a := ⟨trivial, hdisj a ha⟩
  iintro H
  ihave ⟨Hp, Ht⟩ := H $$ %hq
  unfold addrUnset addrTok
  iframe Hp Ht
  ipureintro
  exact hok a ha


end start

end Net
end Perennial
