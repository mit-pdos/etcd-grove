/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/network/Defs.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension. What changed: a registered connection's record
is `(cn, s, key)` with the net extension's `Nat` connection id (`ConnRec`), and its end is
`net.connAt c cn s a la ra` (persistent, some dialed address `a` and local/remote addresses) instead
of the lab's `net.ownTCPConn c cid side`; `sendTok` is `GooseLang/Ext/Net/Proto.lean`'s; the
configured addresses are `VsrWire.addrs`; the readers' `rstream` is over the JSON vocabulary's
decoder (`Spec/events.lean`).
-/
/-
The network package's internal representation (the bodies of the sealed `isTCP`,
`tcpSender`, `addrOk` of `VsrProof/Spec/network.lean`).

**Ghost names** (`network.TcpNames`): the registry `reg` (ghost map, persistent elements: every
connection `c` this TCP put in its map, with its id, end and key), the sender's set `held` (ghost
map, persistent elements: the connections whose send token the sender holds), the dead set
`dead` (ghost map, persistent elements: the connections whose write failed; never in the map
again), the learned sources `src` (ghost map, persistent elements: the keys of accepted
connections, which `srcs` holds), and the system's names `sys`.

**The names of a TCP** are fixed by the TCP: `rootInv tcp ns` holds three quarters of the `mu`
field's points-to in an invariant whose namespace encodes `ns`; two such invariants of the same
TCP with different names could be opened together and would hold 3/2 of the field
(`rootInv_agree`). So the persistent `addrOk tcp a`, `isTCP tcp γ me`, `tcpSender tcp` agree on
the names.

**The lock** (`lockP ns cm sm q`, fractional: the `RWMutex`'s guarded resource): the two maps
(`conns`, `srcs`), the authorities of `dead` and `src`; every entry of `conns` is a registered
connection under its own key, not dead; every learned source is in `srcs`; every dead
connection is registered.

**The registry** (`regInv ns`, an invariant): the authority of `reg`; per registered connection
its fresh token (so a connection is registered once), its end, and its send token if the sender
has not taken it yet (else the persistent `held` element).

**The sender** (`tcpSender`): a reader slot of the lock, the authority of `held` and, per held
connection, its send token, whose stream is whole lines of valid messages or the connection is
dead.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.events
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.queue
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.assert
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.network.Base
public import Perennial.Proof.sync.RWMutexGuard
public import Perennial.Ghost.GhostMap

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The ghost names of a TCP. -/
structure network.TcpNames where
  reg : GName
  held : GName
  dead : GName
  src : GName
  sys : VsrGhost.Names

/-- The names as a list (for the root invariant's namespace). -/
def network.TcpNames.toList (ns : network.TcpNames) : List Nat :=
  [ns.reg, ns.held, ns.dead, ns.src, ns.sys.facts, ns.sys.reps, ns.sys.abs, ns.sys.next,
    ns.sys.regm, ns.sys.regt, ns.sys.size]

theorem network.TcpNames.toList_inj {a b : network.TcpNames} (h : a.toList = b.toList) :
    a = b := by
  obtain ⟨r, h1, d, s, ⟨f, rp, ab, nx, rm, rt, sz⟩⟩ := a
  obtain ⟨r', h1', d', s', ⟨f', rp', ab', nx', rm', rt', sz'⟩⟩ := b
  simp only [network.TcpNames.toList, List.cons.injEq, and_true] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  rfl

/-- A registered connection's record: its id (the net extension's), its end, its key in `conns`. -/
abbrev network.ConnRec := Nat × Bool × GoString

def network.rootN (ns : network.TcpNames) : Namespace :=
  ndot (ndot (ndot nroot "vsr") "tcproot") ns.toList
def network.regN : Namespace := ndot (ndot nroot "vsr") "tcpreg"

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : network.Assumptions] [π : NetProtoGS]

/-- The `tcp.mu` field. -/
abbrev network.muField (tcp : Loc) : Loc := structFieldRef network.TCP go!"mu" tcp

/-- The names of `tcp` are `ns` (persistent; they agree: `rootInv_agree`). -/
def network.rootInv (tcp : Loc) (ns : network.TcpNames) : IProp GF :=
  inv (network.rootN ns) iprop(∃ mu : Loc,
    typedPointsto (GF := GF) (network.muField (GF := GF) tcp) mu
      (DFrac.own ((1 : Qp).half + (1 : Qp).half.half)))

/-- `c` is registered with record `x` (persistent). -/
abbrev network.regd (ns : network.TcpNames) (c : Loc) (x : network.ConnRec) : IProp GF :=
  ghostMapElem ns.reg c DFrac.discard x

/-- The sender holds `c`'s send token (persistent). -/
abbrev network.heldMark (ns : network.TcpNames) (c : Loc) : IProp GF :=
  ghostMapElem ns.held c DFrac.discard ()

/-- `c`'s write failed: it is dead (persistent). -/
abbrev network.deadMark (ns : network.TcpNames) (c : Loc) : IProp GF :=
  ghostMapElem ns.dead c DFrac.discard ()

/-- `s` is the key of an accepted connection (persistent). -/
abbrev network.srcMark (ns : network.TcpNames) (s : GoString) : IProp GF :=
  ghostMapElem ns.src s DFrac.discard ()

/-- The entry `k ↦ v` of `conns` (persistent): a registered connection under its key, not
dead. -/
abbrev network.entryOk (ns : network.TcpNames) (D : GMap Loc Unit) (k : GoString)
    (v : GoInterface) : IProp GF :=
  iprop(∃ (c : Loc) (x : network.ConnRec),
    ⌜v = interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c ∧ x.2.2 = k ∧
      D.lookup c = none⌝ ∗ network.regd ns c x)

/-- The lock's resource (fraction `q`). -/
abbrev network.lockP (ns : network.TcpNames) (cm sm : Loc) (q : Qp) : IProp GF :=
  iprop(∃ (mc : GMap GoString GoInterface) (ms : GMap GoString Bool) (D : GMap Loc Unit)
      (S : GMap GoString Unit),
    ownMap cm (DFrac.own q) mc ∗ ownMap sm (DFrac.own q) ms ∗
    ghostMapAuth ns.dead q D ∗ ghostMapAuth ns.src q S ∗
    ⌜∀ s, S.lookup s = some () → ms !! s = some true⌝ ∗
    ([∗map] k ↦ v ∈ mc, network.entryOk ns D k v) ∗
    ([∗map] c ↦ _u ∈ D, network.deadMark ns c ∗ ∃ x, network.regd ns c x) ∗
    ([∗map] s ↦ _u ∈ S, network.srcMark ns s))

/-- A whole stream: the lines of valid messages with plain strings, within the bounds (as
`events.wstream` says). -/
def network.wholeLines (γ : VsrGhost.Names) (W : List w8) : IProp GF :=
  iprop(∃ ms : List Msg, ⌜W = VsrWire.lines ms⌝ ∗
    ⌜∀ m ∈ ms, PlainMsg m ∧ MsgBound m ∧ (VsrWire.line m).length < 2 ^ 60⌝ ∗
    [∗list] m ∈ ms, VsrGhost.fact γ (.msg m))

/-- A registered connection in the registry. -/
def network.regEntry (ns : network.TcpNames) (c : Loc) (x : network.ConnRec) :
    IProp GF :=
  iprop(connFresh x.1 x.2.1 ∗ (∃ (a : GoString) (la ra : GoInterface), net.connAt c x.1 x.2.1 a la ra) ∗
    (sendTok x.1 x.2.1 (VsrWire.protoOf ns.sys) [] ∨ network.heldMark ns c))

/-- The registry's invariant. -/
def network.regInv (ns : network.TcpNames) : IProp GF :=
  iprop(∃ R : GMap Loc network.ConnRec, ghostMapAuth ns.reg 1 R ∗
    [∗map] c ↦ x ∈ R, network.regEntry ns c x)

/-- A connection the sender holds. -/
def network.poolEntry (ns : network.TcpNames) (c : Loc) : IProp GF :=
  iprop(∃ (x : network.ConnRec) (W : List w8), network.regd ns c x ∗
    (∃ (a : GoString) (la ra : GoInterface), net.connAt c x.1 x.2.1 a la ra) ∗ sendTok x.1 x.2.1 (VsrWire.protoOf ns.sys) W ∗
    (network.wholeLines ns.sys W ∨ network.deadMark ns c))

/-- The fields of `tcp`, read-only (all but three quarters of `mu`, which `rootInv` has). -/
def network.fieldsRO (tcp : Loc) (v : network.TCP) : IProp GF :=
  iprop(typedPointsto (structFieldRef network.TCP go!"ip" tcp) v.ip' DFrac.discard ∗
    typedPointsto (structFieldRef network.TCP go!"conns" tcp) v.conns' DFrac.discard ∗
    typedPointsto (structFieldRef network.TCP go!"srcs" tcp) v.srcs' DFrac.discard ∗
    typedPointsto (structFieldRef network.TCP go!"queue" tcp) v.queue' DFrac.discard ∗
    typedPointsto (structFieldRef network.TCP go!"mu" tcp) v.mu' DFrac.discard)

/-- `addrOk` (the sealed definition's body). -/
def network.addrOkDef (tcp : Loc) (a : ipv4port.IPv4Port) : IProp GF :=
  iprop(∃ s : GoString, ⌜ipv4port.ipOwn a s⌝ ∗
    (⌜s ∈ VsrWire.addrs⌝ ∨ ∃ ns, network.rootInv tcp ns ∗ network.srcMark ns s))

/-- `a` is a configured address or a source learned by the TCP with names `ns` (persistent;
`addrOkDef` with the names given: what the queue's elements carry, whose predicate is fixed
before the `*TCP` is allocated). -/
def network.addrOkN (ns : network.TcpNames) (a : ipv4port.IPv4Port) : IProp GF :=
  iprop(∃ s : GoString, ⌜ipv4port.ipOwn a s⌝ ∗ (⌜s ∈ VsrWire.addrs⌝ ∨ network.srcMark ns s))

/-- A queued event: a valid message's, from an `addrOkN` source, with its capacity. -/
def network.evOk (ns : network.TcpNames) (ev : events.NetworkEvent) :
    IProp GF :=
  iprop(∃ m : Msg, events.isEvent ev.Event' m ∗ VsrGhost.fact ns.sys (.msg m) ∗
    network.addrOkN ns ev.Src' ∗ events.evCap ev.Event' m)

end defs

section defs2
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : network.Assumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

/-- What the readers need (persistent): `FromDecoder` on a decoder of `γ`'s stream (what
`NewTCP`'s precondition gives, `events.Event.FromDecoder.spec`, kept as a triple: `isTCP`'s
definition cannot mention the package states). -/
def network.readerOk (γ : VsrGhost.Names) : IProp GF :=
  iprop(□ ∀ (ev dec : Loc) (e0 : events.Event) (Φ : val → IProp GF),
    events.rstream γ dec ∗ ev ↦ e0 -∗
    ▷ (∀ err : GoInterface, events.rstream γ dec ∗
        bufio.errOrNil err ∗
        (if decide (err = interface.nil) then ∃ m : Msg, events.isEvent ev m ∗
          events.evCap ev m ∗ VsrGhost.fact γ (.msg m)
        else ∃ e : events.Event, ev ↦ e) -∗ Φ #err) -∗
    WP (App (Val (ev @!! go.GoType.PointerType events.Event.ty @!! go!"FromDecoder"))
      (Val #dec)) {{ Φ }})

/-- The TCP's shared state with names `ns` and fields `v` (persistent). -/
def network.tcpCore (tcp : Loc) (ns : network.TcpNames) (v : network.TCP) : IProp GF :=
  iprop(network.fieldsRO tcp v ∗ network.rootInv tcp ns ∗
    sync.isRWMutexGuard v.mu' (network.lockP ns v.conns' v.srcs') ∗
    inv network.regN (network.regInv ns) ∗
    queue.isQueue events.NetworkEvent.ty v.queue' (network.evOk ns))

/-- `isTCP` (the sealed definition's body). -/
def network.isTCPDef (tcp : Loc) (γ : VsrGhost.Names) (me : GoString) : IProp GF :=
  iprop(∃ (ns : network.TcpNames) (v : network.TCP), ⌜ns.sys = γ⌝ ∗
    network.tcpCore tcp ns v ∗ ipv4port.ipCfg v.ip' me ∗ network.readerOk γ ∗
    errors.newVar network.ErrNoConn go!"network: no connection to the source address")

/-- `tcpSender` (the sealed definition's body). -/
def network.tcpSenderDef (tcp : Loc) : IProp GF :=
  iprop(∃ (ns : network.TcpNames) (v : network.TCP) (T : GMap Loc Unit),
    network.fieldsRO tcp v ∗ network.rootInv tcp ns ∗
    sync.ownRWMutex v.mu' (network.lockP ns v.conns' v.srcs') ∗
    ghostMapAuth ns.held 1 T ∗ [∗map] c ↦ _u ∈ T, network.poolEntry ns c)

end defs2

end Perennial.github_com.tangledbytes.go_vsr.pkg

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

section insts
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : network.Assumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

instance network.rootInv_persistent (tcp : Loc) (ns : network.TcpNames) :
    Persistent (network.rootInv (GF := GF) tcp ns) := by
  unfold network.rootInv; infer_instance

instance network.entryOk_persistent (ns : network.TcpNames) (D : GMap Loc Unit) (k : GoString)
    (v : GoInterface) : Persistent (network.entryOk (GF := GF) ns D k v) := by
  unfold network.entryOk; infer_instance

instance network.fieldsRO_persistent (tcp : Loc) (v : network.TCP) :
    Persistent (network.fieldsRO (GF := GF) tcp v) := by
  unfold network.fieldsRO; infer_instance

instance network.addrOkN_persistent (ns : network.TcpNames) (a : ipv4port.IPv4Port) :
    Persistent (network.addrOkN (GF := GF) ns a) := by
  unfold network.addrOkN; infer_instance

instance network.addrOkDef_persistent (tcp : Loc) (a : ipv4port.IPv4Port) :
    Persistent (network.addrOkDef (GF := GF) tcp a) := by
  unfold network.addrOkDef; infer_instance

instance network.readerOk_persistent (γ : VsrGhost.Names) :
    Persistent (network.readerOk (GF := GF) γ) := by
  unfold network.readerOk; infer_instance

instance network.tcpCore_persistent (tcp : Loc) (ns : network.TcpNames) (v : network.TCP) :
    Persistent (network.tcpCore (GF := GF) tcp ns v) := by
  unfold network.tcpCore; infer_instance

instance network.isTCPDef_persistent (tcp : Loc) (γ : VsrGhost.Names) (me : GoString) :
    Persistent (network.isTCPDef (GF := GF) tcp γ me) := by
  unfold network.isTCPDef; infer_instance

end insts

end Perennial.github_com.tangledbytes.go_vsr.pkg
