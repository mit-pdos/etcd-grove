/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Spec/network.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension (`Proto`, `addrProto`, `addrTok`, `sendTok` of
`GooseLang/Ext/Net/Proto.lean`; the sealed bodies in `Proof/network/Defs.lean` changed accordingly);
the configured addresses are `VsrWire.addrs`; the specs' shapes are the lab's.
-/
/-
Cross-package specs of `pkg/network`: the `*TCP` (`isTCP tcp γ me`, persistent), the right to
call `Send` (`tcpSender tcp`, exclusive: the one goroutine that sends), the addresses `Send`
may be given (`addrOk tcp a`: a configured address, or the source of a connection the TCP
accepted), the events `Recv` returns (`netEvOk`: a valid message's event, from an `addrOk`
source), and the send functions (`sendFn γ f R Q`: a one-shot callback: from the caller's frame `R`,
`f(w)` writes one valid line, or fails, and gives `Q`; `Send` calls it at most once and returns
`Q`, or `R` back with an error when it did not call it).
Specs: `NewTCP`, `Run`, `Send`, `Recv`, and `Send`/`Recv` through the `Network` interface
(`isNet`, `netSender`, `netAddrOk`).

Every connection's streams follow `protoOf γ` (the protocols of the configured addresses,
`netProtos γ`, persistent, which `Run` and `Send` take).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.events
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.queue
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.assert
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.network.Defs

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : network.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

/-- Every configured address's protocols are `protoOf γ` both ways (persistent; the wire's
`VsrWire.protos`, which the start gives each node). -/
def network.netProtos (γ : VsrGhost.Names) : IProp GF := VsrWire.protos γ

/-- The `*TCP` `tcp` at the configured address `me`, whose received events are valid messages
of `γ` (persistent).
-- sealed: the package's choice -/
def network.isTCP (tcp : Loc) (γ : VsrGhost.Names) (me : GoString) : IProp GF :=
  network.isTCPDef tcp γ me

/-- The right to call `tcp.Send` (exclusive: `Send` is called by one goroutine at a time).
-- sealed: the package's choice -/
def network.tcpSender (tcp : Loc) : IProp GF := network.tcpSenderDef tcp

/-- `tcp.Send` may be given the address `a`: its string is a configured address, or the key of
a connection `tcp` accepted (persistent).
-- sealed: the package's choice -/
def network.addrOk (tcp : Loc) (a : ipv4port.IPv4Port) : IProp GF :=
  network.addrOkDef tcp a

instance network.netProtos_persistent (γ : VsrGhost.Names) :
    Persistent (network.netProtos (GF := GF) γ) := by
  unfold network.netProtos VsrWire.protos; infer_instance
instance network.isTCP_persistent (tcp : Loc) (γ : VsrGhost.Names) (me : GoString) :
    Persistent (network.isTCP (GF := GF) tcp γ me) := by
  unfold network.isTCP; infer_instance
instance network.addrOk_persistent (tcp : Loc) (a : ipv4port.IPv4Port) :
    Persistent (network.addrOk (GF := GF) tcp a) := by
  unfold network.addrOk; infer_instance

/-- A configured address is `addrOk`. -/
theorem network.addrOk_cfg (tcp : Loc) (γ : VsrGhost.Names) (me : GoString)
    (a : ipv4port.IPv4Port) (s : GoString) (hs : ipv4port.ipOwn a s) (hc : s ∈ VsrWire.addrs) :
    network.isTCP (GF := GF) tcp γ me ⊢ network.addrOk tcp a := by
  unfold network.addrOk network.addrOkDef
  iintro -
  iexists s
  isplit
  · ipureintro; exact hs
  · ileft; ipureintro; exact hc

/-- An event `tcp` received (persistent): a valid message's event, from an `addrOk` source
(`Recv` gives its contents, with the payload's `Logs` capacity). -/
def network.netEvOk (γ : VsrGhost.Names) (tcp : Loc) (ev : events.NetworkEvent) :
    IProp GF :=
  iprop(∃ m : Msg, events.isEvent ev.Event' m ∗ VsrGhost.fact γ (.msg m) ∗
    network.addrOk tcp ev.Src')

instance network.netEvOk_persistent (γ : VsrGhost.Names) (tcp : Loc)
    (ev : events.NetworkEvent) : Persistent (network.netEvOk (GF := GF) γ tcp ev) := by
  unfold network.netEvOk; infer_instance

/-- The function value `f` (a `func(io.Writer) error`), called once with the caller's frame `R`,
writes to a stream of `γ` that is whole lines of valid messages: it returns an error and the
stream, whole lines again if the error is `nil`, and `Q` (not persistent: a one-shot callback;
the replica's closures read its fields, which `R` holds and `Q` gives back). -/
def network.sendFn (γ : VsrGhost.Names) (f : GoFunc) (R Q : IProp GF) :
    IProp GF :=
  iprop(∀ (w : GoInterface) (Φ : val → IProp GF),
    events.wstream γ w true -∗ R -∗
    ▷ (∀ err : GoInterface, events.wstream γ w (decide (err = interface.nil)) -∗
      bufio.errOrNil err -∗ Q -∗ Φ #err) -∗
    WP (App (Val #f) (Val #w)) {{ Φ }})

/-- The `Network` interface value `n` holds a `*TCP` (persistent). -/
def network.isNet (n : GoInterface) (γ : VsrGhost.Names) : IProp GF :=
  iprop(∃ (tcp : Loc) (me : GoString),
    ⌜n = interface.mkOk (go.GoType.PointerType network.TCP.ty) #tcp⌝ ∗ network.isTCP tcp γ me)

/-- The right to call `n.Send` (`tcpSender` of the `*TCP` it holds). -/
def network.netSender (n : GoInterface) : IProp GF :=
  iprop(∃ tcp : Loc, ⌜n = interface.mkOk (go.GoType.PointerType network.TCP.ty) #tcp⌝ ∗
    network.tcpSender tcp)

/-- `n.Send` may be given `a` (`addrOk` of the `*TCP` it holds; persistent). -/
def network.netAddrOk (n : GoInterface) (a : ipv4port.IPv4Port) : IProp GF :=
  iprop(∃ tcp : Loc, ⌜n = interface.mkOk (go.GoType.PointerType network.TCP.ty) #tcp⌝ ∗
    network.addrOk tcp a)

/-- A configured address is `netAddrOk` of a network. -/
theorem network.netAddrOk_cfg (n : GoInterface) (γ : VsrGhost.Names) (a : ipv4port.IPv4Port)
    (s : GoString) (hs : ipv4port.ipOwn a s) (hc : s ∈ VsrWire.addrs) :
    network.isNet (GF := GF) n γ ⊢ network.netAddrOk n a := by
  unfold network.isNet network.netAddrOk
  iintro ⟨%tcp, %me, %hn, H⟩
  iexists tcp
  isplit
  · ipureintro; exact hn
  · iapply network.addrOk_cfg tcp γ me a s hs hc $$ H

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : network.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]
variable [models_lab.jsoncodec.JsonCodec GF]

set_option goose.wp.extras true

/-- `NewTCP(me)`, `me` a configured address: a `*TCP` at `me` (for any `γ`) and its sender
right. What its connections' readers (`handleConn`: `FromDecoder`) need is given here and kept
in `isTCP`: the G1 hook set (`events.frameDecoderSet`, D8), the JSON codec registered
(scanner `F`); `ErrNoConn`'s value (`errors.newVar`, D10: the package's state, which a spec over an
arbitrary package state cannot derive). -/
abbrev network.NewTCP.spec : Prop :=
  ∀ (F : List w8 → Bool → w64 × w64) (me : GoString) (γ : VsrGhost.Names), me ∈ VsrWire.addrs →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.network ∗
      events.frameDecoderSet ∗
      encoding.json.codecSet (GF := GF) ∗ encoding.json.kitCodecOk F ∗
      errors.newVar (GF := GF) network.ErrNoConn
        go!"network: no connection to the source address" }}
    (App (Val (@! network.NewTCP)) (Val #me))
  {{ (tcp : Loc), RET #tcp; network.isTCP tcp γ me ∗ network.tcpSender tcp }}

/-- `tcp.Run()`: listens at `me` (its token) and serves the connections it accepts. -/
abbrev network.TCP.Run.spec : Prop :=
  ∀ (tcp : Loc) (γ : VsrGhost.Names) (me : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.network ∗
      network.isTCP tcp γ me ∗ addrTok me ∗ network.netProtos γ }}
    (App (Val (tcp @!! go.GoType.PointerType network.TCP.ty @!! go!"Run")) (Val #()))
  {{ (err : GoInterface), RET #err; True }}

/-- `tcp.Send(a, f)`: `f` run once on a connection to `a` (dialed, or kept) with the frame `R`,
giving `Q`; or `f` not run (the dial failed, or `a` is an ended accepted source: `ErrNoConn`),
an error and `R` back. The error is `nil` or an error whose `Error()` returns some string
(`bufio.errOrNil`: what logging it with `slog` needs; D6). -/
abbrev network.TCP.Send.spec : Prop :=
  ∀ (tcp : Loc) (γ : VsrGhost.Names) (me : GoString) (a : ipv4port.IPv4Port) (f : GoFunc)
    (R Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.network ∗
      network.isTCP tcp γ me ∗ network.tcpSender tcp ∗ network.addrOk tcp a ∗
      network.sendFn γ f R Q ∗ R ∗ network.netProtos γ }}
    (App (App (Val (tcp @!! go.GoType.PointerType network.TCP.ty @!! go!"Send")) (Val #a))
      (Val #f))
  {{ (err : GoInterface), RET #err; network.tcpSender tcp ∗ bufio.errOrNil err ∗
      (Q ∨ (⌜err ≠ interface.nil⌝ ∗ R)) }}

/-- `tcp.Recv()`: `(ev, true)`, a received event (with its payload's `Logs` capacity), or
`(_, false)`. -/
abbrev network.TCP.Recv.spec : Prop :=
  ∀ (tcp : Loc) (γ : VsrGhost.Names) (me : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.network ∗
      network.isTCP tcp γ me }}
    (App (Val (tcp @!! go.GoType.PointerType network.TCP.ty @!! go!"Recv")) (Val #()))
  {{ (ev : events.NetworkEvent) (ok : Bool), RET (PairV #ev #ok);
      if ok then ∃ m : Msg, events.isEvent ev.Event' m ∗ VsrGhost.fact γ (.msg m) ∗
        network.addrOk tcp ev.Src' ∗ events.evCap ev.Event' m
      else True }}

/-- `n.Send(a, f)` through the `Network` interface (as the code calls it: `MethodResolve` on the
interface value, D7): as `TCP.Send` (its error `bufio.errOrNil`, D6). -/
abbrev network.Network.Send.spec : Prop :=
  ∀ (n : GoInterface) (γ : VsrGhost.Names) (a : ipv4port.IPv4Port) (f : GoFunc)
    (R Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.network ∗
      network.isNet n γ ∗ network.netSender n ∗ network.netAddrOk n a ∗
      network.sendFn γ f R Q ∗ R ∗ network.netProtos γ }}
    (App (App (App (Val (GoInstruction (MethodResolve network.Network.ty go!"Send"))) (Val #n))
      (Val #a)) (Val #f))
  {{ (err : GoInterface), RET #err; network.netSender n ∗ bufio.errOrNil err ∗
      (Q ∨ (⌜err ≠ interface.nil⌝ ∗ R)) }}

/-- `n.Recv()` through the `Network` interface (as the code calls it: `MethodResolve` on the
interface value, D7): as `TCP.Recv`. -/
abbrev network.Network.Recv.spec : Prop :=
  ∀ (n : GoInterface) (γ : VsrGhost.Names),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.network ∗
      network.isNet n γ }}
    (App (App (Val (GoInstruction (MethodResolve network.Network.ty go!"Recv"))) (Val #n))
      (Val #()))
  {{ (ev : events.NetworkEvent) (ok : Bool), RET (PairV #ev #ok);
      if ok then ∃ (tcp : Loc) (m : Msg),
          ⌜n = interface.mkOk (go.GoType.PointerType network.TCP.ty) #tcp⌝ ∗
          events.isEvent ev.Event' m ∗ VsrGhost.fact γ (.msg m) ∗
          network.addrOk tcp ev.Src' ∗ events.evCap ev.Event' m
      else True }}

end spec

end Perennial.github_com.tangledbytes.go_vsr.pkg
