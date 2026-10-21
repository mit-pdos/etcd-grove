/-
**The bridge's protocol** (`third_party/bridge`, etcd's test bridge; `notes/client-cut-plan.md`
K2; Lean-first, no Rocq counterpart). A bridge `b` accepts on a relay's listener (`relayListener`,
`Proof/net/InvRelay.lean`) and, per accepted connection, dials the relay's address, records a
`*bridgeConn` `c` in its map `b.conns` and starts `serveConn(c)`, whose two goroutines copy bytes
each way (`ioCopy`) until a copy fails or the bridge is blackholed. The specs are safety specs:
no panic, no data race; nothing about the bytes but what the relay's specs ask (each direction
writes what it read).

**The mutex `b.mu` guards** (`lockInv`): the map `b.conns` and its keys; the channel `b.pausec`;
the flag "blackholed" (`γ.holed`, half here, half the owner's: `bridgeHoled`), with the closer's
view of `b.blackholec` while it is not (so `Blackhole`, which closes it unguarded, is called once
per `Unblackhole`: `issues/etcd-bridge-blackhole-twice-panic.md`); and a fraction of the field
`b.blackholec`.

**`b.blackholec` is read without the mutex**, by every copy goroutine of every registered
connection (`ioCopy`'s `select`), and written by `Unblackhole` under it. Go is race-free here
because `Unblackhole` closes every registered connection and waits for its `donec`, closed once
its copy goroutines are done, before the write. So: registering `c` splits the lock's fraction
`q` of the field in two halves, one for `c`'s goroutines (`shares`, `c`'s entry: the half and a
claim `token`); when they are done, `serveConn` deposits the half in an invariant (`doneQ`) and
closes `donec` with it; whoever removes `c` from the map (`Unblackhole`, `DropConnections`, or
`serveConn` itself) waits on `donec`, trades the claim token for the half and gives it back to the
lock. The lock holds a wand from its fraction and every outstanding share to the whole field
(`Hwand`), so that once the map is empty, `Unblackhole` holds the field whole.

**The wait group `b.wg`** counts `serveListen` and every `serveConn`; nobody waits on it here
(`Close` is not verified). Its counter's bound is by thread tokens, as the server's `GoAttach`
(`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvGoAttach.lean`): each `serveConn` is counted by
the thread token `serveListen` deposits at its `Add`, which the `go` statement gives back fresh.
`serveListen` itself is counted by a flag (`γ.sl`), not a token: `newBridge`'s caller keeps its
own token, and the `go` statement's fresh token goes to `serveListen`, which needs one for its
first `Add`. So the counter is at most the deposited tokens plus one, below `threadBound GF + 1`
(`wgInv`; a premise, `threadBound GF + 1 ≤ 2 ^ 31`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.third_party.bridge.Base
public import Proof.net.InvRelay
public import Perennial.Proof.sync
public import Perennial.Ghost.Token
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bridgeP

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.third_party

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- A field of the bridge `b`. -/
abbrev bF (b : Loc) (f : GoString) : Loc := structFieldRef bridge.bridge f b

end addrs

/-- The ghost names of a bridge: the flag "blackholed", the wait group's, the started
`serveConn`s' receipts, and the flag "`serveListen` runs". -/
structure BridgeNames where
  holed : GName
  wg : sync.WaitGroupNames
  run : GName
  sl : GName

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The wait group's namespace (`sync.isWaitGroup`). -/
def bridgeWGN : Namespace := nroot.@"bridgeWaitGroup"
/-- The counter's invariant's namespace (`wgInv`). -/
def bridgeWgInvN : Namespace := nroot.@"bridgeWgInv"
/-- The namespace of a connection's deposit (`doneQ`). -/
def bridgeDoneN : Namespace := nroot.@"bridgeDone"

theorem bridgeWG_mask : (↑bridgeWGN : CoPset) ⊆ ⊤ \ ↑bridgeWgInvN :=
  sync.wg_mask_ndot_ne nroot "bridgeWaitGroup" "bridgeWgInv" (by decide)

theorem bridgeWgInvN_mask : (↑bridgeWgInvN : CoPset) ⊆ ⊤ \ ↑bridgeWGN :=
  sync.wg_mask_ndot_ne nroot "bridgeWgInv" "bridgeWaitGroup" (by decide)

/-- **The wait group's counter** (an invariant): the counter `ctr`, `k` `serveConn`s started
(their receipts' authority) with their thread tokens deposited, and `serveListen` if it runs
(half the flag `s`); no waiter. -/
def wgInv (γ : BridgeNames) : IProp GF :=
  iprop(∃ (ctr : w32) (k : Nat) (s : Bool), sync.ownWaitGroup γ.wg ctr ∗ threadToks k ∗
    ownTokAuth γ.run k ∗ ghostVar γ.sl (1 : Qp).half s ∗
    ⌜0 ≤ sint.Z ctr ∧ sint.nat ctr = k + (if s then 1 else 0)⌝ ∗
    sync.ownWaitGroupWaiters γ.wg 0)

/-- A started `serveConn`'s receipt (its `Done` takes a deposited thread token back). -/
def wgRunning (γ : BridgeNames) : IProp GF := ownToks γ.run 1

/-- `serveListen`'s receipt: the other half of the flag, at `true`. -/
def slRunning (γ : BridgeNames) : IProp GF := ghostVar γ.sl (1 : Qp).half true

/-- **A connection's deposit** (persistent; the `Q` its `donec` is closed with): an invariant
holding, once its goroutines are done, their share `q` of `b.blackholec`, or the claim token
`γt` of whoever took it. -/
def doneQ (b : Loc) (q : Qp) (γt : GName) : IProp GF :=
  inv bridgeDoneN iprop(token γt ∨ ∃ ch : GoChan, bF b go!"blackholec" ↦{DFrac.own q} ch)

instance doneQ_persistent (b : Loc) (q : Qp) (γt : GName) :
    Persistent (doneQ (GF := GF) b q γt) := by
  unfold doneQ; infer_instance

/-- **The connection `c` of the bridge `b`** (persistent): its fields (never written after
`serveListen` makes it), its two connections, and its `donec` (closed with `doneQ b q γt`). -/
def connOk (b c : Loc) (q : Qp) (γt : GName) : IProp GF :=
  iprop(∃ (inc outc : GoInterfaceOk) (donec : GoChan) (γd : ChanNames),
    c ↦□ (bridge.bridgeConn.mk (interface.ok inc) (interface.ok outc) donec) ∗
    netConnOk inc ∗ netConnOk outc ∗ ownBroadcastChan donec γd (doneQ b q γt) .Unknown)

instance connOk_persistent (b c : Loc) (q : Qp) (γt : GName) :
    Persistent (connOk (GF := GF) b c q γt) := by
  unfold connOk; infer_instance

/-- The registered connections' shares of `b.blackholec` (at the channel `ch`). -/
def sharesPts (b : Loc) (ch : GoChan) (shares : GMap Loc (Qp × GName)) : IProp GF :=
  iprop([∗map] _c ↦ x ∈ shares, bF b go!"blackholec" ↦{DFrac.own x.1} ch)

/-- **The mutex's resource** (see the file header). -/
def lockInv (b : Loc) (γ : BridgeNames) : IProp GF :=
  iprop(∃ (m : GoMap) (conns : GMap Loc Unit) (shares : GMap Loc (Qp × GName))
      (pc bhc : GoChan) (γpc γbh : ChanNames) (holed : Bool) (q : Qp),
    "Hconns" ∷ bF b go!"conns" ↦ m ∗ "Hm" ∷ m ↦$ conns ∗
    "%Hdom" ∷ ⌜∀ c, (conns !! c).isSome = (shares !! c).isSome⌝ ∗
    "Hpausec" ∷ bF b go!"pausec" ↦ pc ∗
    "#Hpc" ∷ ownBroadcastChan pc γpc iprop(True) .Unknown ∗
    "Hpcst" ∷ (ownBroadcastChan pc γpc iprop(True) .Pending ∨
      ownBroadcastChan pc γpc iprop(True) .Done) ∗
    "Hbh" ∷ bF b go!"blackholec" ↦{DFrac.own q} bhc ∗
    "#Hbhc" ∷ ownBroadcastChan bhc γbh iprop(True) .Unknown ∗
    "Hholed" ∷ ghostVar γ.holed (1 : Qp).half holed ∗
    "Hbhst" ∷ (if holed then iprop(True) else ownBroadcastChan bhc γbh iprop(True) .Pending) ∗
    "Hwand" ∷ (bF b go!"blackholec" ↦{DFrac.own q} bhc ∗ sharesPts b bhc shares -∗
      bF b go!"blackholec" ↦ bhc) ∗
    "Hregs" ∷ [∗map] c ↦ x ∈ shares, connOk b c x.1 x.2 ∗ token x.2)

/-- **The bridge `b`, to the relay address `addr`** (persistent): the fields written once by
`newBridge` (its dialer, to `addr`; its listener, a relay's to `addr`; `stopc`), the mutex with
its resource, the wait group with its counter's invariant, and the bound on live goroutines. -/
def isBridge (b : Loc) (γ : BridgeNames) (addr : GoString) : IProp GF :=
  iprop(∃ (l : GoInterfaceOk) (sc : GoChan) (γsc : ChanNames),
    bF b go!"dialer" ↦□
      (interface.mkOk bridge.dialer.ty #(bridge.dialer.mk go!"tcp" addr) : GoInterface) ∗
    bF b go!"l" ↦□ (interface.ok l : GoInterface) ∗ relayListener l addr ∗
    bF b go!"stopc" ↦□ sc ∗ ownBroadcastChan sc γsc iprop(True) .Unknown ∗
    sync.isMutex (bF b go!"mu") (lockInv b γ) ∗
    sync.isWaitGroup (bF b go!"wg") γ.wg bridgeWGN ∗ inv bridgeWgInvN (wgInv γ) ∗
    ⌜threadBound GF + 1 ≤ 2 ^ 31⌝)

instance isBridge_persistent (b : Loc) (γ : BridgeNames) (addr : GoString) :
    Persistent (isBridge (GF := GF) b γ addr) := by
  unfold isBridge; infer_instance

/-- **The owner's half of the flag "blackholed"**: `h` (exclusive). -/
def bridgeHoled (γ : BridgeNames) (h : Bool) : IProp GF := ghostVar γ.holed (1 : Qp).half h

/-- **A bridge, as the `Bridge` interface `br` its `New` returns, to `addr`, its owner's flag
`h`** (exclusive: the flag). -/
def ownBridge (br : GoInterface) (addr : GoString) (h : Bool) : IProp GF :=
  iprop(∃ (b : Loc) (γ : BridgeNames),
    ⌜br = interface.mkOk (go.GoType.PointerType bridge.bridge.ty) #b⌝ ∗ isBridge b γ addr ∗
    bridgeHoled γ h)

end defs

end bridgeP
end EtcdGrove
end Perennial
