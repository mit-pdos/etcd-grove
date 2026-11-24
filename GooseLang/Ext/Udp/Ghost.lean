/-
The ghost state of the UDP extension (`Impl.lean`) and its interpretation (`ExtInterp`). Its
resources are the extension's state, piece by piece, and nothing else.

**The network's resources** (global, in the one `AllG GF` of the ghost state, `UdpGS`):
`udpSent a ms` (exclusive, one per valid address, `addrOk`, from the start resources: the valid
addresses are finitely many, `Deploy.lean`'s `addrSpace`): the datagrams sent to `a` are `ms`.
`Send` adds to it and `Recv` reads it, as logically atomic steps (`Specs.lean`), so a program keeps
it in an invariant with what it promises about the datagrams sent to `a` (the per-address protocol:
every member satisfies it, so every datagram received does).

**The node's resources** (local): `udpSock s a` (persistent): the socket `s` of this node exists,
bound to `a`. Sockets are never closed (U12), so a socket's resource is persistent and may be used
by any number of threads at once (a sender and a receiver of one socket).

**Crashes**: the network's resources are global and survive a crash, as the network does. The
sockets' ghost map is the node's, made anew at a crash (no socket survives, U7).

**The interpretation holds only what the state determines** (no mode, no history): the ghost map of
the datagrams is the network's `sentTo` at every valid address; the sockets' ghost map is the node's
sockets.
-/
module

public import Perennial.GooseLang.Lifting
public import Perennial.Ghost.GhostMap
public import GooseLang.Ext.Net.Deploy
public import GooseLang.Ext.Udp.Impl

@[expose] public section

noncomputable section

namespace Perennial
namespace Udp

open Iris Iris.BI Iris.Std ProofMode Net

/-- The global ghost state: the universal camera and the ghost map of the datagrams sent to each
valid address. -/
structure UdpGS (GF : BundledGFunctors) where
  allG : AllG GF
  γsent : GName

/-- The local ghost state: the universal camera and the ghost map of the node's sockets (persistent
entries: a socket's address never changes). -/
structure UdpLocalGS (GF : BundledGFunctors) where
  allG : AllG GF
  γsock : GName

/-- What the adequacy theorem provides: the universal camera. -/
structure UdpGpreS (GF : BundledGFunctors) where
  allG : AllG GF

section defs
variable {GF : BundledGFunctors}

/-- The ghost map of the datagrams agrees with the network: it has exactly the valid addresses,
each with the datagrams sent to it. -/
def SentOk (g : UdpGlobal) (sm : GMap GoString (List (List w8))) : Prop :=
  (∀ a, (sm !! a).isSome = addrOk a) ∧ (∀ a ms, sm !! a = some ms → ms = g.sentTo a)

/-- The interpretation of the network. -/
def udpCtx (hG : UdpGS GF) (g : UdpGlobal) : IProp GF :=
  letI := hG.allG
  iprop(∃ sm, ghostMapAuth hG.γsent 1 sm ∗ ⌜SentOk g sm⌝)

/-- The interpretation of a node: its sockets are those of the ghost map. -/
def udpLocalCtx (hL : UdpLocalGS GF) (L : UdpLocal) : IProp GF :=
  letI := hL.allG; ghostMapAuth hL.γsock 1 L.socks

/-- The datagrams sent to `a` are `ms` (exclusive). -/
def udpSent (hG : UdpGS GF) (a : GoString) (ms : List (List w8)) : IProp GF :=
  letI := hG.allG; ghostMapElem hG.γsent a (.own 1) ms

/-- The socket `s` of this node exists, bound to `a` (persistent). -/
def udpSock (hL : UdpLocalGS GF) (s : w64) (a : GoString) : IProp GF :=
  letI := hL.allG; ghostMapElem hL.γsock s .discard a

instance udpSent_timeless (hG : UdpGS GF) a ms : Timeless (udpSent hG a ms) := by
  unfold udpSent; infer_instance
instance udpSock_timeless (hL : UdpLocalGS GF) s a : Timeless (udpSock hL s a) := by
  unfold udpSock; infer_instance
instance udpSock_persistent (hL : UdpLocalGS GF) s a : Persistent (udpSock hL s a) := by
  unfold udpSock; infer_instance

end defs

/-! ## Initialization -/

section init
variable {GF : BundledGFunctors}

/-- The start resources of the network: every valid address's datagrams, none. -/
def udpStart (hG : UdpGS GF) (_g : UdpGlobal) : IProp GF :=
  [∗map] a ↦ ms ∈ addrSpace ([] : List (List w8)), udpSent hG a ms

theorem sentOk_init (g : UdpGlobal) (h : g.sent = ∅) : SentOk g (addrSpace []) := by
  refine ⟨fun a => addrSpace_lookup_isSome _ a, fun a ms hms => ?_⟩
  obtain rfl := addrSpace_lookup_some hms
  simp [UdpGlobal.sentTo, h]

theorem udp_global_init (hPre : UdpGpreS GF) (g : UdpGlobal) (hg : g.sent = ∅) :
    ⊢@{IProp GF} |==> ∃ hG : UdpGS GF, udpCtx hG g ∗ udpStart hG g := by
  letI := hPre.allG
  imod ghost_map_alloc (GF := GF) (addrSpace ([] : List (List w8))) with ⟨%γ, H, Hs⟩
  imodintro
  iexists (⟨hPre.allG, γ⟩ : UdpGS GF)
  isplitl [H]
  · unfold udpCtx
    iexists addrSpace []
    iframe H
    ipureintro
    exact sentOk_init g hg
  · unfold udpStart udpSent
    iframe Hs

/-- The start resources of a node: its sockets. -/
def sockStart (hL : UdpLocalGS GF) (L : UdpLocal) : IProp GF :=
  [∗map] s ↦ a ∈ L.socks, udpSock hL s a

theorem udp_local_init (hPre : UdpGpreS GF) (L : UdpLocal) :
    ⊢@{IProp GF} |==> ∃ hL : UdpLocalGS GF, udpLocalCtx hL L ∗ sockStart hL L := by
  letI := hPre.allG
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := GoString) with ⟨%γ, H⟩
  imod ghost_map_insert_persist_big (γ := γ) L.socks (fun _ _ h => by simp at h)
    $$ H with ⟨H, Hs⟩
  imodintro
  iexists (⟨hPre.allG, γ⟩ : UdpLocalGS GF)
  unfold udpLocalCtx sockStart udpSock
  have hu : L.socks ∪ (∅ : GMap w64 GoString) = L.socks := by
    apply GMap.ext; intro k; rw [gmap_lookup_union]; cases L.socks.lookup k <;> rfl
  rw [hu]
  iframe H Hs

end init

/-- The ghost state of the UDP extension. The program gets every valid address's datagrams, and
each node its sockets. The network starts with no datagram (`UdpGlobal.init`); a node's sockets are
not constrained (`initP`: `True`). -/
instance udp_interp : ExtInterp udpExt where
  LocalGS := UdpLocalGS
  GlobalGS := UdpGS
  localCtx := udpLocalCtx
  globalCtx := udpCtx
  PreG := UdpGpreS
  initgP g := g.init
  initP _ _ := True
  globalStart := udpStart
  localStart := sockStart
  global_init _ hPre g hg := udp_global_init hPre g hg
  local_init _ hPre L _ _ := udp_local_init hPre L

/-- The ghost state can be allocated for every initial state of the semantics (`udp_semantics`'s
`initGlobal` is `udp_interp`'s `initgP`). -/
instance udp_init_compat : ExtInitCompat udpExt where
  initgP_of_init _ h := h
  initP_of_init _ _ _ := trivial

end Udp
end Perennial
