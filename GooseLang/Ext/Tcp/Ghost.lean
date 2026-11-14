/-
The ghost state of the TCP extension (`Impl.lean`) and its interpretation (`ExtInterp`). Its
resources are the extension's state, piece by piece, and nothing else (no history of operations).

**The network's resources** (global, all in the one `AllG GF` of the ghost state, `TcpGS`):

* `tcpPlan a h` (persistent): the plan has the address `a`, at the host `h`.
* `tcpPend a S` (exclusive, one per plan address, from the start resources): `S` is the set of the
  connections dialed to `a` and not yet accepted. `Dial` adds to it and `Accept` takes from it, as
  logically atomic steps, so a program keeps it in an invariant with what it promises about the
  connections of `S` (the per-address protocol).
* For a connection `c` and its end `s` (`false` the dialer, `true` the acceptor):
  - `tcpEnd c s st`: the state of the end (closed, its deadlines). A half of a ghost variable; the
    network holds the other half.
  - `tcpDir c s d`: the direction from the end `s` to the other end: its unread bytes and its
    status (`TcpDir`). A half of a ghost variable, and a token that makes it exclusive.
  - `tcpConnAt c a` (persistent): `c` was dialed to `a`.
  A connection's ghost names are in a ghost map from connection numbers (persistent entries).

**The node's resources** (local): `tcpLis l a o`, the listener `l` at `a`, open if `o`
(exclusive); `tcpLisAt l a` (persistent), the listener `l` exists, at `a`, which is what an `Accept`
or a `Close` needs to step while `tcpLis` is elsewhere (in an invariant: a listener shared between
threads); and the node's host (`TcpLocalGS.host`), fixed, which the local interpretation says is the
node's.

**Crashes**: the network's resources are global and survive a crash, as the network does. The
listeners' ghost maps are the node's, made anew at a crash (no listener survives).
-/
module

public import Perennial.GooseLang.Lifting
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.Token
public import GooseLang.Ext.Tcp.Impl

@[expose] public section

noncomputable section

namespace Perennial
namespace Tcp

open Iris Iris.BI Iris.Std ProofMode

/-! ## Ghost names -/

/-- The ghost names of a connection, and its address. `v s`: the state of the end `s`; `q s`: the
direction from the end `s`; `tk s`: the token of that direction. -/
structure ConnNames where
  addr : GoString
  v0 : GName
  v1 : GName
  q0 : GName
  q1 : GName
  tk0 : GName
  tk1 : GName
deriving DecidableEq

def ConnNames.enc (γ : ConnNames) :=
  (γ.addr, γ.v0, γ.v1, γ.q0, γ.q1, γ.tk0, γ.tk1)

instance ConnNames.countable : Pos.Countable ConnNames :=
  .ofInjective (fun γ => Pos.Countable.encode γ.enc) (fun a b h => by
    have h' := Pos.encode_inj h
    cases a; cases b; simp only [ConnNames.enc, Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h'; rfl)

def ConnNames.v (γ : ConnNames) : Bool → GName
  | false => γ.v0
  | true => γ.v1

def ConnNames.q (γ : ConnNames) : Bool → GName
  | false => γ.q0
  | true => γ.q1

def ConnNames.tk (γ : ConnNames) : Bool → GName
  | false => γ.tk0
  | true => γ.tk1

def TcpStatus.toNat : TcpStatus → Nat
  | .open => 0
  | .fin => 1
  | .cut => 2

instance TcpStatus.countable : Pos.Countable TcpStatus :=
  .ofInjective (fun k : TcpStatus => Pos.Countable.encode k.toNat)
    (fun a b h => by
      have h' := Pos.encode_inj h
      cases a <;> cases b <;> first | rfl | (simp [TcpStatus.toNat] at h'))

instance TcpDir.countable : Pos.Countable TcpDir :=
  .ofInjective (fun d : TcpDir => Pos.Countable.encode (d.bytes, d.status))
    (fun a b h => by
      have h' := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'; rfl)

instance TcpEnd.countable : Pos.Countable TcpEnd :=
  .ofInjective (fun st : TcpEnd => Pos.Countable.encode (st.closed, st.rdl, st.wdl))
    (fun a b h => by
      have h' := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl, rfl⟩ := h'; rfl)

/-- The global ghost state: the universal camera, and the ghost maps of the connections' names, of
the pending sets and of the plan. -/
structure TcpGS (GF : BundledGFunctors) where
  allG : AllG GF
  γnames : GName
  γpend : GName
  γplan : GName

/-- The local ghost state: the universal camera, the node's host, and its listeners' ghost map. -/
structure TcpLocalGS (GF : BundledGFunctors) where
  allG : AllG GF
  host : GoString
  γlis : GName
  /-- The listeners' addresses (persistent entries: a listener's address never changes). -/
  γat : GName

/-- What the adequacy theorem provides: the universal camera. -/
structure TcpGpreS (GF : BundledGFunctors) where
  allG : AllG GF

section defs
variable {GF : BundledGFunctors}

/-! ## The network's interpretation -/

/-- The network's part of the connection `cn`, with names `γ`: the other halves of its ends' and
directions' ghost variables. -/
def connCtx [AllG GF] (γ : ConnNames) (cn : TcpConn) : IProp GF :=
  iprop(⌜γ.addr = cn.addr⌝ ∗
    ghostVar (γ.v false) (1 : Qp).half (cn.endSt false) ∗
    ghostVar (γ.v true) (1 : Qp).half (cn.endSt true) ∗
    ghostVar (γ.q false) (1 : Qp).half (cn.out false) ∗
    ghostVar (γ.q true) (1 : Qp).half (cn.out true))

/-- The pending sets agree with the network: `pm` has the plan's addresses, each with the
connections dialed to it and not yet accepted; and every connection was dialed to a plan address. -/
def PendOk (g : TcpGlobal) (pm : GMap GoString (GSet Nat)) : Prop :=
  (∀ a, (pm !! a).isSome = (g.plan !! a).isSome) ∧
  (∀ a S c, pm !! a = some S →
    (c ∈ S ↔ ∃ cn, g.conns !! c = some cn ∧ cn.addr = a ∧ cn.accepted = false)) ∧
  (∀ c cn, g.conns !! c = some cn → (g.plan !! cn.addr).isSome = true ∧ 2 * c + 1 < 2 ^ 64)

/-- The interpretation of the network. -/
def tcpCtx (hG : TcpGS GF) (g : TcpGlobal) : IProp GF :=
  letI := hG.allG
  iprop(∃ (nm : GMap Nat ConnNames) (pm : GMap GoString (GSet Nat)),
    ghostMapAuth hG.γnames 1 nm ∗ ghostMapAuth hG.γpend 1 pm ∗ ghostMapAuth hG.γplan 1 g.plan ∗
    ⌜(∀ c, (nm !! c).isSome = (g.conns !! c).isSome) ∧ PendOk g pm⌝ ∗
    [∗map] c ↦ cn ∈ g.conns, ∃ γ, ⌜nm !! c = some γ⌝ ∗ ghostMapElem hG.γnames c .discard γ ∗
      connCtx γ cn)

/-- The listeners' addresses. -/
def lisAddrs (m : GMap w64 (GoString × Bool)) : GMap w64 GoString := GMap.fmap Prod.fst m

/-- The interpretation of a node: its host is the ghost state's, and its listeners are those of
the ghost map (`γlis`), their addresses those of the other (`γat`). -/
def tcpLocalCtx (hL : TcpLocalGS GF) (L : TcpLocal) : IProp GF :=
  letI := hL.allG
  iprop(⌜L.host = hL.host⌝ ∗ ghostMapAuth hL.γlis 1 L.lis ∗ ghostMapAuth hL.γat 1 (lisAddrs L.lis))

/-! ## The resources -/

/-- `c` has the ghost names `γ`. -/
def tcpNames (hG : TcpGS GF) (c : Nat) (γ : ConnNames) : IProp GF :=
  letI := hG.allG; ghostMapElem hG.γnames c .discard γ

/-- The end `s` of `c`: its state `st`. -/
def tcpEnd (hG : TcpGS GF) (c : Nat) (s : Bool) (st : TcpEnd) : IProp GF :=
  letI := hG.allG
  iprop(∃ γ, tcpNames hG c γ ∗ ghostVar (γ.v s) (1 : Qp).half st)

/-- The direction from the end `s` of `c`: its unread bytes and its status, `d`. Exclusive (the
direction's token, `γ.tk s`, which only this resource holds). -/
def tcpDir (hG : TcpGS GF) (c : Nat) (s : Bool) (d : TcpDir) : IProp GF :=
  letI := hG.allG
  iprop(∃ γ, tcpNames hG c γ ∗ ghostVar (γ.q s) (1 : Qp).half d ∗ token (γ.tk s))

/-- `c` was dialed to `a` (and its ends' ids are in range). -/
def tcpConnAt (hG : TcpGS GF) (c : Nat) (a : GoString) : IProp GF :=
  letI := hG.allG
  iprop(∃ γ, tcpNames hG c γ ∗ ⌜γ.addr = a ∧ 2 * c + 1 < 2 ^ 64⌝)

/-- The connections dialed to `a` and not yet accepted are `S`. -/
def tcpPend (hG : TcpGS GF) (a : GoString) (S : GSet Nat) : IProp GF :=
  letI := hG.allG; ghostMapElem hG.γpend a (.own 1) S

/-- The plan has `a`, at the host `h`. -/
def tcpPlan (hG : TcpGS GF) (a h : GoString) : IProp GF :=
  letI := hG.allG; ghostMapElem hG.γplan a .discard h

/-- The listener `l` of this node, at `a`, open if `o`. -/
def tcpLis (hL : TcpLocalGS GF) (l : w64) (a : GoString) (o : Bool) : IProp GF :=
  letI := hL.allG; ghostMapElem hL.γlis l (.own 1) (a, o)

/-- The listener `l` of this node exists, at `a` (persistent: what an `Accept` or `Close` of `l`
needs to take a step, whoever holds `tcpLis`). -/
def tcpLisAt (hL : TcpLocalGS GF) (l : w64) (a : GoString) : IProp GF :=
  letI := hL.allG; ghostMapElem hL.γat l .discard a

instance tcpNames_persistent (hG : TcpGS GF) c γ : Persistent (tcpNames hG c γ) := by
  unfold tcpNames; letI := hG.allG; infer_instance
instance tcpConnAt_persistent (hG : TcpGS GF) c a : Persistent (tcpConnAt hG c a) := by
  unfold tcpConnAt; letI := hG.allG; infer_instance
instance tcpPlan_persistent (hG : TcpGS GF) a h : Persistent (tcpPlan hG a h) := by
  unfold tcpPlan; letI := hG.allG; infer_instance

instance tcpEnd_timeless (hG : TcpGS GF) c s st : Timeless (tcpEnd hG c s st) := by
  unfold tcpEnd tcpNames; letI := hG.allG; infer_instance
instance tcpDir_timeless (hG : TcpGS GF) c s d : Timeless (tcpDir hG c s d) := by
  unfold tcpDir tcpNames; letI := hG.allG; infer_instance
instance tcpConnAt_timeless (hG : TcpGS GF) c a : Timeless (tcpConnAt hG c a) := by
  unfold tcpConnAt tcpNames; letI := hG.allG; infer_instance
instance tcpPend_timeless (hG : TcpGS GF) a S : Timeless (tcpPend hG a S) := by
  unfold tcpPend; letI := hG.allG; infer_instance
instance tcpPlan_timeless (hG : TcpGS GF) a h : Timeless (tcpPlan hG a h) := by
  unfold tcpPlan; letI := hG.allG; infer_instance
instance tcpLis_timeless (hL : TcpLocalGS GF) l a o : Timeless (tcpLis hL l a o) := by
  unfold tcpLis; letI := hL.allG; infer_instance
instance tcpLisAt_timeless (hL : TcpLocalGS GF) l a : Timeless (tcpLisAt hL l a) := by
  unfold tcpLisAt; letI := hL.allG; infer_instance
instance tcpLisAt_persistent (hL : TcpLocalGS GF) l a : Persistent (tcpLisAt hL l a) := by
  unfold tcpLisAt; letI := hL.allG; infer_instance

end defs

/-! ## Initialization -/

section init
variable {GF : BundledGFunctors}

/-- The pending sets of a network with no connections: the plan's addresses, each with no
connection. -/
def pendInit (g : TcpGlobal) : GMap GoString (GSet Nat) := GMap.fmap (fun _ => (∅ : GSet Nat)) g.plan

/-- The start resources of the network: its plan, and every plan address's (empty) pending set. -/
def tcpStart (hG : TcpGS GF) (g : TcpGlobal) : IProp GF :=
  iprop(([∗map] a ↦ h ∈ g.plan, tcpPlan hG a h) ∗ [∗map] a ↦ S ∈ pendInit g, tcpPend hG a S)

theorem pendOk_init (g : TcpGlobal) (h : g.conns = ∅) : PendOk g (pendInit g) := by
  refine ⟨fun a => ?_, fun a S c hS => ?_, fun c cn hc => ?_⟩
  · simp [pendInit]
  · simp only [pendInit, GMap.lookup_fmap] at hS
    cases hp : g.plan.lookup a <;> simp [hp] at hS
    subst hS; rw [h]; simp [GMap.not_elem_of_empty]
  · rw [h] at hc; simp at hc

theorem tcp_global_init (hPre : TcpGpreS GF) (g : TcpGlobal) (hg : g.conns = ∅) :
    ⊢@{IProp GF} |==> ∃ hG : TcpGS GF, tcpCtx hG g ∗ tcpStart hG g := by
  letI := hPre.allG
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := ConnNames) with ⟨%γn, Hn⟩
  imod ghost_map_alloc (GF := GF) (pendInit g) with ⟨%γp, Hp, Hps⟩
  imod ghost_map_alloc_empty (GF := GF) (K := GoString) (V := GoString) with ⟨%γl, Hl⟩
  imod ghost_map_insert_persist_big (γ := γl) g.plan (fun _ _ h => by simp at h)
    $$ Hl with ⟨Hl, Hls⟩
  imodintro
  iexists (⟨hPre.allG, γn, γp, γl⟩ : TcpGS GF)
  isplitl [Hn Hp Hl]
  · unfold tcpCtx
    iexists ∅, pendInit g
    iframe Hn Hp
    have hu : g.plan ∪ (∅ : GMap GoString GoString) = g.plan := by
      apply GMap.ext; intro k; rw [gmap_lookup_union]; cases g.plan.lookup k <;> rfl
    rw [hu]
    iframe Hl
    isplitr
    · ipureintro
      exact ⟨fun c => by simp [hg, gmap_get?_eq], pendOk_init g hg⟩
    · rw [hg]; iapply BigSepM.bigSepM_empty.2; iempintro
  · unfold tcpStart tcpPlan tcpPend
    iframe Hls Hps

/-- The start resources of a node: its host, and its listeners. -/
def lisStart (hL : TcpLocalGS GF) (L : TcpLocal) : IProp GF :=
  iprop(⌜hL.host = L.host⌝ ∗ ([∗map] l ↦ x ∈ L.lis, tcpLis hL l x.1 x.2) ∗
    [∗map] l ↦ a ∈ lisAddrs L.lis, tcpLisAt hL l a)

theorem tcp_local_init (hPre : TcpGpreS GF) (L : TcpLocal) :
    ⊢@{IProp GF} |==> ∃ hL : TcpLocalGS GF, tcpLocalCtx hL L ∗ lisStart hL L := by
  letI := hPre.allG
  imod ghost_map_alloc (GF := GF) L.lis with ⟨%γ, H, Hs⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := GoString) with ⟨%γa, Ha⟩
  imod ghost_map_insert_persist_big (γ := γa) (lisAddrs L.lis) (fun _ _ h => by simp at h)
    $$ Ha with ⟨Ha, Has⟩
  imodintro
  iexists (⟨hPre.allG, L.host, γ, γa⟩ : TcpLocalGS GF)
  unfold tcpLocalCtx lisStart tcpLis tcpLisAt
  have hu : lisAddrs L.lis ∪ (∅ : GMap w64 GoString) = lisAddrs L.lis := by
    apply GMap.ext; intro k; rw [gmap_lookup_union]; cases (lisAddrs L.lis).lookup k <;> rfl
  rw [hu]
  iframe H Hs Ha Has
  isplit <;> ipureintro <;> rfl

end init

/-- The ghost state of the TCP extension. The program gets the network's plan and pending sets,
and each node its listeners (none, in an initial state that satisfies `initP`) and its host. -/
instance tcp_interp : ExtInterp tcpExt where
  LocalGS := TcpLocalGS
  GlobalGS := TcpGS
  localCtx := tcpLocalCtx
  globalCtx := tcpCtx
  PreG := TcpGpreS
  initgP g := g.conns = ∅
  initP _ _ := True
  globalStart := tcpStart
  localStart := lisStart
  global_init _ hPre g hg := tcp_global_init hPre g hg
  local_init _ hPre L _ _ := tcp_local_init hPre L

end Tcp
end Perennial
