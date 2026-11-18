/-
The ghost state of the net extension (`Impl.lean`) and its interpretation (`ExtInterp`). Its
resources are the extension's state, piece by piece, and nothing else (no history of operations).

**The network's resources** (global, all in the one `AllG GF` of the ghost state, `NetGS`):

* `netPlan a h` (persistent): the plan has the address `a`, at the host `h`. The plan itself is a
  field of the ghost state (`NetGS.plan`, the network's, which no step changes; the start resources
  say which), for `Listen`'s resolution of a wildcard, which needs the whole plan (`ListenAt`).
* `netPend a S` (exclusive, one per plan address, from the start resources): `S` is the set of the
  connections dialed to `a` and not yet accepted. `Dial` adds to it and `Accept` takes from it, as
  logically atomic steps, so a program keeps it in an invariant with what it promises about the
  connections of `S` (the per-address protocol).
* For a connection `c` and its end `s` (`false` the dialer, `true` the acceptor):
  - `netEnd c s st`: the state of the end (closed, its deadlines). A half of a ghost variable; the
    network holds the other half.
  - `netDir c s d`: the direction from the end `s` to the other end: its unread bytes and its
    status (`NetDir`). A half of a ghost variable, and a token that makes it exclusive.
  - `netConnAt c a` (persistent): `c` was dialed to `a`.
  A connection's ghost names are in a ghost map from connection numbers (persistent entries).

**The node's resources** (local): `netLis l a o`, the listener `l` at `a`, open if `o`
(exclusive); `netLisAt l a` (persistent), the listener `l` exists, at `a`, which is what an `Accept`
or a `Close` needs to step while `netLis` is elsewhere (in an invariant: a listener shared between
threads); and the node's host (`NetLocalGS.host`), fixed, which the local interpretation says is the
node's.

**Crashes**: the network's resources are global and survive a crash, as the network does. The
listeners' ghost maps are the node's, made anew at a crash (no listener survives).
-/
module

public import Perennial.GooseLang.Lifting
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.Token
public import GooseLang.Ext.Net.Impl

@[expose] public section

noncomputable section

namespace Perennial
namespace Net

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

def NetStatus.toNat : NetStatus → Nat
  | .open => 0
  | .fin => 1
  | .cut => 2

instance NetStatus.countable : Pos.Countable NetStatus :=
  .ofInjective (fun k : NetStatus => Pos.Countable.encode k.toNat)
    (fun a b h => by
      have h' := Pos.encode_inj h
      cases a <;> cases b <;> first | rfl | (simp [NetStatus.toNat] at h'))

instance NetDir.countable : Pos.Countable NetDir :=
  .ofInjective (fun d : NetDir => Pos.Countable.encode (d.bytes, d.status))
    (fun a b h => by
      have h' := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'; rfl)

instance NetEnd.countable : Pos.Countable NetEnd :=
  .ofInjective (fun st : NetEnd => Pos.Countable.encode (st.closed, st.rdl, st.wdl))
    (fun a b h => by
      have h' := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl, rfl⟩ := h'; rfl)

/-- The global ghost state: the universal camera, the ghost maps of the connections' names, of
the pending sets and of the plan, and the plan itself (`plan`: the network's, which no step
changes; what `Listen`'s resolution of a wildcard needs, `ListenAt`). -/
structure NetGS (GF : BundledGFunctors) where
  allG : AllG GF
  γnames : GName
  γpend : GName
  γplan : GName
  plan : GMap GoString GoString

/-- The local ghost state: the universal camera, the node's host, and its listeners' ghost map. -/
structure NetLocalGS (GF : BundledGFunctors) where
  allG : AllG GF
  host : GoString
  γlis : GName
  /-- The listeners' addresses (persistent entries: a listener's address never changes). -/
  γat : GName

/-- What the adequacy theorem provides: the universal camera. -/
structure NetGpreS (GF : BundledGFunctors) where
  allG : AllG GF

section defs
variable {GF : BundledGFunctors}

/-! ## The network's interpretation -/

/-- The network's part of the connection `cn`, with names `γ`: the other halves of its ends' and
directions' ghost variables. -/
def connCtx [AllG GF] (γ : ConnNames) (cn : NetConn) : IProp GF :=
  iprop(⌜γ.addr = cn.addr⌝ ∗
    ghostVar (γ.v false) (1 : Qp).half (cn.endSt false) ∗
    ghostVar (γ.v true) (1 : Qp).half (cn.endSt true) ∗
    ghostVar (γ.q false) (1 : Qp).half (cn.out false) ∗
    ghostVar (γ.q true) (1 : Qp).half (cn.out true))

/-- The pending sets agree with the network: `pm` has the plan's addresses, each with the
connections dialed to it and not yet accepted; and every connection was dialed to a plan address. -/
def PendOk (g : NetGlobal) (pm : GMap GoString (GSet Nat)) : Prop :=
  (∀ a, (pm !! a).isSome = (g.plan !! a).isSome) ∧
  (∀ a S c, pm !! a = some S →
    (c ∈ S ↔ ∃ cn, g.conns !! c = some cn ∧ cn.addr = a ∧ cn.accepted = false)) ∧
  (∀ c cn, g.conns !! c = some cn →
    (g.plan !! cn.addr).isSome = true ∧ c ≠ 0 ∧ 2 * c + 1 < 2 ^ 64)

/-- The interpretation of the network. -/
def netCtx (hG : NetGS GF) (g : NetGlobal) : IProp GF :=
  letI := hG.allG
  iprop(∃ (nm : GMap Nat ConnNames) (pm : GMap GoString (GSet Nat)),
    ghostMapAuth hG.γnames 1 nm ∗ ghostMapAuth hG.γpend 1 pm ∗ ghostMapAuth hG.γplan 1 g.plan ∗
    ⌜(∀ c, (nm !! c).isSome = (g.conns !! c).isSome) ∧ PendOk g pm ∧ g.plan = hG.plan⌝ ∗
    [∗map] c ↦ cn ∈ g.conns, ∃ γ, ⌜nm !! c = some γ⌝ ∗ ghostMapElem hG.γnames c .discard γ ∗
      connCtx γ cn)

/-- The listeners' addresses. -/
def lisAddrs (m : GMap w64 (GoString × Bool)) : GMap w64 GoString := GMap.fmap Prod.fst m

/-- The interpretation of a node: its host is the ghost state's, and its listeners are those of
the ghost map (`γlis`), their addresses those of the other (`γat`). -/
def netLocalCtx (hL : NetLocalGS GF) (L : NetLocal) : IProp GF :=
  letI := hL.allG
  iprop(⌜L.host = hL.host⌝ ∗ ghostMapAuth hL.γlis 1 L.lis ∗ ghostMapAuth hL.γat 1 (lisAddrs L.lis))

/-! ## The resources -/

/-- `c` has the ghost names `γ`. -/
def netNames (hG : NetGS GF) (c : Nat) (γ : ConnNames) : IProp GF :=
  letI := hG.allG; ghostMapElem hG.γnames c .discard γ

/-- The end `s` of `c`: its state `st`. -/
def netEnd (hG : NetGS GF) (c : Nat) (s : Bool) (st : NetEnd) : IProp GF :=
  letI := hG.allG
  iprop(∃ γ, netNames hG c γ ∗ ghostVar (γ.v s) (1 : Qp).half st)

/-- The direction from the end `s` of `c`: its unread bytes and its status, `d`. Exclusive (the
direction's token, `γ.tk s`, which only this resource holds). -/
def netDir (hG : NetGS GF) (c : Nat) (s : Bool) (d : NetDir) : IProp GF :=
  letI := hG.allG
  iprop(∃ γ, netNames hG c γ ∗ ghostVar (γ.q s) (1 : Qp).half d ∗ token (γ.tk s))

/-- `c` was dialed to `a` (and its ends' ids are in range, and not `0`). -/
def netConnAt (hG : NetGS GF) (c : Nat) (a : GoString) : IProp GF :=
  letI := hG.allG
  iprop(∃ γ, netNames hG c γ ∗ ⌜γ.addr = a ∧ c ≠ 0 ∧ 2 * c + 1 < 2 ^ 64⌝)

/-- The connections dialed to `a` and not yet accepted are `S`. -/
def netPend (hG : NetGS GF) (a : GoString) (S : GSet Nat) : IProp GF :=
  letI := hG.allG; ghostMapElem hG.γpend a (.own 1) S

/-- The plan has `a`, at the host `h`. -/
def netPlan (hG : NetGS GF) (a h : GoString) : IProp GF :=
  letI := hG.allG; ghostMapElem hG.γplan a .discard h

/-- The listener `l` of this node, at `a`, open if `o`. -/
def netLis (hL : NetLocalGS GF) (l : w64) (a : GoString) (o : Bool) : IProp GF :=
  letI := hL.allG; ghostMapElem hL.γlis l (.own 1) (a, o)

/-- The listener `l` of this node exists, at `a` (persistent: what an `Accept` or `Close` of `l`
needs to take a step, whoever holds `netLis`). -/
def netLisAt (hL : NetLocalGS GF) (l : w64) (a : GoString) : IProp GF :=
  letI := hL.allG; ghostMapElem hL.γat l .discard a

instance netNames_persistent (hG : NetGS GF) c γ : Persistent (netNames hG c γ) := by
  unfold netNames; letI := hG.allG; infer_instance
instance netConnAt_persistent (hG : NetGS GF) c a : Persistent (netConnAt hG c a) := by
  unfold netConnAt; letI := hG.allG; infer_instance
instance netPlan_persistent (hG : NetGS GF) a h : Persistent (netPlan hG a h) := by
  unfold netPlan; letI := hG.allG; infer_instance

instance netEnd_timeless (hG : NetGS GF) c s st : Timeless (netEnd hG c s st) := by
  unfold netEnd netNames; letI := hG.allG; infer_instance
instance netDir_timeless (hG : NetGS GF) c s d : Timeless (netDir hG c s d) := by
  unfold netDir netNames; letI := hG.allG; infer_instance
instance netConnAt_timeless (hG : NetGS GF) c a : Timeless (netConnAt hG c a) := by
  unfold netConnAt netNames; letI := hG.allG; infer_instance
instance netPend_timeless (hG : NetGS GF) a S : Timeless (netPend hG a S) := by
  unfold netPend; letI := hG.allG; infer_instance
instance netPlan_timeless (hG : NetGS GF) a h : Timeless (netPlan hG a h) := by
  unfold netPlan; letI := hG.allG; infer_instance
instance netLis_timeless (hL : NetLocalGS GF) l a o : Timeless (netLis hL l a o) := by
  unfold netLis; letI := hL.allG; infer_instance
instance netLisAt_timeless (hL : NetLocalGS GF) l a : Timeless (netLisAt hL l a) := by
  unfold netLisAt; letI := hL.allG; infer_instance
instance netLisAt_persistent (hL : NetLocalGS GF) l a : Persistent (netLisAt hL l a) := by
  unfold netLisAt; letI := hL.allG; infer_instance

end defs

/-! ## Initialization -/

section init
variable {GF : BundledGFunctors}

/-- The pending sets of a network with no connections: the plan's addresses, each with no
connection. -/
def pendInit (g : NetGlobal) : GMap GoString (GSet Nat) := GMap.fmap (fun _ => (∅ : GSet Nat)) g.plan

/-- The start resources of the network: its plan, and every plan address's (empty) pending set. -/
def netStart (hG : NetGS GF) (g : NetGlobal) : IProp GF :=
  iprop(([∗map] a ↦ h ∈ g.plan, netPlan hG a h) ∗ ([∗map] a ↦ S ∈ pendInit g, netPend hG a S) ∗
    ⌜hG.plan = g.plan⌝)

theorem pendOk_init (g : NetGlobal) (h : g.conns = ∅) : PendOk g (pendInit g) := by
  refine ⟨fun a => ?_, fun a S c hS => ?_, fun c cn hc => ?_⟩
  · simp [pendInit]
  · simp only [pendInit, GMap.lookup_fmap] at hS
    cases hp : g.plan.lookup a <;> simp [hp] at hS
    subst hS; rw [h]; simp [GMap.not_elem_of_empty]
  · rw [h] at hc; simp at hc

theorem net_global_init (hPre : NetGpreS GF) (g : NetGlobal) (hg : g.conns = ∅) :
    ⊢@{IProp GF} |==> ∃ hG : NetGS GF, netCtx hG g ∗ netStart hG g := by
  letI := hPre.allG
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := ConnNames) with ⟨%γn, Hn⟩
  imod ghost_map_alloc (GF := GF) (pendInit g) with ⟨%γp, Hp, Hps⟩
  imod ghost_map_alloc_empty (GF := GF) (K := GoString) (V := GoString) with ⟨%γl, Hl⟩
  imod ghost_map_insert_persist_big (γ := γl) g.plan (fun _ _ h => by simp at h)
    $$ Hl with ⟨Hl, Hls⟩
  imodintro
  iexists (⟨hPre.allG, γn, γp, γl, g.plan⟩ : NetGS GF)
  isplitl [Hn Hp Hl]
  · unfold netCtx
    iexists ∅, pendInit g
    iframe Hn Hp
    have hu : g.plan ∪ (∅ : GMap GoString GoString) = g.plan := by
      apply GMap.ext; intro k; rw [gmap_lookup_union]; cases g.plan.lookup k <;> rfl
    rw [hu]
    iframe Hl
    isplitr
    · ipureintro
      exact ⟨fun c => by simp [hg, gmap_get?_eq], pendOk_init g hg, rfl⟩
    · rw [hg]; iapply BigSepM.bigSepM_empty.2; iempintro
  · unfold netStart netPlan netPend
    iframe Hls Hps
    ipureintro; rfl

/-- The start resources of a node: its host, and its listeners. -/
def lisStart (hL : NetLocalGS GF) (L : NetLocal) : IProp GF :=
  iprop(⌜hL.host = L.host⌝ ∗ ([∗map] l ↦ x ∈ L.lis, netLis hL l x.1 x.2) ∗
    [∗map] l ↦ a ∈ lisAddrs L.lis, netLisAt hL l a)

theorem net_local_init (hPre : NetGpreS GF) (L : NetLocal) :
    ⊢@{IProp GF} |==> ∃ hL : NetLocalGS GF, netLocalCtx hL L ∗ lisStart hL L := by
  letI := hPre.allG
  imod ghost_map_alloc (GF := GF) L.lis with ⟨%γ, H, Hs⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := GoString) with ⟨%γa, Ha⟩
  imod ghost_map_insert_persist_big (γ := γa) (lisAddrs L.lis) (fun _ _ h => by simp at h)
    $$ Ha with ⟨Ha, Has⟩
  imodintro
  iexists (⟨hPre.allG, L.host, γ, γa⟩ : NetLocalGS GF)
  unfold netLocalCtx lisStart netLis netLisAt
  have hu : lisAddrs L.lis ∪ (∅ : GMap w64 GoString) = lisAddrs L.lis := by
    apply GMap.ext; intro k; rw [gmap_lookup_union]; cases (lisAddrs L.lis).lookup k <;> rfl
  rw [hu]
  iframe H Hs Ha Has
  isplit <;> ipureintro <;> rfl

end init

/-- The ghost state of the net extension. The program gets the network's plan and pending sets,
and each node its listeners (none, in an initial state that satisfies `initP`) and its host. -/
instance net_interp : ExtInterp netExt where
  LocalGS := NetLocalGS
  GlobalGS := NetGS
  localCtx := netLocalCtx
  globalCtx := netCtx
  PreG := NetGpreS
  initgP g := g.conns = ∅
  initP _ _ := True
  globalStart := netStart
  localStart := lisStart
  global_init _ hPre g hg := net_global_init hPre g hg
  local_init _ hPre L _ _ := net_local_init hPre L

end Net
end Perennial
