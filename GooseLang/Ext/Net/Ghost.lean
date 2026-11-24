/-
The ghost state of the net extension (`Impl.lean`) and its interpretation (`ExtInterp`). Its
resources are the extension's state, piece by piece, and nothing else (no history of operations).

**The network's resources** (global, all in the one `AllG GF` of the ghost state, `NetGS`):

* `netLisTok a` (exclusive, one per valid address, from the start resources): the right to listen
  at `a`, which `Listen` of `a` takes (`wp_net_Listen`, by an atomic update, so that the token may
  live in an invariant: a node that re-listens at its address after every restart keeps it there),
  so that a proof can show that only its holder ever listens at `a`. `Listen` of a wildcard (D21)
  takes the tokens of every valid address with its port (`lisToks la`: those of the addresses `la`
  takes, `lisAccepts`; `la`'s own alone for a valid address, `lisToks_addrOk`).
* `netPend a S` (exclusive, one per valid address, `addrOk`, from the start resources: the valid
  addresses are finitely many, `Deploy.lean`'s `addrSpace`): `S` is the set of the
  connections dialed to `a` and not yet accepted. `Dial` adds to it and `Accept` takes from it, as
  logically atomic steps, so a program keeps it in an invariant with what it promises about the
  connections of `S` (the per-address protocol).
* For a connection `c` and its end `s` (`false` the dialer, `true` the acceptor):
  - `netEnd c s st`: the state of the end (closed, its deadlines). A half of a ghost variable; the
    network holds the other half.
  - `netDir c s d`: the direction from the end `s` to the other end: its unread bytes and its
    status (`NetDir`). A half of a ghost variable, and a token that makes it exclusive.
  - `netConnAt c a` (persistent): `c` was dialed to `a`.
  - `netWLock c s` (exclusive): the write lock of the end `s` is held (D25), which a `Write`'s first
    step takes from the network and its last gives back (the network holds the token while the lock
    is free); the proof of `net`'s `Write` keeps it between the two.
  A connection's ghost names are in a ghost map from connection numbers (persistent entries).

**The node's resources** (local): `netLis l a o`, the listener `l` at `a`, open if `o`
(exclusive); `netLisOn l a` (persistent), the listener `l` exists, at `a` (a valid address or a
wildcard, `listenOk`), which is what an `Accept` or a `Close` needs to step while `netLis` is
elsewhere (in an invariant: a listener shared between threads); `netLisAt l a`, the same at a valid
address (`addrOk`).

**Crashes**: the network's resources are global and survive a crash, as the network does. The
listeners' ghost maps are the node's, made anew at a crash (no listener survives).
-/
module

public import Perennial.GooseLang.Lifting
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.Token
public import GooseLang.Ext.Net.Deploy

@[expose] public section

noncomputable section

namespace Perennial
namespace Net

open Iris Iris.BI Iris.Std ProofMode

/-! ## Ghost names -/

/-- The ghost names of a connection, and its address. `v s`: the state of the end `s`; `q s`: the
direction from the end `s`; `tk s`: the token of that direction; `wl s`: the token of the end's
write lock (D25). -/
structure ConnNames where
  addr : GoString
  v0 : GName
  v1 : GName
  q0 : GName
  q1 : GName
  tk0 : GName
  tk1 : GName
  wl0 : GName
  wl1 : GName
deriving DecidableEq

def ConnNames.enc (γ : ConnNames) :=
  (γ.addr, γ.v0, γ.v1, γ.q0, γ.q1, γ.tk0, γ.tk1, γ.wl0, γ.wl1)

instance ConnNames.countable : Pos.Countable ConnNames :=
  .ofInjective (fun γ => Pos.Countable.encode γ.enc) (fun a b h => by
    have h' := Pos.encode_inj h
    cases a; cases b; simp only [ConnNames.enc, Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h'; rfl)

def ConnNames.v (γ : ConnNames) : Bool → GName
  | false => γ.v0
  | true => γ.v1

def ConnNames.q (γ : ConnNames) : Bool → GName
  | false => γ.q0
  | true => γ.q1

def ConnNames.tk (γ : ConnNames) : Bool → GName
  | false => γ.tk0
  | true => γ.tk1

def ConnNames.wl (γ : ConnNames) : Bool → GName
  | false => γ.wl0
  | true => γ.wl1

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

/-- The global ghost state: the universal camera, the ghost maps of the connections' names and of
the pending sets. -/
structure NetGS (GF : BundledGFunctors) where
  allG : AllG GF
  γnames : GName
  γpend : GName
  /-- The listening tokens (`netLisTok`). -/
  γtok : GName

/-- The local ghost state: the universal camera and its listeners' ghost map. -/
structure NetLocalGS (GF : BundledGFunctors) where
  allG : AllG GF
  γlis : GName
  /-- The listeners' addresses (persistent entries: a listener's address never changes). -/
  γat : GName

/-- What the adequacy theorem provides: the universal camera. -/
structure NetGpreS (GF : BundledGFunctors) where
  allG : AllG GF

section defs
variable {GF : BundledGFunctors}

/-! ## The network's interpretation -/

/-- The network's part of a write lock (D25): its token while it is free. -/
def lockCtx [AllG GF] (γ : GName) (held : Bool) : IProp GF :=
  if held then iprop(True) else token γ

/-- The network's part of the connection `cn`, with names `γ`: the other halves of its ends' and
directions' ghost variables, and the tokens of its free write locks. -/
def connCtx [AllG GF] (γ : ConnNames) (cn : NetConn) : IProp GF :=
  iprop(⌜γ.addr = cn.addr⌝ ∗
    ghostVar (γ.v false) (1 : Qp).half (cn.endSt false) ∗
    ghostVar (γ.v true) (1 : Qp).half (cn.endSt true) ∗
    ghostVar (γ.q false) (1 : Qp).half (cn.out false) ∗
    ghostVar (γ.q true) (1 : Qp).half (cn.out true) ∗
    lockCtx (γ.wl false) (cn.lock false) ∗ lockCtx (γ.wl true) (cn.lock true))

/-- The pending sets agree with the network: `pm` has the valid addresses, each with the
connections dialed to it and not yet accepted; and every connection was dialed to a valid address. -/
def PendOk (g : NetGlobal) (pm : GMap GoString (GSet Nat)) : Prop :=
  (∀ a, (pm !! a).isSome = addrOk a) ∧
  (∀ a S c, pm !! a = some S →
    (c ∈ S ↔ ∃ cn, g.conns !! c = some cn ∧ cn.addr = a ∧ cn.accepted = false)) ∧
  (∀ c cn, g.conns !! c = some cn →
    addrOk cn.addr = true ∧ c ≠ 0 ∧ 2 * c + 1 < 2 ^ 64)

/-- The interpretation of the network. -/
def netCtx (hG : NetGS GF) (g : NetGlobal) : IProp GF :=
  letI := hG.allG
  iprop(∃ (nm : GMap Nat ConnNames) (pm : GMap GoString (GSet Nat)),
    ghostMapAuth hG.γnames 1 nm ∗ ghostMapAuth hG.γpend 1 pm ∗
    ⌜(∀ c, (nm !! c).isSome = (g.conns !! c).isSome) ∧ PendOk g pm⌝ ∗
    [∗map] c ↦ cn ∈ g.conns, ∃ γ, ⌜nm !! c = some γ⌝ ∗ ghostMapElem hG.γnames c .discard γ ∗
      connCtx γ cn)

/-- The listeners' addresses. -/
def lisAddrs (m : GMap w64 (GoString × Bool)) : GMap w64 GoString := GMap.fmap Prod.fst m

/-- The interpretation of a node: its listeners are those of the ghost map (`γlis`), their
addresses those of the other (`γat`). -/
def netLocalCtx (hL : NetLocalGS GF) (L : NetLocal) : IProp GF :=
  letI := hL.allG
  iprop(ghostMapAuth hL.γlis 1 L.lis ∗ ghostMapAuth hL.γat 1 (lisAddrs L.lis))

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

/-- D25. The write lock of the end `s` of `c` is held, by whoever has this (exclusive). -/
def netWLock (hG : NetGS GF) (c : Nat) (s : Bool) : IProp GF :=
  letI := hG.allG
  iprop(∃ γ, netNames hG c γ ∗ token (γ.wl s))

/-- `c` was dialed to `a` (and its ends' ids are in range, and not `0`). -/
def netConnAt (hG : NetGS GF) (c : Nat) (a : GoString) : IProp GF :=
  letI := hG.allG
  iprop(∃ γ, netNames hG c γ ∗ ⌜γ.addr = a ∧ c ≠ 0 ∧ 2 * c + 1 < 2 ^ 64⌝)

/-- The connections dialed to `a` and not yet accepted are `S`. -/
def netPend (hG : NetGS GF) (a : GoString) (S : GSet Nat) : IProp GF :=
  letI := hG.allG; ghostMapElem hG.γpend a (.own 1) S

/-- The right to listen at the valid address `a` (exclusive: `netLisTok_excl`). -/
def netLisTok (hG : NetGS GF) (a : GoString) : IProp GF :=
  letI := hG.allG; ghostMapElem hG.γtok a (.own 1) ()

/-- The listener `l` of this node, at `a`, open if `o`. -/
def netLis (hL : NetLocalGS GF) (l : w64) (a : GoString) (o : Bool) : IProp GF :=
  letI := hL.allG; ghostMapElem hL.γlis l (.own 1) (a, o)

/-- The listener `l` of this node exists, at the valid address `a` (persistent: `netLisOn` at an
`addrOk` address, `netLisAt_on`, `netLisOn_at`, which a listener at a valid address takes only the
connections dialed to, `lisAccepts_addrOk`). -/
def netLisAt (hL : NetLocalGS GF) (l : w64) (a : GoString) : IProp GF :=
  letI := hL.allG; iprop(ghostMapElem hL.γat l .discard a ∗ ⌜addrOk a = true⌝)

/-- The listener `l` of this node exists, at `a`, a valid address or a wildcard (`listenOk`, D21):
what `Listen` gives (persistent, as `netLisAt`, which is it at a valid address: `netLisAt_on`,
`netLisOn_at`). -/
def netLisOn (hL : NetLocalGS GF) (l : w64) (a : GoString) : IProp GF :=
  letI := hL.allG; iprop(ghostMapElem hL.γat l .discard a ∗ ⌜listenOk a = true⌝)

/-- D21. The right to listen at `la` (a valid address or a wildcard): the listening tokens of the
valid addresses it takes (`lisAccepts`), `la`'s alone for a valid address (`lisToks_addrOk`), every
valid address with its port for a wildcard. -/
def lisToks (hG : NetGS GF) (la : GoString) : IProp GF :=
  [∗map] a ↦ _u ∈ addrSpace (), iprop(⌜lisAccepts la a⌝ → netLisTok hG a)

instance netNames_persistent (hG : NetGS GF) c γ : Persistent (netNames hG c γ) := by
  unfold netNames; letI := hG.allG; infer_instance
instance netConnAt_persistent (hG : NetGS GF) c a : Persistent (netConnAt hG c a) := by
  unfold netConnAt; letI := hG.allG; infer_instance

instance netEnd_timeless (hG : NetGS GF) c s st : Timeless (netEnd hG c s st) := by
  unfold netEnd netNames; letI := hG.allG; infer_instance
instance netDir_timeless (hG : NetGS GF) c s d : Timeless (netDir hG c s d) := by
  unfold netDir netNames; letI := hG.allG; infer_instance
instance netWLock_timeless (hG : NetGS GF) c s : Timeless (netWLock hG c s) := by
  unfold netWLock netNames; letI := hG.allG; infer_instance
instance netConnAt_timeless (hG : NetGS GF) c a : Timeless (netConnAt hG c a) := by
  unfold netConnAt netNames; letI := hG.allG; infer_instance
instance netPend_timeless (hG : NetGS GF) a S : Timeless (netPend hG a S) := by
  unfold netPend; letI := hG.allG; infer_instance
instance netLis_timeless (hL : NetLocalGS GF) l a o : Timeless (netLis hL l a o) := by
  unfold netLis; letI := hL.allG; infer_instance
instance netLisAt_timeless (hL : NetLocalGS GF) l a : Timeless (netLisAt hL l a) := by
  unfold netLisAt; letI := hL.allG; infer_instance
instance netLisAt_persistent (hL : NetLocalGS GF) l a : Persistent (netLisAt hL l a) := by
  unfold netLisAt; letI := hL.allG; infer_instance
instance netLisTok_timeless (hG : NetGS GF) a : Timeless (netLisTok hG a) := by
  unfold netLisTok; letI := hG.allG; infer_instance
instance netLisOn_timeless (hL : NetLocalGS GF) l a : Timeless (netLisOn hL l a) := by
  unfold netLisOn; letI := hL.allG; infer_instance
instance netLisOn_persistent (hL : NetLocalGS GF) l a : Persistent (netLisOn hL l a) := by
  unfold netLisOn; letI := hL.allG; infer_instance
instance lisToks_timeless (hG : NetGS GF) la : Timeless (lisToks hG la) := by
  unfold lisToks; letI := hG.allG; infer_instance

theorem netLisAt_on (hL : NetLocalGS GF) (l : w64) (a : GoString) :
    netLisAt hL l a ⊢ netLisOn hL l a := by
  letI := hL.allG
  unfold netLisAt netLisOn
  iintro ⟨H, %h⟩
  iframe H
  ipureintro; simp [listenOk, h]

theorem netLisOn_at (hL : NetLocalGS GF) (l : w64) {a : GoString} (h : addrOk a = true) :
    netLisOn hL l a ⊢ netLisAt hL l a := by
  letI := hL.allG
  unfold netLisAt netLisOn
  iintro ⟨H, -⟩
  iframe H
  ipureintro; exact h

/-- At a valid address, the right to listen is its listening token. -/
theorem lisToks_addrOk (hG : NetGS GF) {la : GoString} (h : addrOk la = true) :
    lisToks hG la ⊣⊢ netLisTok hG la := by
  letI := hG.allG
  have hl : PartialMap.get? (addrSpace ()) la = some () := by
    rw [gmap_get?_eq]; exact addrSpace_lookup_ok () h
  unfold lisToks
  constructor
  · refine (BigSepM.bigSepM_lookup_acc hl).1.trans ?_
    iintro ⟨H, -⟩
    iapply H
    ipureintro; exact Or.inl rfl
  · have key : ∀ {k : GoString} {v : Unit}, PartialMap.get? (Std.delete (addrSpace ()) la) k = some v →
        (iprop(□ True) : IProp GF) ⊢ iprop(⌜lisAccepts la k⌝ → netLisTok hG k) := by
      intro k v hk
      iintro - %hacc
      have hk' : la = k := (lisAccepts_addrOk h).mp hacc
      subst hk'
      rw [gmap_get?_eq] at hk
      have : (GMap.delete la (addrSpace ())) !! la = none := GMap.lookup_delete _ _
      rw [show Std.delete (addrSpace ()) la = GMap.delete la (addrSpace ()) from rfl, this] at hk
      cases hk
    refine Entails.trans ?_ (BigSepM.bigSepM_delete hl).2
    iintro Ht
    isplitl [Ht]
    · iintro %_; iexact Ht
    · iapply (BigSepM.bigSepM_intro key)
      imodintro; itrivial

theorem netLisTok_excl (hG : NetGS GF) (a : GoString) :
    netLisTok hG a ∗ netLisTok hG a ⊢ (False : IProp GF) := by
  letI := hG.allG
  unfold netLisTok
  iintro ⟨H1, H2⟩
  icases ghostMapElem_valid_2 a hG.γtok (.own 1) (.own 1) () () $$ H1 H2 with %⟨H, -⟩
  exact absurd H (Iris.CMRA.not_valid_excl_op_left (x := DFrac.own (1 : Qp)))

end defs

/-! ## Initialization -/

section init
variable {GF : BundledGFunctors}

/-- The pending sets of a network with no connections: every valid address, with no
connection. -/
def pendInit : GMap GoString (GSet Nat) := addrSpace (∅ : GSet Nat)

/-- The start resources of the network: every valid address's (empty) pending set and its
listening token. -/
def netStart (hG : NetGS GF) (_g : NetGlobal) : IProp GF :=
  iprop(([∗map] a ↦ S ∈ pendInit, netPend hG a S) ∗
    [∗map] a ↦ _u ∈ addrSpace (), netLisTok hG a)

theorem pendOk_init (g : NetGlobal) (h : g.conns = ∅) : PendOk g pendInit := by
  refine ⟨fun a => ?_, fun a S c hS => ?_, fun c cn hc => ?_⟩
  · exact addrSpace_lookup_isSome _ a
  · obtain rfl := addrSpace_lookup_some hS
    rw [h]; simp [GMap.not_elem_of_empty]
  · rw [h] at hc; simp at hc

theorem net_global_init (hPre : NetGpreS GF) (g : NetGlobal) (hg : g.conns = ∅) :
    ⊢@{IProp GF} |==> ∃ hG : NetGS GF, netCtx hG g ∗ netStart hG g := by
  letI := hPre.allG
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := ConnNames) with ⟨%γn, Hn⟩
  imod ghost_map_alloc (GF := GF) pendInit with ⟨%γp, Hp, Hps⟩
  imod ghost_map_alloc (GF := GF) (addrSpace ()) with ⟨%γt, -, Hts⟩
  imodintro
  iexists (⟨hPre.allG, γn, γp, γt⟩ : NetGS GF)
  isplitl [Hn Hp]
  · unfold netCtx
    iexists ∅, pendInit
    iframe Hn Hp
    isplitr
    · ipureintro
      exact ⟨fun c => by simp [hg, gmap_get?_eq], pendOk_init g hg⟩
    · rw [hg]; iapply BigSepM.bigSepM_empty.2; iempintro
  · unfold netStart netPend netLisTok
    iframe Hps Hts

/-- The start resources of a node: its listeners. -/
def lisStart (hL : NetLocalGS GF) (L : NetLocal) : IProp GF :=
  letI := hL.allG
  iprop(([∗map] l ↦ x ∈ L.lis, netLis hL l x.1 x.2) ∗
    [∗map] l ↦ a ∈ lisAddrs L.lis, ghostMapElem hL.γat l .discard a)

theorem net_local_init (hPre : NetGpreS GF) (L : NetLocal) :
    ⊢@{IProp GF} |==> ∃ hL : NetLocalGS GF, netLocalCtx hL L ∗ lisStart hL L := by
  letI := hPre.allG
  imod ghost_map_alloc (GF := GF) L.lis with ⟨%γ, H, Hs⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := GoString) with ⟨%γa, Ha⟩
  imod ghost_map_insert_persist_big (γ := γa) (lisAddrs L.lis) (fun _ _ h => by simp at h)
    $$ Ha with ⟨Ha, Has⟩
  imodintro
  iexists (⟨hPre.allG, γ, γa⟩ : NetLocalGS GF)
  unfold netLocalCtx lisStart netLis
  have hu : lisAddrs L.lis ∪ (∅ : GMap w64 GoString) = lisAddrs L.lis := by
    apply GMap.ext; intro k; rw [gmap_lookup_union]; cases (lisAddrs L.lis).lookup k <;> rfl
  rw [hu]
  iframe H Hs Ha Has

end init

/-- The ghost state of the net extension. The program gets the network's pending sets (every
valid address's), and each node its listeners. The network starts with no connection
(`NetGlobal.init`); a node's listeners are not constrained (`initP`: `True`). -/
instance net_interp : ExtInterp netExt where
  LocalGS := NetLocalGS
  GlobalGS := NetGS
  localCtx := netLocalCtx
  globalCtx := netCtx
  PreG := NetGpreS
  initgP g := g.init
  initP _ _ := True
  globalStart := netStart
  localStart := lisStart
  global_init _ hPre g hg := net_global_init hPre g hg
  local_init _ hPre L _ _ := net_local_init hPre L

/-- The ghost state can be allocated for every initial state of the semantics (`net_semantics`'s
`initGlobal` is `net_interp`'s `initgP`). -/
instance net_init_compat : ExtInitCompat netExt where
  initgP_of_init _ h := h
  initP_of_init _ _ _ := trivial

end Net
end Perennial
