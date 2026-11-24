/-
The replica framework (`replica/replica.go`, the `*replica.Replica` that `epaxos.Replica` embeds):
its representation and the predicates the protocol layer (epaxos) sees. The function specs are in
`Epaxos/Interface/ReplicaSpec.lean`.

* **Pointers.** `FwPtrs`: the framework's read-only field values (slices, maps, channels,
  pointers), fixed by `replica.New`; every predicate is indexed by them.
* **Read-only fields** `fwRO γ r id L p` (persistent): `N = len(L)`, `F = 2`, `Id = id`,
  `PeerAddrList = L` (the final node list, `listFinal γ L`), the flags as `epaxos.New` leaves them
  (`Thrifty`, `Exec`, `Dreply` true; `LRead`, `Beacon`, `Durable`, `Shutdown` false; `Dt` nil),
  the logger (non-verbose), the configuration (empty `ProxyInfo`), the rpc table (`tableOk`: the
  nine protocol codes, each with a prototype of its kind and a channel whose invariant is
  `deliverChanP`), `ProposeChan` (a bag of `proposal`s), `BeaconChan` (nothing is ever sent), and
  the shared invariants (`clientInvs γ`: the replica addresses' protocols, the role registry).
* **The lock** `r.M` with `fwLockInv γ id L p Rext = fwCore γ id L p ∗ Rext`: `fwCore` (sealed,
  the framework's own: the peer slots with their writers and the framework's halves of the sent
  lists, the client writers, `Alive`, `Latencies`, the `Stats` map) and `Rext`, the protocol
  layer's part (its choice; epaxos takes `True`: its `CommittedUpTo` is in the instance lock's
  invariant, `ownRep`, since every access, `updateCommitted`'s writes under `r.M` included, is
  made by the run loop holding the instance lock, and `SendMsg` marshals it from the caller's
  `msgObj`). Laws: `fwCore_alive` (read `Alive`), `fwCore_stats` (update `Stats.M`).
* **`isReplicaFw γ r id L p Rext`** (persistent): `fwRO`, the frozen fields and table
  (`fwFrozen`), and the mutex with `fwLockInv` (a handle `ConnectToPeers` returns; it says nothing
  about which peers are connected: a higher peer may connect later, and `SendMsg` to an
  unconnected peer sends nothing).
* **Delivery.** `deliverable γ id d n m obj`: `obj` holds the protocol message `m` (fresh, owned),
  the `n`-th protocol message `d` sent to `id` (`msgSent`), for another replica `d < nRep`, and its
  one-shot delivery token (`delivTok`). The reader goroutine of peer `d` sends it on the channel of `m`'s code, whose
  invariant is `deliverChanP γ id k` ("some deliverable message of kind `k`"); epaxos's run loop
  receives it.
* **Client proposals** on `ProposeChan`: `proposal γ id g`: the `*GPropose` `g` (read-only) for
  client `c`'s op on connection `cid` (`clientConn`: role, escrow), its `Propose` (`CommandId 0`,
  `ClientId c`, the command `cmdOf i` of the op's input, `Timestamp 0`), its `Reply` writer
  registered with `cid` (`clientWriter`), the reply token (`replyTok`, exclusive: one reply per
  connection, what the client protocol `clientReplyOk` allows) and either the op token (`opTok`,
  exclusive: one proposal per connection; the client listener's) or, for `handleCommit`'s
  re-proposal of a proposal whose slot was decided a no-op, the protocol layer's re-proposal token
  `inChan γ id ⟨cid, cmdOf i⟩` (`Epaxos/Interface/EpaxosGhost.lean`; the op token was used when the
  proposal first entered the protocol model).
* **Start resources** `repFwStart γ i` (per replica id; for `repStart`): the framework's halves of
  the sent lists from `i`, the delivery minting rights at `i`, the dial tokens of `i` to the lower
  ids and its own, the client-writer and reply-token maps' authorities.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Registry
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.RpcTable
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Ghost
public import Perennial.Golang.Theory.Chan.Idioms.Bag

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The replica framework's invariants' namespace. -/
def fwN : Namespace := ndot epN "replica"

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-! ## Client writers and reply tokens -/

/-- The `*bufio.Writer` `w` is replica `id`'s writer of client connection `cid` (persistent). -/
def clientWriterDef (γ : EpNames) (id : Nat) (w : Loc) (cid : Nat) : IProp GF :=
  ghostMapElem (γ.rep.cwriters id) w DFrac.discard cid

@[irreducible] def clientWriter (γ : EpNames) (id : Nat) (w : Loc) (cid : Nat) :
    IProp GF := clientWriterDef γ id w cid

theorem clientWriter_unseal : clientWriter (GF := GF) = clientWriterDef := by
  funext; with_unfolding_all rfl

/-- The right to reply once on replica `id`'s client writer `w` (exclusive). -/
def replyTokDef (γ : EpNames) (id : Nat) (w : Loc) : IProp GF :=
  ghostMapElem (γ.rep.replies id) w (DFrac.own 1) ()

@[irreducible] def replyTok (γ : EpNames) (id : Nat) (w : Loc) : IProp GF :=
  replyTokDef γ id w

theorem replyTok_unseal : replyTok (GF := GF) = replyTokDef := by funext; with_unfolding_all rfl

instance clientWriter_persistent (γ : EpNames) (id : Nat) (w : Loc) (cid : Nat) :
    Persistent (clientWriter (GF := GF) γ id w cid) := by
  rw [clientWriter_unseal]; unfold clientWriterDef; infer_instance
instance clientWriter_timeless (γ : EpNames) (id : Nat) (w : Loc) (cid : Nat) :
    Timeless (clientWriter (GF := GF) γ id w cid) := by
  rw [clientWriter_unseal]; unfold clientWriterDef; infer_instance
instance replyTok_timeless (γ : EpNames) (id : Nat) (w : Loc) : Timeless (replyTok (GF := GF) γ id w) := by
  rw [replyTok_unseal]; unfold replyTokDef; infer_instance

theorem clientWriter_agree (γ : EpNames) (id : Nat) (w : Loc) (cid cid' : Nat) :
    clientWriter (GF := GF) γ id w cid -∗ clientWriter γ id w cid' -∗ ⌜cid = cid'⌝ := by
  rw [clientWriter_unseal]; unfold clientWriterDef
  iintro H1 H2
  icombine H1 H2 gives %H
  ipureintro; exact H.2

theorem replyTok_excl (γ : EpNames) (id : Nat) (w : Loc) :
    replyTok (GF := GF) γ id w -∗ replyTok γ id w -∗ False := by
  rw [replyTok_unseal]; unfold replyTokDef
  iintro H1 H2
  icases ghostMapElem_ne _ w w _ () () $$ H1 H2 with %Hne
  exact absurd rfl Hne

/-- The one-shot token of the `PROPOSE` of client connection `cid` (exclusive): the acceptor's
fresh token of the connection, which the client listener hands over with the connection's only
proposal (the client protocol allows one `PROPOSE` per connection; the peer classification does
not use a client connection's acceptor token). -/
def opTokDef (_γ : EpNames) (cid : Nat) : IProp GF := connFresh cid true

@[irreducible] def opTok (γ : EpNames) (cid : Nat) : IProp GF := opTokDef γ cid

theorem opTok_unseal : opTok (GF := GF) = opTokDef := by funext; with_unfolding_all rfl

theorem opTok_excl (γ : EpNames) (cid : Nat) : opTok (GF := GF) γ cid -∗ opTok γ cid -∗ False := by
  rw [opTok_unseal]; unfold opTokDef
  iintro H1 H2
  iapply (connFresh_excl (Gg := G) cid true)
  isplitl [H1]
  · iexact H1
  · iexact H2

/-! ## Start resources

`repFwStart γ i` (the framework's start resources of replica `i`) is declared in
`Epaxos/Interface/Registry.lean` (below this file), where `repStart` names it. -/

/-! ## Laws linking the registry, the roles and the peer streams -/

/-- The final list gives the replica ids of its addresses. -/
theorem listFinal_addrId (γ : EpNames) (L : List GoString) (i : Nat) (a : GoString)
    (h : L[i]? = some a) : listFinal (GF := GF) γ L ⊢ addrId γ a i := by
  rw [addrId_unseal]; unfold addrIdDef listFinal finalListOk
  iintro ⟨#H, %Hp⟩
  iexists L
  iframe H
  ipureintro
  exact ⟨Hp.nodup_iff.mpr (by decide), h⟩

/-- Replica `d` registers its connection `cid` to replica `i`'s address, a lower id, as `peer d`
(with the dialer's fresh token and its dial token): the role, and the connection is `d`'s only
one to `i`. -/
theorem peerRole_register (γ : EpNames) (E : CoPset) (cid : Nat) (d i : Nat) (hE : ↑roleN ⊆ E) :
    ⊢ ⌜i < d ∧ d < nRep⌝ -∗ inv roleN (roleInv (GF := GF) γ) -∗ connFresh cid false -∗ dialTok γ d i ={E}=∗
      roleElem γ cid (.peer (W64 d)) ∗ peerConn γ d i cid := by
  iintro %Hids #Hreg Hfr Hd
  imod dialTok_use γ d i cid $$ %Hids Hd with #Hpc
  iinv Hreg with Hi Hclose
  unfold roleInv
  icases Hi with ⟨%M, %N, >HM, >HN, >%HMN, >Hfs⟩
  cases hM : M.lookup cid with
  | some n =>
    icases (BigSepM.bigSepM_delete (show get? M cid = some n from hM)).1 $$ Hfs with ⟨Hf2, -⟩
    iexfalso
    iapply (connFresh_excl (Gg := G) cid false)
    isplitl [Hfr]
    · iexact Hfr
    · iexact Hf2
  | none =>
    imod ghost_map_insert_persist cid (ConnRole.peer (W64 d)) hM $$ HM with ⟨HM, #He⟩
    imod Hclose $$ [HM HN Hfs Hfr] with -
    · inext
      iexists M.insert cid (ConnRole.peer (W64 d)), N
      iframe HM HN
      isplitr
      · ipureintro
        intro c
        by_cases hc : cid = c
        · subst hc
          rw [GMap.lookup_insert]
          have := HMN cid
          rw [hM] at this
          simp only [reduceCtorEq, exists_false, iff_false, Option.some.injEq] at this ⊢
          exact this
        · rw [GMap.lookup_insert_ne _ _ hc]
          exact HMN c
      iapply (BigSepM.bigSepM_insert (show get? M cid = none from hM)).2
      iframe
    imodintro
    unfold roleElem
    iframe He Hpc

/- The replica addresses' protocols are prefix-closed: `repDialP_ppc`, `repAccP_ppc`
(`Interface/ConnBuf.lean`; the lab's `repDialP_prefixClosed`/`repAccP_prefixClosed`). -/

end ghost

section fld
variable [GooseExts] [GoLocalContext] [GoGlobalContext] [go.Semantics]

/-- The field `f` of the `*replica.Replica` `r` (stated over the local context only, so that a
use determines every argument). -/
abbrev fld (r : Loc) (f : GoString) : Loc := structFieldRef replica.Replica f r

end fld

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]

/-! ## The framework's pointers -/

/-- The framework's read-only field values (`replica.New` fixes them). -/
structure FwPtrs where
  /-- `Logger` (embedded `*dlog.Logger`) -/
  logger : Loc
  /-- `Alias` -/
  aliasStr : GoString
  /-- `PeerAddrList` -/
  addrs : GoSlice
  /-- `Peers`, `PeerReaders`, `PeerWriters` -/
  peers : GoSlice
  readers : GoSlice
  writers : GoSlice
  /-- `ClientWriters` -/
  cwriters : GoMap
  /-- `Config`, and its `Proxy` -/
  cfg : Loc
  proxy : Loc
  /-- `Alive` -/
  alive : GoSlice
  /-- `State` -/
  st : Loc
  /-- `RPC` -/
  tbl : Loc
  /-- `Stats`, and its map `M` -/
  stats : Loc
  statsMap : GoMap
  /-- `ProposeChan`, `BeaconChan` -/
  pchan : GoChan
  bchan : GoChan
  /-- `Ewma`, `Latencies` -/
  ewma : GoSlice
  lat : GoSlice


/-! ## Delivery and proposals -/

/-- `obj` holds the protocol message `m` (fresh, owned), the `n`-th protocol message replica `d`
(another replica: `d < nRep`, `d ≠ id`) sent to replica `id`, with its one-shot delivery
token. -/
def deliverable (γ : EpNames) (id d n : Nat) (m : Msg) (obj : GoInterface) : IProp GF :=
  iprop(⌜d < nRep ∧ d ≠ id⌝ ∗ msgObj obj m (DFrac.own 1) ∗ ⌜m.wf⌝ ∗ msgSent γ d id n m ∗
    delivTok γ id d n)

/-- The invariant of replica `id`'s channel of kind `k`: a deliverable message of that kind. -/
def deliverChanP (γ : EpNames) (id : Nat) (k : MsgKind) (obj : GoInterface) : IProp GF :=
  iprop(∃ (d n : Nat) (m : Msg), ⌜m.kind = some k⌝ ∗ deliverable γ id d n m obj)

/-- The entries `epaxos.New` registers: the nine kinds' codes, each with a prototype of its kind
and a channel with `deliverChanP` (persistent). -/
def tableEntriesOk (γ : EpNames) (id : Nat) (E : GMap w8 rpc.Pair'') : IProp GF :=
  iprop(⌜∀ c, E.lookup c ≠ none → ∃ k ∈ MsgKind.all, c = k.code⌝ ∗
    [∗list] k ∈ MsgKind.all, ∃ (obj : GoInterface) (ch : GoChan) (γc : ChanNames),
      ⌜E.lookup k.code = some (rpc.Pair''.mk obj ch) ∧ protoObj k obj⌝ ∗
      isChanBag γc ch (deliverChanP γ id k))

/-- Replica `id`'s frozen rpc table (persistent). -/
def tableOk (γ : EpNames) (id : Nat) (tbl : Loc) : IProp GF :=
  iprop(∃ E, isTable tbl E ∗ tableEntriesOk γ id E)

instance tableEntriesOk_persistent (γ : EpNames) (id : Nat) (E : GMap w8 rpc.Pair'') :
    Persistent (tableEntriesOk (GF := GF) γ id E) := by
  unfold tableEntriesOk; infer_instance

instance tableOk_persistent (γ : EpNames) (id : Nat) (tbl : Loc) :
    Persistent (tableOk (GF := GF) γ id tbl) := by
  unfold tableOk; infer_instance

/-- The `*GPropose` `g` replica `id`'s client listener sends on `ProposeChan`: see the file
header. -/
def proposal (γ : EpNames) (id : Nat) (g : Loc) : IProp GF :=
  iprop(∃ (pp w mu : Loc) (proxy : Bool) (addr : GoString) (cid : Nat) (c : w64) (i : KvI)
      (cv : state.Command),
    g ↦□ replica.defs.GPropose.mk pp w mu proxy addr ∗
    pp ↦□ replica.defs.Propose.mk (W32 0) (W32 (uint.Z c)) cv (W64 0) ∗ cmdOk cv (cmdOf i) ∗
    clientConn γ cid c i ∗ clientWriter γ id w cid ∗ replyTok γ id w ∗
    (opTok γ cid ∨ inChan γ id ⟨cid, cmdOf i⟩))

/-! ## The lock -/

/- The peer and client slots are `replica/Ghost.lean`'s `peerSlotX`, `clientSlotX` (over
`Net/`'s connections: `connIn`, `connWr`, `connRd`); the lab's documentation copies `peerP`,
`peerSlot`, `clientSlot` are not kept. -/

/-- The framework's part of `r.M`'s invariant (sealed; package-internal except through its
laws): the peer slots (`Peers`, `PeerReaders`, `PeerWriters`), the client writers (the
`ClientWriters` map, and the registered writers by pointer with their reply tokens' authority),
`Alive`, `Latencies`, the `Stats` map.

Proof note: `ConnectToPeers` fills the slots `j < id` (and `Alive[j]`) without `r.M`, while
`serveConn` (another goroutine) fills the slots `j > id` under it; the replica package's proof
may refine this body (e.g. keep the elements `j < id` in a cancelable invariant until dialing is
done); no other package unseals it. -/
def fwCoreDef (γ : EpNames) (id : Nat) (L : List GoString) (p : FwPtrs) : IProp GF :=
  iprop(∃ (ns : FwNames) (CWm : GMap w32 Loc) (CW : GMap Loc Nat) (RT : GMap Loc Unit)
      (sm : GMap GoString w64),
    fwNames γ id ns ∗
    inv fwDepN (depInv ns.1 ns.2.2.1 (fwPeers γ id L p.peers p.writers p.alive p.lat p.ewma)) ∗
    inv fwDepN (depInv ns.2.1 ns.2.2.2 (fwReaders L p.readers)) ∗
    (fwPeers γ id L p.peers p.writers p.alive p.lat p.ewma ∨ (token ns.1 ∗ £ 1)) ∗
    (fwReaders L p.readers ∨ token ns.2.1) ∗
    ownMap p.cwriters (DFrac.own 1) CWm ∗
    ghostMapAuth (γ.rep.cwriters id) 1 CW ∗ ghostMapAuth (γ.rep.replies id) 1 RT ∗
    ⌜∀ w, (CW.lookup w).isSome = (RT.lookup w).isSome⌝ ∗
    ([∗map] w ↦ cid ∈ CW, clientSlotX γ id L w cid) ∗
    ownMap p.statsMap (DFrac.own 1) sm)

@[irreducible] def fwCore (γ : EpNames) (id : Nat) (L : List GoString) (p : FwPtrs) :
    IProp GF := fwCoreDef γ id L p

theorem fwCore_unseal : fwCore (GF := GF) = fwCoreDef := by funext; with_unfolding_all rfl

/-- `r.M`'s invariant: the framework's part and the protocol layer's `Rext`. -/
def fwLockInv (γ : EpNames) (id : Nat) (L : List GoString) (p : FwPtrs) (Rext : IProp GF) :
    IProp GF :=
  iprop(fwCore γ id L p ∗ Rext)

/-! ## The read-only fields and the handle -/

/-- The framework's read-only fields and their contents, and the shared facts (persistent): see
the file header. -/
def fwRODef (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs) :
    IProp GF :=
  iprop(fld r go!"Logger" ↦□ p.logger ∗ p.logger ↦□ (zeroValDef : dlog.Logger) ∗
    fld r go!"N" ↦□ W64 L.length ∗ fld r go!"F" ↦□ W64 2 ∗ fld r go!"Id" ↦□ W32 id ∗
    fld r go!"Alias" ↦□ p.aliasStr ∗ fld r go!"PeerAddrList" ↦□ p.addrs ∗ p.addrs ↦*□ L ∗
    fld r go!"Peers" ↦□ p.peers ∗ fld r go!"PeerReaders" ↦□ p.readers ∗
    fld r go!"PeerWriters" ↦□ p.writers ∗ fld r go!"ClientWriters" ↦□ p.cwriters ∗
    fld r go!"Config" ↦□ p.cfg ∗
    (∃ c : config.Config, p.cfg ↦□ c ∗ ⌜c.Proxy' = p.proxy⌝) ∗
    p.proxy ↦□ (zeroValDef : config.ProxyInfo) ∗
    fld r go!"Alive" ↦□ p.alive ∗ fld r go!"State" ↦□ p.st ∗ fld r go!"RPC" ↦□ p.tbl ∗
    fld r go!"StableStore" ↦□ null ∗
    fld r go!"Stats" ↦□ p.stats ∗ p.stats ↦□ replica.defs.Stats.mk p.statsMap ∗
    fld r go!"Shutdown" ↦□ false ∗ fld r go!"ProposeChan" ↦□ p.pchan ∗
    fld r go!"BeaconChan" ↦□ p.bchan ∗ fld r go!"Thrifty" ↦□ true ∗ fld r go!"Exec" ↦□ true ∗
    fld r go!"LRead" ↦□ false ∗ fld r go!"Dreply" ↦□ true ∗
    fld r go!"Ewma" ↦□ p.ewma ∗ fld r go!"Latencies" ↦□ p.lat ∗ fld r go!"Dt" ↦□ null ∗
    ⌜L.length = nRep ∧ id < L.length⌝ ∗ listFinal γ L ∗ clientInvs γ ∗
    (∃ γc : ChanNames, isChanBag γc p.pchan (proposal γ id) ∗ ⌜sint.Z γc.chanCap < 2 ^ 32⌝) ∗
    (∃ γc : ChanNames, isChanBag (V := Loc) γc p.bchan (fun _ => iprop(False))))

@[irreducible] def fwRO (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs) :
    IProp GF := fwRODef γ r id L p

theorem fwRO_unseal : fwRO (GF := GF) = fwRODef := by funext; with_unfolding_all rfl

instance fwRO_persistent (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs) :
    Persistent (fwRO (GF := GF) γ r id L p) := by
  rw [fwRO_unseal]; unfold fwRODef; infer_instance

/-- The fields `epaxos.New` writes after `replica.New` (`Beacon`, `Durable`, both `false`) and the
rpc table, frozen (persistent). -/
def fwFrozenDef (γ : EpNames) (r : Loc) (id : Nat) (p : FwPtrs) : IProp GF :=
  iprop(fld r go!"Beacon" ↦□ false ∗ fld r go!"Durable" ↦□ false ∗ tableOk γ id p.tbl ∗
    isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.epaxos)

@[irreducible] def fwFrozen (γ : EpNames) (r : Loc) (id : Nat) (p : FwPtrs) : IProp GF :=
  fwFrozenDef γ r id p

theorem fwFrozen_unseal : fwFrozen (GF := GF) = fwFrozenDef := by funext; with_unfolding_all rfl

instance fwFrozen_persistent (γ : EpNames) (r : Loc) (id : Nat) (p : FwPtrs) :
    Persistent (fwFrozen (GF := GF) γ r id p) := by
  rw [fwFrozen_unseal]; unfold fwFrozenDef; infer_instance

/-- What `ConnectToPeers` starts from (exclusive, package-internal; the right to listen at the
replica's address is its `addrProto`'s, in `clientInvs`: `listen_au`; the lab's `addrTok` is gone),
the fresh lock, the mutable slices' and maps' initial contents, `Listener` and
`PreferredPeerOrder`, and the framework's start ghost state (`repFwStart`). -/
def fwStartDef (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs) :
    IProp GF :=
  iprop(repFwStart γ id ∗
    fld r go!"M" ↦ (zeroValDef : sync.Mutex) ∗
    p.peers ↦* List.replicate L.length (interface.nil : GoInterface) ∗
    p.readers ↦* List.replicate L.length (null : Loc) ∗
    p.writers ↦* List.replicate L.length (null : Loc) ∗
    p.alive ↦* List.replicate L.length false ∗ p.lat ↦* List.replicate L.length (W64 0) ∗
    p.ewma ↦* List.replicate L.length (W64 0) ∗
    ownMap p.cwriters (DFrac.own 1) (∅ : GMap w32 Loc) ∗
    (∃ sm : GMap GoString w64, ownMap p.statsMap (DFrac.own 1) sm) ∗
    fld r go!"Listener" ↦ (interface.nil : GoInterface) ∗
    (∃ po : GoSlice, fld r go!"PreferredPeerOrder" ↦ po ∗
      po ↦* ((List.range L.length).map fun (j : Nat) => W32 (((id + 1 + j) % L.length : Nat) : Int))))

@[irreducible] def fwStart (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs) :
    IProp GF := fwStartDef γ r id L p

theorem fwStart_unseal : fwStart (GF := GF) = fwStartDef := by funext; with_unfolding_all rfl

/-- What `replica.New` returns (exclusive): the read-only part, the fields and table `epaxos.New`
then sets up (`Beacon`, `Durable`, the table with next code 9 and no entry), the `Stats` map
(epaxos initializes its counters), an empty store, and `fwStart`. -/
def fwFresh [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [StateTreemap GF] (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs) :
    IProp GF :=
  iprop(fwRO γ r id L p ∗ fld r go!"Beacon" ↦ false ∗ fld r go!"Durable" ↦ false ∗
    ownTable p.tbl (W8 9) ∅ ∗ isState p.st ∅ ∗ fwStart γ r id L p)

/-- Freeze what `epaxos.New` set up (`Beacon`, `Durable` written back `false`, the nine
registrations), with epaxos's initialization (for the framework's dynamic calls into epaxos's
`Marshal`/`New`/`Unmarshal`): `fwFrozen`. -/
theorem fwFreeze (γ : EpNames) (r : Loc) (id : Nat) (p : FwPtrs) (n : w8)
    (E : GMap w8 rpc.Pair'') :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.epaxos -∗
    fld r go!"Beacon" ↦ false -∗ fld r go!"Durable" ↦ false -∗ ownTable p.tbl n E -∗
      tableEntriesOk γ id E ==∗ fwFrozen γ r id p := by
  rw [fwFrozen_unseal]; unfold fwFrozenDef tableOk
  iintro #Hep Hb Hd Ht #He
  ipersist Hb
  ipersist Hd
  imod ownTable_freeze $$ Ht with #Ht
  imodintro
  iframe Hb Hd Hep
  iexists E
  iframe Ht He

/-- The framework after `ConnectToPeers` (persistent): read-only fields, frozen part, the lock
with `fwLockInv` (`Rext` the protocol layer's). -/
def isReplicaFwDef (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs)
    (Rext : IProp GF) : IProp GF :=
  iprop(fwRO γ r id L p ∗ fwFrozen γ r id p ∗
    sync.isMutex (fld r go!"M") (fwLockInv γ id L p Rext) ∗ fwPhase1 γ id ∗ fwPhase2 γ id)

@[irreducible] def isReplicaFw (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString)
    (p : FwPtrs) (Rext : IProp GF) : IProp GF := isReplicaFwDef γ r id L p Rext

theorem isReplicaFw_unseal : isReplicaFw (GF := GF) = isReplicaFwDef := by
  funext; with_unfolding_all rfl

instance isReplicaFw_persistent (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString)
    (p : FwPtrs) (Rext : IProp GF) : Persistent (isReplicaFw γ r id L p Rext) := by
  rw [isReplicaFw_unseal]; unfold isReplicaFwDef; infer_instance

/-- The listener `ConnectToPeers` leaves for `WaitForClientConnections` (exclusive,
package-internal). -/
def fwListeningDef (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) : IProp GF :=
  iprop(∃ (li : GoInterface) (l : w64), fld r go!"Listener" ↦□ li ∗ net.isListener li l ∗
    netLis (extLocalGS netExt (L := hG.goose_localGS)) l (L.getD id []) true ∗
    netLisAt (extLocalGS netExt (L := hG.goose_localGS)) l (L.getD id []))

@[irreducible] def fwListening (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) :
    IProp GF := fwListeningDef γ r id L

theorem fwListening_unseal : fwListening (GF := GF) = fwListeningDef := by funext; with_unfolding_all rfl

/-- `PreferredPeerOrder`, owned (before `ComputeClosestPeers`): a permutation of the replica ids
with `id` last (HUB-REQUEST replica-6; `New`'s initial order `(id + 1 + j) % N`). -/
def fwPrefOwn (r : Loc) (id : Nat) : IProp GF :=
  iprop(∃ (po : GoSlice) (ord : List w32), fld r go!"PreferredPeerOrder" ↦ po ∗ po ↦* ord ∗
    ⌜ord.Perm ((List.range nRep).map fun j : Nat => W32 (j : Int)) ∧
      ord[nRep - 1]? = some (W32 (id : Int))⌝)

/-- `PreferredPeerOrder` after `ComputeClosestPeers` (persistent): a permutation of the replica
ids with `id` last (so its first `N - 1` entries are the other replicas), every entry
non-negative (HUB handlers-3: `sint.nat` maps a negative entry to 0). -/
def prefOrder (r : Loc) (id : Nat) (L : List GoString) (ord : List w32) : IProp GF :=
  iprop(∃ po : GoSlice, fld r go!"PreferredPeerOrder" ↦□ po ∗ po ↦*□ ord ∗
    ⌜(ord.map (fun x => sint.nat x)).Perm (List.range L.length) ∧
      ord[L.length - 1]? = some (W32 id) ∧ ∀ o ∈ ord, 0 ≤ sint.Z o⌝)

/-! ## Laws for the protocol layer -/

theorem isReplicaFw_ro (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs)
    (Rext : IProp GF) : isReplicaFw γ r id L p Rext ⊢ fwRO γ r id L p := by
  rw [isReplicaFw_unseal]; unfold isReplicaFwDef
  iintro ⟨#H, -, -, -, -⟩
  iexact H

theorem isReplicaFw_lock (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs)
    (Rext : IProp GF) :
    isReplicaFw γ r id L p Rext ⊢ sync.isMutex (fld r go!"M") (fwLockInv γ id L p Rext) := by
  rw [isReplicaFw_unseal]; unfold isReplicaFwDef
  iintro ⟨-, -, #H, -, -⟩
  iexact H

/-- The fields epaxos reads (`r.N`, `r.Id`, the flags; through the embedded pointer). -/
theorem fwRO_fields (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs) :
    fwRO (GF := GF) γ r id L p ⊢
      fld r go!"N" ↦□ W64 L.length ∗ fld r go!"F" ↦□ W64 2 ∗ fld r go!"Id" ↦□ W32 id ∗
      fld r go!"State" ↦□ p.st ∗ fld r go!"RPC" ↦□ p.tbl ∗ fld r go!"ProposeChan" ↦□ p.pchan ∗
      fld r go!"Thrifty" ↦□ true ∗ fld r go!"Exec" ↦□ true ∗ fld r go!"Dreply" ↦□ true ∗
      fld r go!"Shutdown" ↦□ false ∗ fld r go!"Stats" ↦□ p.stats ∗
      p.stats ↦□ replica.defs.Stats.mk p.statsMap ∗ fld r go!"Alive" ↦□ p.alive ∗
      ⌜L.length = nRep ∧ id < L.length⌝ := by
  rw [fwRO_unseal]; unfold fwRODef
  iintro #H
  icases H with ⟨-, -, HN, HF, HId, -, -, -, -, -, -, -, -, -, -, HAl, HSt, HRPC, -, HStats, HSm,
    HSh, HPc, -, HTh, HEx, -, HDr, -, -, -, %HL, -⟩
  iframe #
  ipureintro; exact HL

theorem fwFrozen_fields (γ : EpNames) (r : Loc) (id : Nat) (p : FwPtrs) :
    fwFrozen (GF := GF) γ r id p ⊢ fld r go!"Beacon" ↦□ false ∗ fld r go!"Durable" ↦□ false := by
  rw [fwFrozen_unseal]; unfold fwFrozenDef
  iintro ⟨#Hb, #Hd, -, -⟩
  isplitl
  · iexact Hb
  · iexact Hd

/-- `ProposeChan` carries proposals. -/
theorem fwRO_proposeChanCap (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs) :
    fwRO (GF := GF) γ r id L p ⊢ ∃ γc : ChanNames, isChanBag γc p.pchan (proposal γ id) ∗
      ⌜sint.Z γc.chanCap < 2 ^ 32⌝ := by
  rw [fwRO_unseal]; unfold fwRODef
  iintro #H
  icases H with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%γc, Hp, %Hc⟩, -⟩
  iexists γc; iframe Hp; ipureintro; exact Hc

theorem fwRO_proposeChan (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs) :
    fwRO (GF := GF) γ r id L p ⊢ ∃ γc : ChanNames, isChanBag γc p.pchan (proposal γ id) := by
  iintro #H
  icases fwRO_proposeChanCap γ r id L p $$ H with ⟨%γc, Hp, -⟩
  iexists γc; iexact Hp

/-- `epaxos.alive(q)`: under `r.M` (and with the handle), read `Alive`. An update: `Alive` is
written without `r.M` while `ConnectToPeers` dials, and is in `r.M`'s invariant only once dialing
is done (the handle knows it). -/
theorem fwCore_alive (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs)
    (Rext : IProp GF) (E : CoPset) (hE : ↑fwN ⊆ E) :
    isReplicaFw γ r id L p Rext -∗ fwCore γ id L p ={E}=∗
      ∃ als : List Bool, ⌜als.length = L.length⌝ ∗ p.alive ↦* als ∗
        (p.alive ↦* als -∗ fwCore γ id L p) := by
  have hE' : ↑fwDepN ⊆ E := fun x hx => hE x (nclose_subseteq (ndot epN "replica") "dep" x hx)
  rw [isReplicaFw_unseal, fwCore_unseal]; unfold isReplicaFwDef fwCoreDef fwPhase1
  iintro ⟨-, -, -, ⟨%ns', #Hn', #Hd⟩, -⟩ ⟨%ns, %CWm, %CW, %RT, %sm, #Hn, #Hi1, #Hi2, Hp, Hr, Hrest⟩
  ihave %Heq := fwNames_agree $$ Hn Hn'
  subst Heq
  ihave Hp : |={E}=> fwPeers γ id L p.peers p.writers p.alive p.lat p.ewma $$ [Hp]
  · icases Hp with (Hp | ⟨Hk, Hlc⟩)
    · imodintro; iexact Hp
    iapply dep_take _ _ _ E hE' $$ Hi1 Hd [Hk] Hlc
    iright; iexact Hk
  imod Hp
  unfold fwPeers
  icases Hp with ⟨%cs, %ws, %als, %ls, Hps, Hws, Has, Hls, %Hlen, Hsl⟩
  imodintro
  iexists als
  iframe Has
  isplitr
  · ipureintro; exact Hlen.2.2.1
  iintro Has
  iexists ns, CWm, CW, RT, sm
  iframe Hn Hi1 Hi2 Hr Hrest
  ileft
  iexists cs, ws, als, ls
  iframe
  ipureintro; exact Hlen

/-- epaxos's statistics: under `r.M`, update `Stats.M`. -/
theorem fwCore_stats (γ : EpNames) (id : Nat) (L : List GoString) (p : FwPtrs) :
    fwCore (GF := GF) γ id L p ⊢ ∃ sm : GMap GoString w64, ownMap p.statsMap (DFrac.own 1) sm ∗
      (∀ sm' : GMap GoString w64, ownMap p.statsMap (DFrac.own 1) sm' -∗ fwCore γ id L p) := by
  rw [fwCore_unseal]; unfold fwCoreDef
  iintro ⟨%ns, %CWm, %CW, %RT, %sm, #Hn, #Hi1, #Hi2, Hp, Hr, Hcw, HCW, HRT, %HCR, Hcs, Hsm⟩
  iexists sm
  iframe Hsm
  iintro %sm' Hsm
  iexists ns, CWm, CW, RT, sm'
  iframe
  iframe #
  ipureintro; exact HCR

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
