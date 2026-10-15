# ReadIndex with a persistent atomic update: specification handoff for the raft library

For: the raft team (`origin/worktree-raft-rest`, read at `cec7448e9`).
From: the backend unit T1 (`notes/decisions.md` in the backend worktree, "Put and Get as persistent
atomic updates linearized by raft (unit T1)").
Status: proposal. Nothing here is built. Section 7 lists the open questions; everything marked
**[unsure]** is a point I could not settle from the sources.

All names are the branch's own (`RaftNames`, `isCommitted`, `readReq`, `readOk`, `readStateOk`,
`rdCred`, `RqRec`, `propAu`, `propSlot`, `propsOwn`, `raftCommitInv`, `raftN`, `commit_extend`,
`fire_one`/`fire_upto`, ...). New names are proposals; rename them freely.

---

## 1. Summary

- **What the client passes.** `RawNode.ReadIndex`/`node.ReadIndex` take a *persistent atomic
  update* `readAu γ Qr` over raft's **full committed log** (a new client-half ghost variable
  `rLog γ L`, `L : List raftpb.Entry`, positions = raft indices). The log does not change and the
  result `□ Qr L` is persistent. Today they take `readReq γ c Lc`, which the client allocates
  itself.
- **Where the update fires.** The update is deposited at the call (`read_deposit`, inside
  `raftCommitInv`). It fires once at once, on the committed log `Lc` of that moment, and then at
  **every** ghost commit after it, once for each intermediate prefix (`fire_one`). It fires
  whatever the request's read index turns out to be. The ghost state never needs to know the
  read index to fire. **This corrects the brief**, which asked to fire "from the safe index on,
  including the prefixes committed before it was fixed": an update over the live log can only
  be fired at the current log, so prefixes already committed cannot be fired later. See §4.1.
- **The read index's guarantee, unchanged in form.** `readReq γ c Lc` now records the **exact**
  committed log at the deposit, not a lower bound the client knew. `readOk γ c i`
  (`|Lc| ≤ i`) and the whole doom/confirm argument (`read_arrive_core`, `rqRecOk_confirm`,
  `HbAckOk`, ...) stay as they are. A `ReadState{Index := i, RequestCtx := c}` still carries only
  `readStateOk` (timeless). The client combines it with its own handle `isRead γ c Qr` to get the
  witness `readWit γ c Qr i`. That witness gives `▷ ▷ □ Qr L` for every committed `L` with
  `i ≤ |L|` (`read_collect`).
- **One spec for any number of voters.** The premise `1 < GMap.size γ.reCfg` goes from
  `RawNode.ReadIndex.spec`, `node.ReadIndex.spec`, `raft.Step.spec`, `stepLeader`'s spec and
  `RawNode.Step.spec`. The `IsSingleton` branch (`raft.go:1343`) becomes a new `Step` rule,
  `readSingle`, refined from the same `readOk`. The rule is provable in the **static** mode,
  where all code proofs live today. In the dynamic mode it is **false**: your own
  `issues/raft-readindex-singleton-stale.md` has both counterexamples. Under reconfiguration the
  uniform spec needs that fix (or a run restriction). The task's brief says reconfiguration is
  handled because "the node applies the change only once its commit index has passed it". That
  is not sufficient (execution 1 of the issue). See §4.4.
- **Later credits.** A persistent update in an invariant has to be stripped of a later at every
  firing. So `commit_extend` (and with it the ghost step `ownRaftGhost_step`/`_stepC`/
  `ghost_stepCD`) takes **one `£ 1` per ghost step**. That one credit strips the whole registry
  at once. The per-slot credits go, along with `prop_deposit`'s `£ 1`.
- **Proposals.** These move to the same log. `propAu` becomes persistent, over `rLog` (the full
  log). It fires at **every** committed occurrence of its data. The ticket `propTok` and
  `firstOcc`/`cLog` leave raft's core, and a standing update `noopAu γ` covers raft's own entries
  (empty entries, conf changes).
- **`rdCred`** stays (arrivals stay unbounded under redelivery; positions must not wrap).
- **Freshness of contexts.** The `reReads` authority moves into `raftCommitInv`, because the
  deposit must read the exact log. The client keeps freshness through tokens, `rdFresh γ c`
  (new map `reRdFresh`, the pattern of `propFresh`/`reFresh`).

---

## 2. Ghost definitions

### 2.1 `RaftNames` changes (`Protocol/Ghost.lean`)

Current fields affected (quoted):

```lean
  /-- The proposal registry ... a ghost map `data ↦ (γq, γk)` ... -/
  reProps : GName
  /-- The client log (2026-10-10): a ghost variable, halved between `raftCommitInv` and
  the client (`cLog`), of the data of the committed client entries in commit order,
  first occurrences only. Only a deposited atomic update moves it. -/
  reCLog : GName
  /-- The read contexts (2026-10-12): a ghost map `ctx ↦ Lc` (persistent elements,
  `readReq`), the committed log when the context was created; the authority is in
  `raftCommitInv`, and creating a context consumes its fresh token (`propFresh`). -/
  reReads : GName
```

(The `reReads` comment already says "authority in `raftCommitInv`", but the code has the client
hold it: `readReq_alloc` takes `ghostMapAuth γ.reReads 1 R`, and the register's `regInv` holds
it. The proposal makes the comment true.)

Proposed:

```lean
  /-- The proposal registry: a ghost map `data ↦ γq` (persistent elements) of the data whose
  persistent update was deposited; `γq` names the update's result predicate. Authority in
  `raftCommitInv`. (Was `data ↦ (γq, γk)`; the ticket `γk` goes: results are persistent.) -/
  reProps : GName
  /-- The full committed log, client view: a ghost variable halved between `raftCommitInv`
  (always the global committed log) and the client (`rLog`). Only a deposited update moves it
  (`propAu` of the entry's data, or the standing `noopAu`). Replaces `reCLog`. -/
  reRLog : GName
  /-- The read registry: a ghost map `ctx ↦ (γq, Lc)` (persistent elements): `γq` names the
  read update's result predicate, `Lc` is the global committed log at the deposit. Authority in
  `raftCommitInv`. -/
  reReads : GName
  /-- The fresh read-context tokens: a ghost map `ctx ↦ ()` whose authority the client holds;
  `rdFresh γ c` (an element) is what a deposit consumes and the invariant keeps. -/
  reRdFresh : GName
```

Allocation (`Protocol/Facts.lean` ~1149/1297, which allocates `ghostMapAuth γ.reReads 1 ∅` for
the client today):

- the `reReads` authority now goes into the invariant;
- the client receives the `reRdFresh` authority (empty) and `rLog γ []`;
- the invariant also needs `noopAu γ` (§5), which mentions `γ`. So allocation is two steps.
  First allocate the names, which returns `rLog γ []` and the invariant's half. Then the client
  builds its update, and `raftCommitInv_alloc` takes the half and `noopAu γ`.

### 2.2 The client's log, the read update, the handle and the witness (`Protocol/GhostState.lean`)

```lean
/-- The client's half of the full committed log (positions are raft indices: entry `k` of `L`
has index `k + 1`; replaces `cLog`). -/
def rLog (γ : RaftNames) (L : List raftpb.Entry) : IProp GF :=
  ghostVar γ.reRLog (1 : Qp).half L

instance rLog_timeless (γ : RaftNames) (L : List raftpb.Entry) : Timeless (rLog (GF := GF) γ L)

section inv
variable [InvGS GF]

/-- A read's update: persistent, the log unchanged, a persistent result. Fired by the raft
proof at the deposit and at every commit after it, at the current committed log. -/
def readAu (γ : RaftNames) (Qr : List raftpb.Entry → IProp GF) : IProp GF :=
  iprop(□ AU <{ ∃∃ (L : List raftpb.Entry), rLog γ L }> @ ⊤ \ ↑raftN, ∅
              <{ rLog γ L, COMM □ Qr L }>)

instance readAu_persistent γ Qr : Persistent (readAu (GF := GF) γ Qr)

/-- Firing it: the invariant's half at `l` agrees with the client's, both unchanged. -/
theorem readAu_fire (γ : RaftNames) (Qr : List raftpb.Entry → IProp GF) (l : List raftpb.Entry) :
    ⊢ readAu γ Qr -∗ ghostVar γ.reRLog (1 : Qp).half l ={⊤ \ ↑raftN}=∗
      ghostVar γ.reRLog (1 : Qp).half l ∗ □ Qr l
```

(The proof is `propAu_fire`'s, without the `ghostVar_update_halves`.)

The registry entry and the request's facts:

```lean
/-- The fresh token for a read context `c`. -/
def rdFresh (γ : RaftNames) (c : List w8) : IProp GF := c ↪[γ.reRdFresh] ()

/-- The read context `c` was deposited when the global committed log was `Lc`.
(Was `c ↪[γ.reReads]□ Lc ∗ isCommitted γ Lc`; the meaning of `Lc` changes from "a committed
log the client knew" to "the committed log at the deposit". Same name, same persistence and
timelessness, so `isMessage`, `rdOwn`, `rqRecOk`, `readOk` keep their definitions.) -/
def readReq (γ : RaftNames) (c : List w8) (Lc : List raftpb.Entry) : IProp GF :=
  iprop(∃ γq : GName, c ↪[γ.reReads]□ ((γq, Lc) : GName × List raftpb.Entry) ∗ isCommitted γ Lc)

-- unchanged:
-- def readOk (γ : RaftNames) (c : List w8) (i : w64) : IProp GF :=
--   iprop(∃ Lc, readReq γ c Lc ∗ ⌜(Lc.length : Int) ≤ uint.Z i⌝)

/-- The client's handle on its deposited read: the update's result predicate. -/
def isRead (γ : RaftNames) (c : List w8) (Qr : List raftpb.Entry → IProp GF) : IProp GF :=
  iprop(∃ (γq : GName) (Lc : List raftpb.Entry),
    c ↪[γ.reReads]□ ((γq, Lc) : GName × List raftpb.Entry) ∗ savedPredOwn γq DFrac.discard Qr)

/-- The read witness: the handle and a read index `i` for the context. -/
def readWit (γ : RaftNames) (c : List w8) (Qr : List raftpb.Entry → IProp GF) (i : w64) :
    IProp GF :=
  iprop(isRead γ c Qr ∗ readOk γ c i)
-- both persistent; `isRead`/`readWit` are not timeless (saved predicate), so they stay out of
-- `isMessage`, `rdOwn` and `readStateOk`, which are timeless today.
```

`readReq_agree` keeps its statement (agreement of the pair gives `L1 = L2`). `readOk_prefix` and
`readStateOk_prefix` keep theirs.

The slot (the analogue of `propSlot`) and the registry clause:

```lean
/-- A read slot, for the committed log `l`: the result predicate (tied to `γq`), the update,
the deposit's log `Lc` (a prefix of `l`), and the results so far: `□ Qr` of every prefix of `l`
at least `Lc` long, i.e. of every log the update was fired at. -/
def readSlot (γ : RaftNames) (r : GName × List raftpb.Entry) (l : List raftpb.Entry) : IProp GF :=
  iprop(∃ Qr : List raftpb.Entry → IProp GF, savedPredOwn r.1 DFrac.discard Qr ∗ readAu γ Qr ∗
    ⌜r.2 <+: l⌝ ∗
    □ (∀ (n : Nat), ⌜r.2.length ≤ n ∧ n ≤ l.length⌝ → □ Qr (l.take n)))

/-- The read registry, for the committed log `l`. -/
def readsOwn (γ : RaftNames) (l : List raftpb.Entry)
    (RR : GMap (List w8) (GName × List raftpb.Entry)) : IProp GF :=
  iprop(ghostMapAuth γ.reReads 1 RR ∗ [∗map] c ↦ r ∈ RR, readSlot γ r l ∗ rdFresh γ c)
```

**Where the updates and credits live.** The updates sit in `readSlot` inside `raftCommitInv`
(under its later). There is **no credit per slot**, because a persistent update fires many
times. The single `£ 1` that `commit_extend` takes (§4.2) strips the later off the whole
registry: `▷ [∗map] ...` becomes `[∗map] ...` by `BigSepM.bigSepM_later` and
`lc_fupd_elim_later`. Every update is then fired as often as needed. The deposit needs no
credit, because it receives the update from the client un-latered.

**Mask.** Every update (read, proposal, `noopAu`) has outer mask `⊤ ∖ ↑raftN` and inner mask
`∅`, as `propAu` today. It is fired with `raftCommitInv` open, so `commit_extend` and
`read_deposit` must run at `⊤` (`commit_extend` is `={⊤}=∗` today; `ownRaftGhost_step` too).
A client's update body may open any invariant outside `raftN` (the server's `kvN`), but no
invariant the raft proof holds open at a commit. **[unsure]** I did not check every code path
that ends in `ownRaftGhost_step` for an enclosing open invariant. Of the paths that hold one,
`InvNode`'s `open_node` is the candidate. It opens `nodeN`-style invariants; are any open
around `run`'s `Step`?

### 2.3 `raftCommitInv`

Current (quoted):

```lean
def raftCommitInv (γ : RaftNames) : IProp GF :=
  inv raftN iprop(∃ l, ∃ (R : GMap (List w8) (GName × GName)),
               ownCommitted γ l ∗ committedJust γ l ∗ votesTbl γ ∗ propsOwn γ l R ∗
               winTbl γ)
```

Proposed:

```lean
def raftCommitInv (γ : RaftNames) : IProp GF :=
  inv raftN iprop(∃ l, ∃ (R : GMap (List w8) GName)
                       (RR : GMap (List w8) (GName × List raftpb.Entry)),
               ownCommitted γ l ∗ committedJust γ l ∗ votesTbl γ ∗ winTbl γ ∗
               ghostVar γ.reRLog (1 : Qp).half l ∗      -- the invariant's half: always `l`
               propsOwn γ l R ∗ readsOwn γ l RR ∗ noopAu γ)
```

(`propsOwn` loses its `ghostVar γ.reCLog ... (firstOcc ods)`; §5.)

### 2.4 The deposit and the collection (`Protocol/ReadIndex.lean`, replacing `readReq_alloc`)

```lean
/-- Depositing a read (at `⊤`: the update is fired at once, with the invariant open). The
client gets the exact committed log `Lc` of the moment, a prefix of which is every committed log
it knew (`L0`), the request's record and its handle. -/
theorem read_deposit (γ : RaftNames) (c : List w8) (Qr : List raftpb.Entry → IProp GF)
    (L0 : List raftpb.Entry) :
    ⊢ raftCommitInv (GF := GF) γ -∗ rdFresh γ c -∗ readAu γ Qr -∗ isCommitted γ L0 ={⊤}=∗
      ∃ Lc, ⌜L0 <+: Lc⌝ ∗ readReq γ c Lc ∗ isRead γ c Qr
```

How to prove it:

1. Open the invariant, which holds `l`.
2. `rdFresh γ c` rules out `RR !! c = some _`, by `ghostMapElem_ne` against the kept token, as
   in `prop_deposit`.
3. `readAu_fire` at `l` gives `□ Qr l`.
4. `saved_pred_alloc`, then `ghost_map_insert_persist c (γq, l)`.
5. The slot's results range over `n = |l|` only.
6. `Lc := l`. `L0 <+: l` follows from `isCommitted_prefix`, and `isCommitted γ l` from
   `ownCommitted_lb`.

```lean
/-- Collecting: a read witness at `i` and a committed log at least `i` long give the update's
result at that log, under the invariant's later and the saved predicate's. -/
theorem read_collect (γ : RaftNames) (E : CoPset) (c : List w8)
    (Qr : List raftpb.Entry → IProp GF) (i : w64) (L : List raftpb.Entry) :
    ↑raftN ⊆ E → uint.Z i ≤ (L.length : Int) →
    ⊢ raftCommitInv (GF := GF) γ -∗ readWit γ c Qr i -∗ isCommitted γ L ={E}=∗ ▷ ▷ □ Qr L
```

How to prove it:

1. `readWit` gives `(γq, Lc)` with `|Lc| ≤ i ≤ |L|`.
2. The invariant gives `L <+: l`, so `n := |L|` lies in `[|Lc|, |l|]` and `l.take n = L`.
3. The slot's results give `▷ □ Qr' L`, and `saved_pred_agree` gives `▷ ▷ (Qr' L ≡ Qr L)`.
4. Close the invariant.

The shape is `prop_collect`'s (`▷ ▷`). A client that wants no laters spends `£ 2`
(`lc_fupd_elim_later` twice).

```lean
/-- From a handed-out `ReadState` whose context is the client's. -/
theorem readStateOk_readWit (γ : RaftNames) (st : ReadState) (c : List w8)
    (Qr : List raftpb.Entry → IProp GF) :
    ⊢ readStateOk (GF := GF) γ st -∗ isPropData γ st.RequestCtx' c -∗ isRead γ c Qr -∗
      readWit γ c Qr st.Index'
-- = readStateOk_readOk, framing `isRead`.
```

At the node, `node_readState_data` is unchanged. It returns
`∃ c, st.RequestCtx' ↦*□ c ∗ readOk γ.raft c st.Index'`, and the client frames its `isRead`. Add
`node_read_collect`, which is `read_collect` through `open_node`'s `Hcinv`, as `node_collect`
does for proposals.

---

## 3. The specs

### 3.1 `RawNode.ReadIndex.spec` (`Spec/go_etcd_io/raft/v3/RawNode__ReadIndex.lean`)

Current (quoted):

```lean
abbrev RawNode.ReadIndex.spec : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (rctx : GoSlice) (c : List w8)
    (Lc : List raftpb.Entry),
  1 < GMap.size γ.reCfg →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs ∗
      "#Hpd" ∷ isPropData γ rctx c ∗
      "#Hrq" ∷ readReq γ c Lc ∗
      "Hcred" ∷ rdCred γ 1 }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"ReadIndex")) (Val #rctx))
  {{ RET #(); "Hrn" ∷ ownRawNode γ rn id rs }}
```

Proposed:

```lean
abbrev RawNode.ReadIndex.spec : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (rctx : GoSlice) (c : List w8)
    (Qr : List raftpb.Entry → IProp GF) (L0 : List raftpb.Entry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs ∗
      "#Hpd" ∷ isPropData γ rctx c ∗
      "Hfr" ∷ rdFresh γ c ∗
      "#Hau" ∷ readAu γ Qr ∗
      "#HL0" ∷ isCommitted γ L0 ∗
      "Hcred" ∷ rdCred γ 1 }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"ReadIndex")) (Val #rctx))
  {{ RET #(); "Hrn" ∷ ownRawNode γ rn id rs ∗
      ∃ Lc, "%HL0c" ∷ ⌜L0 <+: Lc⌝ ∗ "#Hrq" ∷ readReq γ c Lc ∗ "#Hrd" ∷ isRead γ c Qr }}
```

- The proof is `read_deposit` (with `raftCommitInv` from `ownLogGhost_inv`) at `⊤`, then
  today's proof. `wp_raft_Step` gets `readReq γ c Lc` for the message's `isMessage`, as now.
- `L0` is optional (`[]`). It is what keeps the register's `Read` proof: its `regLb` log is a
  prefix of `Lc`.
- *Alternative*: keep the spec taking `readReq` (minus the size premise) and export
  `read_deposit` as a ghost lemma the client applies just before the call. That is equivalent,
  and the code proof changes less. I put the update in the spec because the user's design reads
  "the caller provides a persistent update to ReadIndex".

### 3.2 `node.ReadIndex.spec` (`Spec/go_etcd_io/raft/v3/node__ReadIndex.lean`)

Current (quoted):

```lean
abbrev node.ReadIndex.spec : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc) (rctx : GoSlice) (c : List w8)
    (Lc : List raftpb.Entry),
  1 < GMap.size γ.raft.reCfg →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode γ id n ∗
      isPropData γ.raft rctx c ∗ readReq γ.raft c Lc ∗ rdCred γ.raft 1 }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"ReadIndex"))
      (Val #(interface.ok context.backgroundCtxVal))) (Val #rctx))
  {{ (err : GoInterface), RET #err; True }}
```

Proposed (no voter-count premise):

```lean
abbrev node.ReadIndex.spec : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc) (rctx : GoSlice) (c : List w8)
    (Qr : List raftpb.Entry → IProp GF) (L0 : List raftpb.Entry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode γ id n ∗
      isPropData γ.raft rctx c ∗ rdFresh γ.raft c ∗ readAu γ.raft Qr ∗
      isCommitted γ.raft L0 ∗ rdCred γ.raft 1 }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"ReadIndex"))
      (Val #(interface.ok context.backgroundCtxVal))) (Val #rctx))
  {{ (err : GoInterface), RET #err;
      ∃ Lc, ⌜L0 <+: Lc⌝ ∗ readReq γ.raft c Lc ∗ isRead γ.raft c Qr }}
```

The deposit happens at the start, on the caller's goroutine (`open_node`'s `Hcinv`, at `⊤`),
before the request goes onto `recvc`. The post holds whatever `err` is. If the request is
dropped (no leader, node stopped), the update stays deposited and keeps firing, which does no
harm. No `ReadState` then names `c`, so no witness is ever formed.

### 3.3 What `Ready` delivers

`RawNode.Ready.spec`'s `"#Hrs_ok" ∷ ([∗list] st ∈ sts, readStateOk γ st)` is **unchanged**, as are
`readStateOk` (quoted below) and `node.Ready`/`node_readState_data`:

```lean
def readStateOk (γ : RaftNames) (st : ReadState) : IProp GF :=
  iprop(∃ c, isPropData γ st.RequestCtx' c ∗ readOk γ c st.Index')
```

The client turns a `ReadState{Index := i, RequestCtx := rctx'}` with bytes `c` into
`readWit γ c Qr i` (`readStateOk_readWit`, or `node_readState_data` plus its `isRead`), and then
into `▷ ▷ □ Qr L` for every committed `L` with `i ≤ |L|` (`read_collect`). A `ReadState` may
arrive several times for one context (redelivery), and each copy carries its own `readOk`.

### 3.4 The safe-index lemma

What is provable, precisely:

> **(S)** If a `ReadState` with index `i` names context `c`, then `|Lc| ≤ i`, where `Lc` is the
> global committed log *at the deposit of `c`*. The deposit happens inside the
> `ReadIndex` call, so `Lc` extends the global committed log at the call's start. Ghostly:
> `readOk γ c i`, with `readReq γ c Lc` from `read_deposit` (and `⌜L0 <+: Lc⌝` for every
> committed `L0` the caller held at the call).

The consumer needs (S): `i ≥` the committed length at the call. With the firing discipline of
§4.1, (S) is exactly what makes `readWit` sound: every committed `L` with `|L| ≥ i ≥ |Lc|` was
the current log at some moment after the deposit, so the update was fired at it.

The stronger internal fact, `|P_arrival| ≤ i` (the global log at the request's *arrival at the
leader*, for a confirmed record), is what `read_arrive_core` plus `rqRecOk_confirm` actually show.
It implies (S), since `Lc <+: P_arrival` (`isCommitted_prefix` at arrival). It stays internal:
no `RqRec` records `P_arrival`, and the consumer does not need it.

---

## 4. Proof obligations and plan

### 4.1 Where the read updates fire (and why not "from the safe index on")

- **At the deposit**: at the current `l` (`read_deposit`).
- **At every ghost commit**: `commit_extend` extends the global log entry by entry (`fire_upto`
  → `fire_one`), possibly by many entries in one call. In `fire_one`, after the entry `e` is
  appended (`l' = l ++ [e]`, `ownCommitted_extend`) and after any proposal or no-op update moved
  `rLog` (§5), it fires **every** slot's `readAu` at `l'` and extends each slot's results to
  `n = |l'|` (`readSlot` at `l'`). Order matters: first the entry's own update (which moves the
  log), then the reads (at the new log). Slots stay valid as `l` grows: `r.2 <+: l` is kept, and
  the results' `□ ∀ n ≤ |l|` is extended by the new `n` (the analogue of `slot_grow`).
- **Not** conditioned on the read index. The read index is not known when a commit happens
  (before the heartbeat quorum confirms the request), and it is never known for a doomed or lost
  request. A persistent update fired at the current log is sound whenever it is fired after the
  deposit, so firing every deposited read at every commit is safe. The read index enters only in
  `readWit`, which promises results only at logs `|L| ≥ i ≥ |Lc|`, every one of which was fired.
- **Correction to the brief and to the consumer's draft** ("Each commit step fires every
  registered read update whose safe index the new committed log reaches, and registration fires
  it if the log is exactly `i` long", and "firing for all prefixes between `i` and the current
  committed length when the index is fixed"). This cannot be done. The update's atomic state is
  `rLog γ L` at the current value, so a prefix committed before the firing moment cannot be fired
  at later. Firing from the deposit on is what makes it work, and the deposit is the only place
  where the safe index meets the ghost state (through `|Lc| ≤ i`). The consumer's notes
  (`decisions.md`, unit T1, "What the raft library's proof must prove") should be changed to
  say so. I did not edit them.

### 4.2 Credits: one `£ 1` per ghost step

`commit_extend` gains `£ 1`:

```lean
theorem commit_extend (γ : RaftNames) (t n : w64) (G : List raftpb.Entry) (ldr : w64) :
    ⊢ raftCommitInv (GF := GF) γ -∗ cq γ t n G -∗ isLeader γ ldr t -∗ cmtLb γ ldr t n -∗ £ 1
      ={⊤}=∗ isCommitted γ (G.take (uint.Z n).toNat)
```

- The credit strips the later off `propsOwn`, `readsOwn` and `noopAu` at once. This replaces
  `propsOwn_open`/`propsOwnL`'s per-slot `▷`.
- `fire_one`/`fire_upto` then take the un-latered registries.
- The credit travels up the ghost-step lemmas:
  - `ownRaftGhost_step_commit`;
  - `ownRaftGhost_stepC`/`ownRaftGhost_step`;
  - `ownRaftGhostR_stepR` (dynamic);
  - `ghost_stepCD`, `ghost_step_md`, `ghost_step_recv` (`StepGhostMode.lean`, `raft__Step/Base.lean`).
- Simplest is uniform: every ghost step takes `£ 1`, and only `commit` uses it.
- The branch proofs get it from a pure step (`wp_auto_lc 1`/`wp_pure_lc`), since
  `hlc := HasLC.hasLC`.
- The model-level results (`raft_reconfig_step`, `Results.lean`) take `£ 1` per step as a
  premise.
- `prop_deposit` loses its `£ 1`, and `node_propose_ghost`'s `£ 1` goes too.

**[unsure]** whether every branch proof has a pure step before its ghost update. If one does not,
a `£ 1` in `raft.Step.spec`'s precondition (one per call) is the fallback, which callers pay from
their own pure steps.

### 4.3 When the read index is fixed (unchanged machinery, listed for the refinement)

The read index plays no part in firing, and its proof is today's. A request's index is decided at
its **arrival at the leader** of `T`:

- `Step.readArrive`: `sendMsgReadIndexResponse`, with the record `((c, s.commit), d)` by
  `ownRaftGhost_read_arrive`/`read_arrive_core`;
- `Step.readRelease`: `releasePendingReadIndexMessages` after `maybeCommit`, for requests parked
  by `Step.readPend` while `!committedEntryInCurrentTerm`.

It is **confirmed** when a quorum acknowledges the position:

- `Step.readAck`: `recvAck` plus `readonlyAdvance` (`maybeAdvance`);
- `rqRecOk_confirm` / `rqRecOk_confirm_dyn` give `readOk γ c i`.

It **reaches the client** as follows:

- for a local request (`From = 0` or `id`), as a `ReadState` through `preadRespondAll`;
- for a forwarded one (`Step.readFwd`, follower `MsgReadIndex` with `To := lead`, `Term := 0`),
  as a `MsgReadIndexResp` carrying `readOk` in `isMessage`, which the follower turns into a
  `ReadState` (`Step.readState`).

None of these lemmas changes: `readReq`'s new definition has the same persistence and
timelessness, and `readReq_agree` still holds.

### 4.4 The singleton branch: the same spec (static mode), false under reconfiguration

**Model.** A new rule, for `stepLeader`'s `IsSingleton` branch (`raft.go:1341-1347`), which
answers with `r.raftLog.committed` before `committedEntryInCurrentTerm`:

```lean
  /-- `stepLeader`'s `MsgReadIndex` at a single voter (`IsSingleton`): answered at once at the
  commit index, with no heartbeat round and no `committedEntryInCurrentTerm`. -/
  | readSingle (m : Msg) (s : PState) :
      m.ty = .readIndex → s.role = .leader → CfgSingleton cfg →
      Step s [m] (preadRespondAll id s [⟨s.commit, m.src, m.entries⟩])
```

`CfgSingleton cfg` is `Voters[0]` of size 1 and `Voters[1]` empty, as `IsSingleton` reads it.
Statically it is `GMap.size γ.reCfg = 1`. Check that `preadRespondAll` takes a list of
`ReadReq`s this way (the record is `⟨index, from, ents⟩`, as in `readArrive`).

**Refinement** (`ownRaftGhost_step_read_single`). It needs `readOk γ c s.commit` from the
message's `readReq γ c Lc`. Inside the invariant `Lc <+: P` (the global log), so it suffices to
show:

```lean
/-- At a static single voter, the leader's commit index covers the global committed log. -/
theorem single_commit_bound (γ : RaftNames) (id : w64) (s : PState) (P : List raftpb.Entry) :
    γ.reDyn = none → GMap.size γ.reCfg = 1 → s.role = .leader →
    ⊢ ownRaftGhost (GF := GF) γ id s md -∗ committedJust γ P -∗ ... ⌜(P.length : Int) ≤ uint.Z s.commit⌝
```

The proof takes the cases of `committedJust` (as `read_arrive_core` does) with `cq γ t n G`,
`isLeader γ ldr t` and `cmtLb γ ldr t n`:

- **`t > T`** is impossible. The quorum of a one-voter configuration is `{id}`
  (`JQuorum`/`IsQuorum`), so `isAcked γ id t n` holds with `t > s.term`, against
  `ownRaftGhost_ack_le`. Equivalently, take `rqRecOk_confirm` with `Q := {id}`: the leader's own
  acknowledgement confirms its record, and `ownRaftGhost_not_doomed` for `id` gives the premise.
- **`t = T`**: `isLeader_unique` gives `ldr = id`, then `lcmOwn_bound_keep`, as now.
- **`t < T`**: two facts the branch does not have yet.
  1. **`ldr = id`**: every campaigner is a voter. The model's `Step.campaign` has `id ∈ cfg`,
     but no ghost record keeps it. Proposed: `isCampK` gains `⌜γ.reDyn = none → c ∈ γ.reCfg⌝`,
     established by the campaign refinement. With `reCfg = {id}` and the winner's `isCampK`
     (`isWinCore`), `ldr = id` follows.
  2. **`n ≤ s.commit` for a past term**. `lcmOwn` keeps only the current lead term's authority:
     `lcmLead` is `True` off-lead, and `lcmOwn_mono'` drops it. Proposed: `lcmOwn` keeps, for
     every `t ↦ γc ∈ lcm`, `∃ c, monoNatAuthOwn γc 1 c ∗ ⌜c ≤ uint.nat s.commit⌝`. Only the
     current lead term's value grows. It is preserved since the commit index never decreases
     (`Step.commit_mono`; `lcmOwn_mono'` already has the premise `s.commit ≤ s'.commit`). Then
     `cmtLb γ id t n` gives `n ≤ s.commit`.

**Code.** In `stepLeader`'s spec, the `MsgReadIndex` case gains the `IsSingleton` branch, with
`ProgressTracker.IsSingleton.spec` and `responseToReadIndexReq` (both already proved). The spec
premises change as follows:

| Spec | Premise now | Premise after |
|---|---|---|
| `raft.Step.spec` | `(m.Type' = MsgReadIndex → m.Term' = W64 0 ∧ 1 < GMap.size cfg)` | `(m.Type' = MsgReadIndex → m.Term' = W64 0)` |
| `stepLeader` | `(m.Type' = MsgReadIndex → 1 < GMap.size cfg ∧ ents ≠ [])` | `ents ≠ []` |
| `RawNode.Step.spec` | `(m.Type' = MsgReadIndex → 1 < GMap.size γ.reCfg)` | dropped |

The register's `deliver` and `Register.Read` lose `1 < size reCfg`.

**Reconfiguration (dynamic mode, B7): the spec is false there as the code stands.** This is your
`issues/raft-readindex-singleton-stale.md` (2026-10-14, with a Go reproduction), which has two
executions.

- **Execution 1.** `{1,2}` → `remove 2`. Node 1 applies the change but misses the commit of `x`
  at index 3. It wins term 2 alone and answers at its commit index 2 before its empty entry
  commits. The brief's justification, "it applies the change only once its commit has passed
  it", is true here, and the read is stale all the same.
- **Execution 2.** A removed leader, with `IsSingleton` true of a configuration it is not in.

So the uniform spec is provable now in the static mode (all code proofs). For B7 it needs the
issue's fix (`readindex-singleton-fix.patch`: the shortcut moved after
`committedEntryInCurrentTerm`, and taken only if the voter is `r.id`; the request then goes
through `readArrive`, and the same proof applies) or a run restriction. That is a decision for
the user, not a proof gap. The server's contract has no voter-count premise (user's decision), so
it inherits this.

### 4.5 `rdCred`

**Keep it.** Its job, keeping positions in a leader's term from wrapping when arrivals are
unbounded because the transport redelivers, is independent of the update. One deposit per
context (`rdFresh`) bounds deposits, not arrivals. Its flow is unchanged: client →
`MsgReadIndex` → leader's stash (`rdLead`); `Ready` hands out queued requests' credits.

### 4.6 What changes in the existing files

| File | Change |
|---|---|
| `Protocol/Ghost.lean` | `RaftNames`: `reCLog` → `reRLog`; new `reRdFresh`; the value types of `reReads` (`GName × List raftpb.Entry`) and `reProps` (`GName`); doc comments. |
| `Protocol/GhostState.lean` | `readReq` (definition, §2.2); new `rLog`, `readAu`, `readAu_fire`, `rdFresh`, `isRead`, `readWit`, `readSlot`, `readsOwn`, `noopAu`; `propAu`, `propAu_fire`, `propSlot`, `propsOwn`, `isProp` changed (§5); `cLog`, `propTok` removed; `raftCommitInv` (§2.3); `lcmOwn` (§4.4, past terms). `readOk`, `rqRecOk`, `doomed`, `isMessage`, `rdLead`, `rdOwn`, `readStateOk` unchanged. |
| `Protocol/ReadIndex.lean` | `readReq_alloc` → `read_deposit`; new `read_collect`, `single_commit_bound`; `readReq_agree`, `readOk_prefix` re-proved (same statements). |
| `Protocol/LeaderCompleteness.lean` | `fire_one`, `fire_upto`, `slot_grow`, `propsOwn_open`/`propsOwnL` (the per-slot later goes), `commit_extend` (`£ 1`). |
| `Protocol/Facts.lean` | `prop_deposit` (no `£`, persistent update), `prop_collect` (§5), `firstOcc_deposited` (now over `rLog`'s entries), the allocation lemmas (~1149, ~1297), `ownRaftGhost` step wrappers at 1330/1356 (`£ 1`). |
| `Protocol/Model.lean` | `Step.readSingle`. `firstOcc` stays for the register only. |
| `Protocol/Refinement.lean`, `RefinementDyn.lean` | `ownRaftGhost_step_commit`, `ownRaftGhost_stepC`, `ownRaftGhost_step`, `ownRaftGhostR_stepR` (`£ 1`); new `ownRaftGhost_step_read_single` (static); the campaign refinement records voter membership (`isCampK`). |
| `StepGhostMode.lean`, `raft__Step/Base.lean`, `raft__Step/*.lean` | `£ 1` through `ghost_stepCD`/`ghost_step_md`/`ghost_step_recv`; branch proofs take it from a pure step. |
| `Spec/stepLeader.lean` + proof; `Spec/raft__Step.lean`; `Spec/RawNode__Step.lean` | the singleton branch; the size premises dropped. |
| `Spec/RawNode__ReadIndex.lean`, `Spec/node__ReadIndex.lean` + proofs | §3.1, §3.2. |
| `InvNode.lean` | `propArg`/`propRes`/`node_propose_ghost` (persistent update, no `£`, no ticket); `node_collect` (§5); new `node_read_collect`. `node_read_register`, `node_readState_data` unchanged. |
| `InvRawnodeReady.lean` | new `readStateOk_readWit`; `readStateOk_readOk`/`_prefix` unchanged. |
| `examples/register` (`Defs`, `Alloc`, `Init`, `Register__Read`, `Register__do`/`apply`/`Get`/`Put`, `Adequacy`) | `regInv` holds `rLog` (not `cLog`) and builds `noopAu`; `regFold` becomes a function of the full log (`firstOcc` of its entries' data, which the register's Go dedup justifies); `MintOk` over `reRdFresh` instead of the `reReads` authority; `Read` passes `Qr := fun _ => True`, `L0 :=` its `regLb` log; its propose path passes a persistent update. |

The model-level read results (`raft_reconfig_read_states`, `raft_reconfig_read_index`) keep
their statements.

---

## 5. Proposals (short): a persistent update over the full log, fired at every occurrence

etcd applies every committed occurrence of an entry's data, so the proposer's update must fire at
each one. It is over the same `rLog`.

Current (quoted):

```lean
def propAu (γ : RaftNames) (d : List w8) (Q : List (List w8) → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (L : List (List w8)), cLog γ L }> @ ⊤ \ ↑raftN, ∅
          <{ cLog γ (L ++ [d]), COMM Q L }>)

def propSlot (γ : RaftNames) (d : List w8) (γp : GName × GName) (L : List (List w8)) :
    IProp GF :=
  iprop(∃ Q : List (List w8) → IProp GF, savedPredOwn γp.1 DFrac.discard Q ∗
    ( (⌜d ∉ L⌝ ∗ £ 1 ∗ propAu γ d Q)
    ∨ (∃ L0, ⌜L0 ++ [d] <+: L ∧ d ∉ L0⌝ ∗ (Q L0 ∨ token γp.2)) ))
```

Proposed:

```lean
/-- A proposal's update: persistent; the linearizer (raft) chooses the entry `e`, a normal entry
whose proposed slice holds `d`; fired at every committed occurrence. -/
def propAu (γ : RaftNames) (d : List w8) (Q : List raftpb.Entry → IProp GF) : IProp GF :=
  iprop(□ AU <{ ∃∃ (Le : List raftpb.Entry × raftpb.Entry),
                  rLog γ Le.1 ∗ entDataIs γ Le.2 (some d) }> @ ⊤ \ ↑raftN, ∅
              <{ rLog γ (Le.1 ++ [Le.2]), COMM □ Q Le.1 }>)

/-- The standing update for raft's own entries (a leader's empty entry, a refused conf change's
replacement, a conf-change entry: `entDataIs γ e none`). The client gives it at allocation;
it lives in `raftCommitInv`. -/
def noopAu (γ : RaftNames) : IProp GF :=
  iprop(□ AU <{ ∃∃ (Le : List raftpb.Entry × raftpb.Entry),
                  rLog γ Le.1 ∗ entDataIs γ Le.2 none }> @ ⊤ \ ↑raftN, ∅
              <{ rLog γ (Le.1 ++ [Le.2]), COMM True }>)

/-- A proposal slot, for the committed log `l`: the result predicate, the update, and the
results at every occurrence of `d` in `l` (the log before it). -/
def propSlot (γ : RaftNames) (d : List w8) (γq : GName) (l : List raftpb.Entry) : IProp GF :=
  iprop(∃ Q : List raftpb.Entry → IProp GF, savedPredOwn γq DFrac.discard Q ∗ propAu γ d Q ∗
    □ (∀ (m : Nat) (e : raftpb.Entry), ⌜l[m]? = some e⌝ → entDataIs γ e (some d) →
         □ Q (l.take m)))

def propsOwn (γ : RaftNames) (l : List raftpb.Entry) (R : GMap (List w8) GName) : IProp GF :=
  iprop(∃ (ods : List (Option (List w8))),
    ([∗list] e;o ∈ l;ods, entDataIs γ e o) ∗
    ghostMapAuth γ.reProps 1 R ∗
    [∗map] d ↦ γq ∈ R, propSlot γ d γq l ∗ propFresh γ d)

def isProp (γ : RaftNames) (d : List w8) (γq : GName) (Q : List raftpb.Entry → IProp GF) :
    IProp GF :=
  iprop(d ↪[γ.reProps]□ γq ∗ savedPredOwn γq DFrac.discard Q)
```

- **`fire_one`.** For entry `e` with data `o`, under the step's single credit:
  - `o = some d`: `deposited γ d` gives the slot `γq`; fire `propAu` (`rLog`: `l` → `l ++ [e]`,
    `□ Q l`); add `m = |l|` to the slot's results.
  - `o = none`: fire `noopAu`.

  Then extend `ownCommitted`, fire every read slot at `l ++ [e]` (§4.1), and `slot_grow` the
  other proposal slots: their results at `l` stay valid at `l ++ [e]`, since `take` agrees below
  `|l|`. The `by_cases Hfire` on `firstOcc` goes, because the update fires every time.
- **`prop_deposit`**:

  ```lean
  raftCommitInv γ -∗ propFresh γ d -∗ propAu γ d Q ={E}=∗ ∃ γq, isProp γ d γq Q
  ```

  No credit, no ticket. Freshness still gives one deposit per data: only one update can move
  `rLog` at an occurrence, so two updates for one data would be ambiguous. A retry carries the
  persistent `deposited γ d`.
- **`prop_collect`** (every occurrence, persistent, no ticket):

  ```lean
  theorem prop_collect (γ : RaftNames) (E : CoPset) (d : List w8) (γq : GName)
      (Q : List raftpb.Entry → IProp GF) (L : List raftpb.Entry) (m : Nat) (e : raftpb.Entry) :
      ↑raftN ⊆ E → L[m]? = some e →
      ⊢ raftCommitInv γ -∗ isProp γ d γq Q -∗ isCommitted γ L -∗ entDataIs γ e (some d) ={E}=∗
        ▷ ▷ □ Q (L.take m)
  ```

  `node_collect` follows.
- **How etcd's server consumes it.**
  - `kv_prop_au` builds `propAu` with `kvInv` open, and on the commit applies `kvEntry` of `e`'s
    bytes. The bytes come from `entDataIs γ e (some d)` in the binder, through `isPropData`,
    which is persistent; `propDataN` is not `raftN`.
  - `kvInv` builds `noopAu` (a no-op in the KV model).
  - `srvPropWit γ d Q` is `isProp` plus `prop_collect`.
  - The binder is a pair because I am **[unsure]** whether the Lean AU notation takes two `∃∃`
    binders. Both uses in the repository have one (`GhostState.lean:836`, `InvRequest.lean:143`).
  - The consumer's draft has `∃∃ L e, srvRLog γ L ∗ ⌜e.typ = W32 0 ∧ e.data = d⌝` over
    `EntryModel`. Here the entry is a `raftpb.Entry`, and its data is a slice whose bytes
    `entDataIs`/`isPropData` give (§6).

---

## 6. Mapping to the server's contract

The consumer's definitions are quoted from the backend worktree's `decisions.md`, unit T1:

```
srvReadAu γ Qr := □ AU <{∃∃ L, srvRLog γ L}> @ ⊤ ∖ ↑srvRaftN, ∅ <{srvRLog γ L, COMM □ Qr L}>
srvReadWit γ Qr i := □ ∀ L, srvRLogLb γ L -∗ ⌜uint.Z i ≤ uint.Z ai₀ + L.length⌝ ={⊤}=∗ □ Qr L
```

The server's contract is stated against etcd's own raft dependency (`EtcdDeps`, raft v3.7), whose
specs are axioms. No Lean module imports both. So this mapping is the argument a proof of the
contract would make from these specs, not an import.

- **Names.** `srvRaftN` ↔ `raftN`. `ServerRaftNames` carries the `RaftNames`, the start index
  `ai₀`, and the committed prefix `P₀` with `|P₀| = uint.nat ai₀` and `isCommitted γ P₀`. There
  is no snapshot after `run` starts (`rnSnapOnce`), so `P₀` is fixed.
- **The log.**

  ```
  srvRLog γs L    := ∃ Ls, rLog γ (P₀ ++ Ls) ∗ entsModel γ Ls L
  srvRLogLb γs L  := ∃ Ls, isCommitted γ (P₀ ++ Ls) ∗ entsModel γ Ls L
  ```

  `entsModel γ Ls L : IProp` is persistent: entry-wise, `EntryModel` is the entry's
  `Term'`/`Index'`/`Type'` and the bytes its `entDataIs` gives (`[]` for `none` with the zero
  slice, a conf entry's `isPropData` bytes otherwise). It is a function of `Ls` given the
  persistent registries (agreement of `isPropData`, `entDataIs_agree`). `kvInv` keeps
  `entsModel` facts for its log; it learns each new entry's from the `entDataIs` in
  `propAu`/`noopAu`'s binder. If a stand-alone AU-to-AU conversion (`srvReadAu` → `readAu`
  without `kvInv` open) is wanted, `readAu`'s precondition should also hand out
  `isCommitted γ L ∗ ∃ ods, [∗list] e;o ∈ L;ods, entDataIs γ e o`. Raft has both when it fires.
  **[open]**: this costs raft nothing, but I left it out to match the consumer's draft, whose
  `kv_read_compose` builds the update with `kvInv` open.
- **Reads.** `srvReadAu γs Qr` is `readAu γ Qr'` with `Qr' Lf := ∃ Ls L, ⌜Lf = P₀ ++ Ls⌝ ∗
  entsModel γ Ls L ∗ □ Qr L`. In practice `kv_read_compose` builds `readAu` directly.
  - `ReadIndex(ctx, beBytes id)` is `node.ReadIndex` with `c := beBytes id`, `rdFresh` from the
    server's id generator (it holds the `reRdFresh` authority; ids are unique), and
    `L0 := P₀ ++` its applied log.
  - The returned `isRead` plus a `ReadState` for `c` (`readyData` → `readStateOk`) give
    `readWit γ c Qr' i`.
  - `srvReadWit γs Qr i` is then `read_collect` at `P₀ ++ Ls`. Its premise `i ≤ |P₀ ++ Ls|` is
    `uint.Z i ≤ uint.Z ai₀ + L.length`.
  - **Mismatch**: `read_collect` gives `▷ ▷ □ Qr' L` (invariant plus saved predicate). The
    consumer's `srvReadWit` is `={⊤}=∗ □ Qr L` without laters. It must take `£ 2` (and the
    server pays from a pure step), or carry the `▷ ▷`. The consumer's read loop already spends a
    credit for its own saved predicate (`readRegAt`).
- **Proposals.**
  - `srvPropAu γs d Q` is `propAu γ d Q'` (with `Q' Lf` the model of `Lf.drop ai₀`).
  - `srvPropWit` is `isProp` plus `prop_collect`.
  - The standing update is `noopAu`.
  - `rnReadyData`'s `□ E.C (d ++ ce)` carries `srvRLogLb γs (d ++ ce)`, from `RawNode.Ready`'s
    `isCommitted γ (rs.delivered ++ ce)` with `rs.delivered = P₀ ++ d`.

---

## 7. Open questions

1. **Firing discipline.** The design here fires every deposited read at the deposit and at every
   commit. It replaces the brief's "fire from the safe index on". Confirm with the user, and fix
   the consumer's T1 notes (§4.1).
2. **Singleton under reconfiguration.** The uniform spec holds in the static mode. In the dynamic
   mode (B7) it is false without the fix in `issues/raft-readindex-singleton-stale.md` (§4.4).
   Patch the pinned raft (a fork revision), restrict runs, or keep `readSingle` static-only?
3. **Credits.** One `£ 1` per ghost step (§4.2): check that every branch proof has a pure step
   before its ghost update, and that no commit happens at a mask below `⊤`.
4. **Static singleton facts** (§4.4): voter membership of campaigners (`isCampK`) and past-term
   commit bounds (`lcmOwn`). I could not find either. A lemma I missed may give them.
5. **Fresh contexts**: a separate token map `reRdFresh` (proposed), or the proposals' `reFresh`
   (one token space; the register's contexts and data are disjoint encodings). The register's
   `MintOk` moves either way.
6. **Laters at collection**: `▷ ▷` (as `prop_collect`) against the consumer's later-free
   `srvReadWit`/`srvPropWit` (§6).
7. **Two `∃∃` binders** in the AU notation, or the pair used above (§5).
8. **Facts in `readAu`'s precondition** (`isCommitted`, `entDataIs` of `L`): add them or not (§6).
9. **Deposit in the spec or as a ghost lemma** (§3.1). Both are sound; the code proof changes
   less with the lemma.
10. **Lease-based reads** stay out (`ReadOnlyOption = 0` premise), unchanged.
11. **Crash/restart** is out of scope, as today. The static singleton argument uses the commit
    index's monotonicity, which a restart from an older persisted `HardState.Commit` would
    break.
