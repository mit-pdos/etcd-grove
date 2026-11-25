# P9: the kv workload instance of `remote` (M1, `etcd_kv_safe_nocrash`)

Issue #54 (piece P9 of #50). Branch `etcd-safe-p9`, base `5a1c41d945` (`etcd-safe-main-r3/2026-11-25`).
Perennial pin `fce59af75` (matches `/shared/tmp/manifest-fce59af7.json`'s path checkout).

## State (2026-11-25, first session): stopped at the spec phase, for the lead

**The kv instance cannot be stated over `remote`'s interface as it is.** `Run.spec`/`Check.spec`
(`Net/Spec/.../lib/remote/{Run,Check}.lean`) take `PendDec R S` (`Net/Proof/.../lib/remote/Pend.lean:163`)
for a store `R : RBase GF St I O` and porcupine's model spec `S : ModelSpec GF (linkv.PSet St I)`.
For the kv workload `S` must be txnlin's `linkvtxnS` (`Proof/.../etcd/txnlin/Defs.lean:272`: `isModel
linkvtxnS` is what `txnlin.Model()`'s proof gives), so `St = MS` and `I = MI` (the model's
`MIn GoString GoString`). Four of `remote`'s requirements then fail, each for a reason of txnlin's
model, not of the proof:

1. **`genSpec gen (fun x => ∃ i, x = R.iv i)`** (Run.lean:51, Check.lean:42): `iv : MI → GoInterface`
   is a function, but `Gen` returns inputs that are not a function of their model input:
   `genFrom` (`examples/etcd/txnlin/linkvtxn.go:780-789`) puts `Val: v` in a transaction's get and
   delete operations and `Num: guess` in a value comparison, which `decTOp`/`decCmp`
   (`Abs.lean:55-67`) ignore. Two of `Gen`'s inputs decode to one `MI`; at most one is `iv` of it.
2. **`PendDec.ioOk_ok`/`ioOk_err`/`err`, for every `i : MI`**: `linkvtxnS.ioOk` needs `ValidIn x`
   (keys among `wks`, `decIn x = some i`), and `decIn` is partial (a transaction of at most one
   comparison, three then- and one else-operation, `Abs.lean:75`). An `MI` with another key, or a
   longer transaction, has no input `x` that satisfies both `ioOk` and `decIn x = some i`.
3. **`PendDec.ok : ∀ s i o, S.M.step s (iv i, ov o) = (pSeq R.B).step s (i, .ok o)`**, for every `o`:
   txnlin's decoder reads an output by its *input's* kind (`decOut kind y`, `Abs.lean:119`), so an
   output of another kind (a put's answer to a get) decodes as an answer of the input's kind, which the
   model may accept while `pSeq` of `.ok o` refuses it (`ppost` is empty: `B.step` never answers a get
   with a put). The two sides differ at `s = pInit`. The Pend proof uses `ok` only at
   `o = (R.B.step i st).2` with `st` the invariant's state (Pend.lean:352), where it holds when the
   state's revision fits (`decOut_outOf`, `Enc.lean:157`, needs `rev < 2 ^ 64`).
4. **`hinj : ∀ o o', R.encOut (R.ov o) = R.encOut (R.ov o') → o = o'`** (Run.lean:47): with `O = MO`
   and `ov o = boxOut (outOf o)`, `outOf` is not injective (`outOf (.get r none) = outOf (.put r)`,
   `Enc.lean:52`); with `O = Output` (the Go struct, whose encoding is injective), `B` must answer Go
   outputs, and `pSeq B` (over `Output`) and `pM TS decOp` (over `MO`) agree only up to `outOf`'s
   collisions at revisions past `2 ^ 64`, so (3)'s function equality over every `s` fails again.

None of this is a bug of kvremote or txnlin (the single-process proof, `txnlin/Inv.lean`, works
against lintest directly with `decIn`/`decOut`); it is `remote`'s interface, designed for the counter
and for models written for it (dsverify's kits use the Go types as `I`/`O`, gryffnet's `Kit.lean`
header), being narrower than txnlin's model.

## Proposal (for the lead; ledger 2026-11-25, "`remote.PendDec` cannot describe txnlin's model")

Generalize `remote`'s store, keeping every existing instance's statement (each gets the identity and
`True`):

- **`RBase GF St J I O`**: `I` the wire input (the Go value's index: for kv `VIn := {x : Input //
  GenIn x}`, which `Call.spec` takes and implies `ValidIn`, `iv x := boxIn x.1`), `J` the model's input (`MI`), `mi : I → J` (`decIn`, total on `VIn`), `B :
  PendSpec St J O`. The slot, the far side and `Do` keep `I`; the pending map, `PendOk` and the model
  state use `J` (`pendTok n (mi i)`). kv: `O := Output`, `ov := boxOut`, `B := TSo`, txnlin's `TS`
  with its answers mapped by `outOf` (`(TS.step j st).1`, `outOf (TS.step j st).2`; `isWrite`
  `TS`'s), so `PSilent`/`Closed` of `TSo` and `TS` coincide.
- **`RBase.good : St → Prop` with `sysState_good : ∀ st, sysState st ⊢ ⌜good st⌝`** (kv: `st.rev <
  2 ^ 63`, which the instance's `sysState` carries from the cluster's `kvRevFits`).
- **`PendDec`, in the "at a configuration" form** the Pend proof uses (Pend.lean:89-95, 352, 596, 620):
  - `ok : ∀ s c i, s c → R.good c.st → ∃ s', S.M.step s (R.iv i, R.ov (R.B.step (R.mi i) c.st).2) = some s'
    ∧ s' ⟨(R.B.step (R.mi i) c.st).1, c.pend⟩ ∧ PSet.Closed R.B s'`;
  - `errW`/`errR`: the same for `R.unk i`, to `⟨c.st, mi i :: c.pend⟩` (a write) or `c` (a read);
  - `ioOk_ok`, `ioOk_err`, `noObs` as now (over `I`, which is what makes them true for kv);
  - `init` as now. A lemma `PendDec.ofTotal` derives the new form from today's (`pSeq_ok`,
    `pSeq_errW_pending`, `pSeq_errR`, `pSeq_step_closed`), so the counter's and dsverify's instances
    change by one line each.
- `pendOk_ok`/`pendOk_errW`/`pendOk_errR` and their uses in `pend_commit_core`/`pend_choice` take the
  new fields; `Run.spec`/`Check.spec` change only in `RBase`'s type arguments and keep `hinj`.

For kv, `ok` is `decOut_outOf` (with `mStep_rev_le` and `good`) then `linkv.pSeq_ok` at `TS`,
`errW`/`errR` are `decOut_errOut` then `pSeq_errW_pending`/`pSeq_errR`, `ioOk_*` hold since `GenIn` (in `VIn`)
implies `ValidIn`, `hinj` is `EncOutput`'s injectivity, and `Gen`'s post (`linkvInOk`: `GenIn x`) gives `∃ i : VIn, x = iv i`.

Size: the library change ~150 lines in `Pend.lean`/`Defs.lean` and one line per instance (counter,
eight dsverify instances); `counter_remote_robust` and the dsverify statements unchanged (their
`Results` closures rebuild). Alternative, not recommended: a kit-style Go model for kvremote (a new
porcupine model and its proof, thousands of lines, and the kv check no longer txnlin's).

## What does not depend on the decision (the next session's first work)

- `enc`'s specs and proofs (`examples/etcd/dist/enc/enc.go`: `Enc.{U64,I64,Int,Bool,Str}`, `NewDec`,
  `Dec.{U64,I64,Int,Bool,Str,Done}`; `Proof/.../dist/enc/` has only `Base`/`Init`), and kvremote's
  `EncInput`/`DecInput`/`EncOutput`/`DecOutput` over Go values (`encInput x`, `decInput (encInput x) =
  (x, true)`, refusal of short, extended and bad-bool encodings), with `EncOutput`'s injectivity
  (`hinj`). `codecOk` is these plus `IsRead` (`IsWrite.spec`), `Unknown` (`errOut`) and `IsUnknown`.
- `Node`'s `opMaybe` from `txnlin.Call.spec` (already linked: `wp_Call`), once `sysState`'s shape is
  fixed: a write's `lin` is `callUpd`'s `kvOpAu1` at the cluster's `γk`, a read's `□ lin` its
  `kvReadAu` (the read form). This is where D7's one KV state enters (`etcdKV γk` in `sysState`, each
  member's `kvRegsAt` naming `γk`: `etcd-dist-plan.md` §D7, "How clients reach the cluster's one KV
  state").

## State (2026-11-25, second session): the `remote` change made; `enc` begun

**The `remote` change** (approved by the coordinator, `remote`'s owner, #28; ledger entry marked):
- `RBase GF St J I O` (`Net/Proof/.../lib/remote/Defs.lean`): `B : PendSpec St J O`, `mi : I → J`
  (default `fun i => i`), `good : St → Prop` (default `True`), `sysState_good : ∀ st, sysState st ⊢ ⌜good st⌝`
  (default proof by `pure_intro trivial`). `lin`/`slotUpd`/`codecOk`'s `IsRead` read `B` at `R.mi i`.
- `PendDec` (`Pend.lean`) in the "at a configuration" form (`ok`, `errW`, `errR` over `s c i` with `s c` and
  `R.good c.st`, each giving `∃ s'` with the step, the stepped configuration and `Closed`); `ioOk_*`, `noObs`,
  `init` as before. `PendDecTotal` (the old form, for `R : RBase GF St I I O`) and `PendDec.ofTotal (hmi)
  (h)`; `PendDec.pendOk_{ok,errW,errR}` replace the pure `pendOk_*`; `sysState_keep` takes `good` out of the
  invariant's `sysState`. The pending map, `pendTok`, `PendOk` and the model state are over `J`.
- `Do.spec`/`Run.spec`/`Check.spec` quantify `{J}` (with `[DecidableEq J] [Pos.Countable J]` for Run/Check)
  inside the statement, so callers' `(St := …) (I := …) (O := …)` are unchanged; `Robust.lean`'s
  `remote_robust{,RB}` quantify `R : RBase GF St I I O` (the counter's `refine` names no `J`).
- Instances: the counter (`counter/{Defs,ModelDefs,Shared,Client,Server}.lean`) and the seven dsverify kits
  (gryff, craq, swiftpaxos, epaxos, paxos, rabia, quepaxa): `RBase … X X …`, `PendDec … := .ofTotal (fun _
  => rfl) { … }`; the counter's `Client`/`Server` case on `(cR γs).B.isWrite ((cR γs).mi i)`.
- **Build evidence** (fk-lean2, worktree `wt/etcd-safe-p9`, `/shared/tmp/p9-build.sh`): `remote.Link`,
  `remote.counter.TopLevelRobustness`, `remote.counter.Linked`, the seven dsverify
  `TopLevelRobustness` (gryffnet, craqnet, swiftnet, epaxosnet, paxosnet, rabianet, quepaxanet) and the three
  `NonVacuityLinked` (gryff, rabia, quepaxa) all built (`etc/importers.py --leaves` of `remote/Defs.lean`:
  every leaf). `git diff --stat 8933c91f2d HEAD` over every `TopLevelRobustness.lean`/`TopLevelDefs.lean`:
  empty. No statement premise mentions the changed definitions except through `RBase.svc`/`remoteAddr`/
  `pendCtx` of the instances' own stores, which are unchanged for `J = I`. `etc/tier-check.py --check`: ok.

**`enc`** (`examples/etcd/dist/enc`): `Proof/.../dist/enc/Defs.lean` (`encU64 := u64Le`, `encBool`, `encStr`
(length then bytes), the prefix-injectivity lemmas `enc{U64,Bool,Str}_append_inj`; `ownEnc e bs` (the
slice, its capacity), `ownDec d bs ok` (any fraction), `decPost d bs ok en x`: success `∃ r, ok = true ∧ bs = en x
++ r` with `ownDec d r true`, or `∃ r, ownDec d r false`). Specs, all checked: `Spec/.../dist/enc/{Enc__U64,
Enc__I64,Enc__Int,Enc__Bool,Enc__Str,NewDec,Dec__U64,Dec__I64,Dec__Int,Dec__Bool,Dec__Str,Dec__Done}.lean`.
Proved (lean-check on fk-lean2): `Enc.{I64,Int}`, `Dec.{I64,Int}` (from `U64`), `Dec.Done`. The plan for the
codec: `Done = true` makes every read the success branch (a false flag stays false), so `DecInput`'s spec is
`{b ↦*{dq} bs} … {in ok. ok = true → bs = encInput in}` by chaining `decPost`, and `codecOk`'s `DecIn`/`DecOut`
and `hinj` follow from `encInput`/`encOutput`'s injectivity (the `_append_inj` lemmas field by field).

## State (2026-11-25, third session): `enc` proved and linked; kvremote's codec functions proved

- **`enc`**: all twelve functions proved (`Enc.{U64,Bool,Str}`, `NewDec`, `Dec.{U64,Bool,Str}` this session);
  `enc/Lemmas.lean` (defs: `u64Le_getElem`, `leToU64_take_succ`, copied from counter's `Codec.lean`; they belong
  in Perennial's `Std/Word/LittleEndian`); `enc/Link.lean` hand-written (`EtcdGrove.enc.{Enc,Dec}.wp_*`,
  `wp_NewDec`; `etc/gen-link.py` has no mode for it). `enc/Defs.lean` gains `decPost_elim`/`decPost_intro`
  (a read's outcome as one case, and back), which chain reads.
- **kvremote's codec** (`Proof/.../dist/kvremote/`): `Defs.lean` (`cmpBytes`, `tOpBytes`, `vrBytes`,
  `tResBytes`, `kvBytes`, `inputBytes`, `outputBytes`; `_append_inj` for each and `inputBytes_inj`/
  `outputBytes_inj`, bounded by the bytes' length `< 2 ^ 64`: a slice's points-to gives it, `ownSlice_len`).
  Specs (`Spec/.../dist/kvremote/`) and proofs of `enc{Cmp,TOp,VR,TRes,KV}`, `dec{…}` (`decPost` of the bytes),
  `EncInput`/`EncOutput` (`{True} … {b. b ↦* inputBytes x}`), `DecInput`/`DecOutput` (`{b ↦*{dq} bs} … {x ok.
  ok = true → bs = inputBytes x}`). The 14 proofs were generated by `/shared/tmp/p9-kvremote-gen.py` (one-off;
  the files are ordinary proofs, edit them directly).
- **Pitfall** (`word`): in `Enc.U64`'s loop, `word` in both branches of a `wp_if_destruct` gave a kernel error
  ("application type mismatch" of an auxiliary `_proof_1_3` across the branches); the else branch's bound by
  `omega` (`uint.Z (W64 8) = 8` by `decide`, `uint.Z j = uint.nat j` by `simp`) avoids it.
- **Build evidence** (fk-lean2, `/shared/tmp/p9-build.sh`): `enc.Link` built (head `8296ea4511`); the codec
  targets (`/shared/tmp/p9-targets-codec.txt`: `enc.Link` and the 14 kvremote proofs) at `188aae9446`: built
  (3594 jobs, exit 0). `etc/tier-check.py --check`: ok.

## State (2026-11-25, fourth session): the store `kvR γk`, `kvPendDec`, `Codec` proved and linked

- **The store** (`Proof/.../dist/kvremote/Store.lean`, defs): `kvR γk : RBase GF MS MI VIn VOut`.
  Departs from the plan (§11.3 step 1) in the output type: **`O := VOut := {y : Output // y.Err' = false ∧
  (outputBytes y).length < 2 ^ 63}`, not `Output`**. `RBase.encOut_len` bounds every encoding below `2 ^ 63`
  bytes, and `Run.spec`'s `hinj` wants `encOut ∘ ov` injective on all of `O`: no injection of all
  `Output`s (unbounded strings) into lists of bounded length exists, so `O` must be the outputs that fit;
  `Err' = false` because `codecOk`'s `IsUnknown` must answer `false` on every `ov o`. So the base store is
  `TSo` (`TS`'s step, its answer `kvOut o`: `⟨outOf o, _⟩` when it fits, else the zero output) and the guard
  is **`kvGood st := st.rev < 2 ^ 63 ∧ StoreLe inMax st.kv`** (values at most `inMax` bytes: then every
  answer's strings are, `mStep_le`, `outOf_le`, `outputBytes_le`, so the answer fits, `kvOut_good`).
  `I := VIn := {x : Input // GenIn x}`, `mi := kvMi` (the decoding); `encIn x := inEnc x.1` (`inputBytes`
  cut to `[]` past `2 ^ 63`: `GenIn` does not bound the fields `decIn` ignores; `EncInput`'s slice bounds the
  bytes at run time, `inEnc_eq`), `encOut := kvEncOut` (`outEnc` of a boxed `Output`), `unk _ := boxOut
  errOut`, `Eop := kvEop = srvRaftN ∪ kvN` (`kvEop_mask`: `⊤ \ kvEop = (⊤ \ srvRaftN) \ kvN`, `kvAu1`'s mask),
  `sysState := kvSys γk st := ∃ σ, etcdKV γk σ ∗ ⌜GoodKV σ ∧ linkv.absSt σ = st ∧ kvGood st⌝` (timeless).
  Laws: **`kvPendDec γk : PendDec (kvR γk) linkvtxnS`** (proved), **`kvR_hinj`** (`Run.spec`'s `hinj`),
  `Pos.Countable VIn`/`VOut` (field tuples, no `sem` needed), `reach_TSo`/`closed_TSo`, `inEnc_dec`/
  `outEnc_dec`, `kvEncOut_boxOut`, `boxIn_inj`/`boxOut_inj`. `Pos.Countable MI` is txnlin `Inv.lean`'s.
- **For step 3 (Node)**: `kvSys` of the next state needs `kvGood` of it: the value bound from `kvOut_good`'s
  `StoreLe` (with `absSt_step`), the revision from the server's `kvRoom σ` (`σ.rev + 4 ≤ 2 ^ 63`) given at the
  AU's commit (the next revision is at most `σ.rev + 1`). Note `Call.spec`'s `kvRevFits` is not enough alone
  (`kvRoom` of the old state is). `kvSys` deliberately carries `kvGood` (not `kvRevFits σ.rev`).
- **The codec**: `Spec/.../kvremote/Codec.lean` (`Codec.spec : ∀ γk, {pkgInit} Codec() {cd. codecOk (kvR γk)
  cd}`) and its proof (`Proof/.../kvremote/Codec.lean`, callees `EncInput`/`DecInput`/`EncOutput`/
  `DecOutput`/txnlin's `IsWrite`), checked. `kvremote/Link.lean` (hand-written, namespace
  `EtcdGrove.kvremote`): the 14 codec functions and `wp_Codec`, over `EtcdGrove.enc` and txnlin's `Link`
  (its `wp_IsWrite` from txnlin's `IsWrite`/`isWrite`/`thenOf`/`elseOf` proofs: txnlin's `Link` reaches the whole server).
- **Build evidence** (fk-lean2, `/shared/tmp/p9-build.sh`): `kvremote.Store`, the `Codec` spec and proof and
  `kvremote.Link` at `e2aa743ad7`: built (4970 jobs, exit 0), no `sorry` or axiom added. `etc/tier-check.py
  --check`: ok (Store defs, Codec proof, Link linking).

## State (2026-11-25, fifth session): `remote.lin` made abortable; the Node's update conversion proved

- **`remote.lin` could not be handed to etcd** (ledger 2026-11-25, "`remote.lin` cannot abort"): `Call.spec`'s
  write update is etcd's `kvOpAu1`, an Iris atomic update whose accessor must be abortable, and `lin` (a
  one-shot fancy update) gives `etcdKV γk σ` only by stepping. **Changed** (pending the coordinator's review,
  `remote`'s owner, before landing): `lin R i Φ := AU <{ ∃∃ st, sysState st }> @ ⊤ \ Eop, ∅ <{ sysState (step
  st).1, COMM Φ (step st).2 }>`; the old form is `linF` (`lin_linF : lin ⊢ linF`, for far sides that fire it;
  `linF_read_lin : □ linF ⊢ lin` for reads). Producers (`Pend.lean`): `pend_fire` and `pend_choice`'s write
  abort by closing `pendCtx` unchanged, lintest's update (`pend_commit_core`) now runs in the commit branch;
  `readNoop` and the read case build `□ linF` and convert. Consumers: counter `Server` (`lin_linF`), `Shared`'s
  `lin_mono` (by `aupd_intro`/`atomic_acc_wand`), the seven kits' `lin_opAU`/`lin_opU` (`(lin_linF ..).trans`),
  swift's `ClientLin` (twice), quepaxa's `lin_opAU` (was `⊣⊢ .rfl`, only `.1` used: now `⊢`). No
  `TopLevelRobustness.lean`/`TopLevelDefs.lean` text changed.
- **`kvremote/NodeUpd.lean`** (defs, lean-check clean): `slotUpd_callUpd : slotUpd (kvR γk) x Φ ⊢ callUpd γk
  (kvMi x) (if write then nodeQ x Φ else nodeRQ γt x Φ)` via `lin_kvOpAu1` (write: `lin`'s AU to `kvOpAu1`, the
  next state good by `kvSys_step`: `goodKV_step`, `absSt_step`, `kvOut_good`'s bound, the revision from
  `kvRoom` and `kvOpStep_cases`) and `lin_kvReadAu` (read: each firing fires a copy of `□ lin` and puts `Φ o`
  in an invariant `inv nodeN (Φ o ∨ token γt)`, since `kvReadAu`'s result must be persistent); the results
  back: `nodeQ_out` (write: `Q σ ⊢ ∃ o : VOut, ⌜y = o.1⌝ ∗ Φ o`, from `Call.spec`'s `GoodKV σ → y = outAt i σ`)
  and `nodeRQ_out` (read: with the token, `={E}=∗ ▷ ∃ o, …`; the `▷` needs a credit: take `£ 1` from the
  op closure's pure steps before the call, `wp_auto_lc 1`, and `lc_fupd_elim_later`).
- **Finding: `txnlin.Call.spec` is not usable on a client machine.** Its premises `[∗list] sv ∈ ms, kvRegsAt
  sv` and `clientWriteOnce` are the in-process servers' registrations; a client machine holds only the network
  address facts. The Node needs **`Call` across machines**: `Call.spec` with `isNewClient ∗ clientWriteOnce ∗
  kvRegsAt`s replaced by the lead's `view.kvClientV svc cl api eps V Γ` (branch `etcd-safe-n2/2026-11-25`,
  `dist/ClientViewDist.lean`, unbuilt) and `callUpd Γ.kv i Q` (one update, not one per member: the drafts
  take one AU at `Γ.kv`). Its proof is txnlin's `call`/`callPut`/`callGet`/`callDel`/`callList`/`callTxn`
  re-linked over the drafts `KV_Put_dist`, `KV_Get_dist`, `KV_Delete_dist`, `Txn_Commit_dist` (and `kv.Txn`/
  `If`/`Then`/`Else`, proved). Differences from what the Node needs: (1) the drafts take `Γ.auth = false`
  (the kv workload's deployment has auth off: fine); (2) `kvClientV` needs `clientF cl "KV" ↦□ api`, which
  `NewClients`' post must give (it gives `isNewClient`, `clientTokAt`, `clientNoProxy` today); (3) `membersAtV`
  over `eps`: the Node's `eps` must be the members' addresses with `etcdAddrAtV` each (the start's share);
  (4) `Call.spec`'s post `(GoodKV σ → y = outAt i σ)` and `kvRevFits σ.rev` must survive: the drafts' posts
  give the response messages at `σ`, as `kv.Put.spec` etc. do, so txnlin's `call*` proofs carry over.

## State (2026-11-25, sixth session): `lin` reviewed; `Orch` proved and linked; `Call` across machines specified

- **Review of the `remote.lin` change** (an independent `spec-reviewer`, given the old/new `Defs`, `Pend`, the Go,
  the counter, gryff's kit and `NodeUpd`): **sound, no must-fix**; stronger for the far side only for writes
  (for a read `□ lin ⊣⊢ □ linF`), every producer proves it, no `TopLevel*` text mentions `lin`. Fixed: the
  elimination law **`lin_acc`** (`remote/Defs.lean`: the state with the abort and the commit, telescopes
  simplified; `lin_linF` uses it), docstrings (`linF` "one-shot form", the inner mask `∅`, "a write's `lin`,
  committed at most once", `Pend`'s abort, the five dsverify kits' `opAU` notes naming `linF`). Left (should-fix,
  recorded in the ledger entry): an introduction law in the same plain form (so `pend_fire`/`pend_choice`/
  `NodeUpd` stop unfolding telescopes); `lin_mono` (counter `Shared`) and the two `slotUpd_lin` copies (swiftnet
  `ClientOp`, epaxosnet `ClientProof`) moved into `Defs`.
- **Step 4, `Orch`**: `Spec/.../dist/kvremote/Orch.lean` (`kvOrchPre ns ops`: `∃ γk γ`, the bounds `receiptBound
  ≤ 2^63`, `|ns| < 2^31`, `0 ≤ ops`, `|ns|·ops < 2^60`; `remoteAddr (kvR γk)` per address, `mapCtx (I := VIn)`,
  `pendCtx (kvR γk) linkvtxnS γ`, `pendLib … M.init`, `budUnits a (ops·readTries)` per address; post `r ≠
  "Illegal"`). **It is literally N7-kv's `Orch.specWith kvOrchPre`** (same binders `nodes ns ops tmo`, same pre
  `isPkgInit kvremote ∗ nodes ↦*□ ns ∗ OP ns ops`, same post); `Run.spec`'s `tmo ≤ 0 → r = "Ok"` is dropped to
  match. Proof `Proof/.../kvremote/Orch.lean` (masks `pendN_kvEop`/`lintestN_kvEop`, `kvPendDec`, `kvR_hinj`,
  `isModel_of_step`, `Gen`'s `linkvInOk` to `∃ i : VIn, x = iv i`). Linked: `EtcdGrove.kvremote.wp_Orch`
  (`kvremote/Link.lean`, section `linkedNet` with `[NaInvG GF]` as remote's `Link`; txnlin's `Model`/`Gen` chains
  re-linked from txnlin's proofs in `namespace txnlinL`, not by importing txnlin's `Link`, which needs
  `idIssueExt`).
- **N2's drafts** (`dist/ClientViewDist.lean`): checked out from `70588fe058` (the lead's
  `etcd-safe-n2/2026-11-25`), **only that file, unchanged** (it lean-checks clean on this base). It brings in
  definitions only (no axiom, no proof, no `sorry`): `DistView`, `memberViewOk`, `etcdAddrAtV`, `membersAtV`,
  `kvClientV`, `leaseClientV` and the `.spec` abbrevs `KV_{Put,Get,Delete,Compact}_dist`, `Txn_Commit_dist`,
  `Lease_*_dist`, `Client_Lease*_dist`; imports `S2Interim` and client `Inv*` modules already on the base.
- **`Call` across machines**: `Spec/.../dist/kvremote/CallDist.lean`, `EtcdGrove.etcd_txnlin.Call_dist.spec svc`:
  `Call.spec` with `isNewClient ∗ clientWriteOnce ∗ [∗list] kvRegsAt` and the per-member `[∧list] callUpd`
  replaced by `kvClientV svc cl api eps V Γ` and one `callUpd Γ.kv i Q`, `Γ.auth = false`; same post. Not proved.
- **Gap (2), the `KV` field pointer: closed.** `isNewClient cl eps V` already contains `∃ api, clientF cl "KV" ↦□
  … ∗ kvObjAt api eps`; `kvremote/ClientV.lean`'s `kvClientV_intro : isNewClient ∗ clientNoProxy ∗ membersAtV
  svc eps Γ ⊢ ∃ api, kvClientV svc cl api eps V Γ`. So the Node needs from `NewClients` only `isNewClient` and
  `clientNoProxy` (both in its post today) and from the start `membersAtV svc eps Γ` (gap (3), still open: the
  start's share; the Node's precondition takes it).
- **Build evidence** (fk-lean2, `/shared/tmp/p9-build.sh`): at `ed2630cde4`, `/shared/tmp/p9-targets-lin3.txt`
  (every `remote` leaf, the seven dsverify `TopLevelRobustness`, three `NonVacuityLinked`, the counter,
  `kvremote.Link` with `wp_Orch`, `NodeUpd`, `kvremote.Orch`): built, 8227 jobs, exit 0. `ClientViewDist`,
  `CallDist` spec, `ClientV` (and `kvremote.Link` again) at `fbdc33c19a`: built, exit 0.
  `etc/tier-check.py --check`: ok.

## Handoff

**Base**: still `5a1c41d945` (crash merges in it). P9's commits stay crash-free; the replay onto the no-crash base
waits on the lead's answer (which commit).

**Next, in order:**
1. **Prove `Call_dist.spec`.** txnlin's `call*` proofs cannot be re-linked as they are: they take
   `client.client_{Put,Get,Delete,Txn,List}_st.law` (`ClientCallLaws.lean`), whose statements are over `ms`,
   `kvRegsAt`, `clientWriteOnce` and one update per member, not abstract. Plan: (a) a defs module
   `kvremote/ClientCallDistLaws.lean` with `client_{Put,Get,Delete,List,Txn}_dist.law svc`, each the `_st` law
   with `kvClientV` and one AU at `Γ.kv` (posts as the `_st` laws, error arm without `kvErr`: the drafts claim
   nothing of a remote error; check txnlin's `call*` only need `err ≠ nil` there); (b) their proofs over the
   drafts (hypotheses `KV_*_dist.spec svc`, `Txn_Commit_dist.spec svc`): `cl.Put` is `(*Client).Put` through the
   embedded `KV` (`Client.TypeAssumptions.ptr_Put_unfold.method_unfold`, as `client_Put_rep`,
   `ClientPutGet.lean:346`), then the `*kv` call via `clientF cl "KV" ↦□ api`; the post's revision facts from
   the drafts' `m.hdr.revision`/`kvRevFits`; `List` is `Get` with `WithRange`; `Txn` is `kv.Txn`/`If`/`Then`/
   `Else` (proved) then `Txn_Commit_dist`; (c) copies of txnlin's `callPut`/`callGet`/`callDel`/`callList`/
   `callTxn`/`call`/`Call` proofs (862 lines) over the `_dist` laws, in `kvremote/` (or, better, generalize
   txnlin's proofs over an abstract "client facts" predicate: a spec change to txnlin, ledger first).
2. **The Node** (`ServeClient.spec`): as the fifth session's handoff, with `kvClientV_intro` after `NewClients`
   and `membersAtV svc eps Γ` in its precondition (N7-kv's `Node.specWith NP`: `NP c addr epsL` would carry it).
3. Steps 5-6 (the start, the theorem).
Edit loop: `/shared/tmp/p9-chk.sh FILE -q -a`; builds `/shared/tmp/p9-build.sh TARGETS`.
