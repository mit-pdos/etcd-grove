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

## Handoff

Head: see `git log` of `etcd-safe-p9` (pushed). Next, in order:
1. `enc`'s remaining proofs: `Enc.U64` (the 8-append loop: invariant `ownEnc e (bs ++ (u64Le x).take i)`,
   `append` by `wp_slice_append`; the byte lemma `u64Le_getElem` is in `Net/Proof/.../remote/counter/Codec.lean`
   — copy it, a proof imports no proof), `Enc.Bool`, `Enc.Str` (`U64` then `append(e.B, []byte(s)...)`:
   `wp_string_to_bytes`, `wp_slice_append`), `NewDec`, `Dec.U64` (the or-loop: `leToU64_take_succ` from the same
   counter file; then `u64Le (leToU64 (bs.take 8)) = bs.take 8`, `leToU64_le`), `Dec.Bool`, `Dec.Str`; then a
   `Link.lean` for `enc` (hand-written, as `remote`'s).
2. kvremote's `encCmp`/`decCmp`/… and `EncInput`/`DecInput`/`EncOutput`/`DecOutput`, pure `encInput`/`encOutput`
   with injectivity; then `codecOk`, `PendDec` for kv, and §11.3's steps 1, 3-6.
Edit loop: `/shared/tmp/p9-chk.sh FILE -q -a` (copies one file to fk-lean2's worktree; for new imports, copy them
first, e.g. `tar … | ssh … tar x` as done for `enc`), builds `/shared/tmp/p9-build.sh TARGETS` (pushes HEAD).
