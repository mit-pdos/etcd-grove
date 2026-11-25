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

## Handoff

Done: §11.3 step 1 (the store, `kvPendDec`, `kvR_hinj`) and step 2 (`codecOk (kvR γk) (Codec())`, linked).
Next, in order (§11.3), each spec first:
1. **Step 3, the client machine** (`dist/kvremote/Node.lean`): `opMaybe (kvR γk) a tok op` for `Node`'s
   `op` (`func(sys, in) any { return txnlin.Call(sys.(*clientv3.Client), in) }`), from `txnlin.Call.spec`
   (`EtcdGrove.etcd_txnlin.wp_Call`, linked) at `x := i.1`, `i := kvMi x` (`kvMi_dec`), `GenIn` from `x.2`,
   `Q` the continuation: a write's `slotUpd = lin` (`slotUpd_write`) must give `[∧list] sv ∈ ms, callUpd
   sv.γr.kv (kvMi x) Q` with every `sv.γr.kv = γk` (D7: `tok cli` should carry that): `lin` -> `kvOpAu1 γk
   (opIn i) Q` by opening `lin`'s fupd (mask `⊤ \ kvEop`, `kvEop_mask`), giving `etcdKV γk σ` from `kvSys`,
   and at the commit rebuilding `kvSys` of `kvOpStep (opIn i) σ` (`GoodKV`: `goodKV_step` with
   `inKeys_keysIn`; `absSt`: `absSt_step`; `kvGood`: `kvOut_good`'s `StoreLe` and `kvRoom σ` for the
   revision) and `Q σ := Φ (outOf ..)`-ish matching `lin`'s `Φ (TSo.step ..).2` (`kvOut_good`: `.1 =
   outOf`, and `Call.spec`'s `y = outAt i σ` under `GoodKV σ`). A read's `□ lin` -> `kvReadAu γk Q` likewise
   (`reads_stay`). Model: txnlin's `Inv.lean` (`linkvInv_kvOpAu1`-style lemmas at lines ~536, ~779).
   Then `Node`'s WP (`ServeClient.spec`, never returns). `tok` per §11.3 step 3.
2. Step 4 (`Orch`: `Run.spec` at `kvR γk`, `linkvtxnS`, `kvPendDec`, `kvR_hinj`, `kvR_timeless`, txnlin's
   `Model`/`Gen` (`genSpec` post `linkvInOk` -> `∃ i : VIn, x = boxIn i.1`), masks `pendN ⊆ ⊤ \ kvEop`,
   `lintestN ⊆ ⊤ \ (kvEop ∪ pendN)`), then steps 5-6.
Edit loop: `/shared/tmp/p9-chk.sh FILE -q -a`; builds `/shared/tmp/p9-build.sh TARGETS` (pushes HEAD to fk-lean2).
