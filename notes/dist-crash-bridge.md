# etcd-dist D3: the crash bridge for `[netExt, fsExt]` (branch `dist-crash-bridge`, 2026-11-22)

D3 of `notes/etcd-dist-plan.md` (branch `etcd-dist`, section 9): the bridge from Perennial's
`goose_dist_mixed_crash_adequacy` to `Robust crashing stable g threads bound`
(`Robustness/Statement.lean`) for deployments in which some machines crash and restart and others
never crash, over the network and Linux file extensions together.

## What is there

- `Net/Statement/NetFsDeploy.lean` (**trusted**, one definition): `NetFsDeploy addrs crashing stable g`,
  `DistDeploy` of every machine and every machine's files as on disk (`Fs.FsInit`).
- `Net/Statement/NetFsBridge.lean` (untrusted): `robust_of_netFsBoot`, and the per-machine obligations
  `StableBootWp`, `CrashBootWp`, the first-generation resources `fsStartRes`, and the lemmas turning
  them into Perennial's `nodeWp`/`nodeStart`.
- `Net/Proof/github_com/mit_pdos/etcd_grove/examples/net/echo/NetFsCrashLinked.lean`: the minimal
  instance, `echo_netfs_mixed_robust` (echo's server on a crashing machine, its client on a stable one,
  both over `kvnetExts`); `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`.

Nothing in `GooseLang/Ext/NetFs/` (#22's) changed: the bridge uses its `kvnetExts`, `kvnetGF` and
the start/crash projections (`kvnet_net_globalStart`, `kvnet_fs_localStart`, `kvnet_fs_crashStart`)
as they are.

## The statement

```lean
theorem robust_of_netFsBoot [lctx : GoLocalContext] (addrs : List GoString)
    (crashing stable : List (Expr × state)) (g : GlobalState) (threads bound : Nat)
    (Hstart : ∀ [GooseGlobalGS .hasLC GF], receiptBound GF ≤ bound →
      ⊢ ([∗list] a ∈ addrs, addrUnset a) ={⊤}=∗
        ∃ (Pc : Nat → GooseLocalGS GF → IProp GF) (Ps : Nat → IProp GF),
          ⌜∀ (i : Nat) (m : Expr × state), crashing[i]? = some m → CrashBootWp m.1 (Pc i)⌝ ∗
          ⌜∀ (j : Nat) (m : Expr × state), stable[j]? = some m → StableBootWp m.1 m.2 (Ps j)⌝ ∗
          ([∗list] i ↦ m ∈ crashing, ∀ L : GooseLocalGS GF,
            ⌜L.goose_go_local_context = lctx⌝ -∗ fsStartRes L (extLocal Fs.fsExt m.2.world) -∗
            ownGoState (hG := L.goose_go_stateGS) ∅ ={⊤}=∗ Pc i L) ∗
          [∗list] j ↦ _m ∈ stable, Ps j) :
    NetFsDeploy addrs crashing stable g → Robust crashing stable g threads bound
```

(at the extensions `kvnetExts`, any `GF` with `GooseGpreS GF`). `CrashBootWp e P`: for every local
ghost state `L` of the statement's Go context, `P L ∗ threadTok ={⊤}=∗ WP e {v = #()} ∗ (∀ L' V',
crashed L -∗ osInv L' -∗ crashRest True L L' [] false V' -∗ ownGoState L' ∅ ={⊤}=∗ P L')`.
`StableBootWp e σ P`: `P ∗ fsStartRes L σ ∗ ownGoState ∅ ∗ threadTok ={⊤}=∗ WP e {v = #()}`.

## Design choices

- **The precondition is chosen inside the start update.** Perennial's `P` (the crashing nodes'
  generation precondition) is a parameter fixed before `Hstart` runs, so it cannot name the ghost
  names `Hstart` allocates. The bridge's `P i L` is `crashPre`: `∃ Q, ⌜CrashBootWp e_i Q⌝ ∗ Q L`, with
  `Q` (the client's `Pc i`) picked in `Hstart`; every generation's proof unpacks `Q` and packs the
  next `Q L'` with the same `Q`.
- **The obligations quantify over the local ghost state `L`, not over a `HeapGS` with an equation**
  (unlike `DistBootWp`): the WP is at `⟨G, L⟩` by a `letI` in the definition. A proof substitutes the
  statement's `lctx` by `L.goose_go_local_context` (`subst`), never destructuring `GooseLocalGS`
  positionally (Perennial branch `local-names` adds a field to it). Its users must `letI` the
  `HeapGS` again after `dsimp` (the example does).
- **The file system in its legacy mode** (`fs_crash_adequacy`'s resources: `osTree` at the start,
  `crashRest` after a crash) at the plain semantics `fs_semantics` (no `Q`/`SQ` premises): kvnet's
  `kvnetExts`. The shared mode needs a Perennial change (below). A premise on crashes or steps
  (`fsSemWith Q`, `fsSemWithS SQ Q`) would need a `kvnetExts` variant with that semantics; none has
  been needed yet.
- **Step and thread bounds as `robust_of_distBootRB`**: the adequacy theorem at `n + 1` and `n + 2`
  for an execution of `n < bound` steps; `Hstart` gets `receiptBound GF ≤ bound`.
- **Placement**: in the `Net` part (`Net/Statement/`), beside `DistBridge.lean`, because it uses
  `DistDeploy` and `addrUnset` and the main tree cannot import the part. KvNet can copy it with
  `etc/copy-part.py` if kvnet's statement uses it.

## The Perennial gap (shared mode)

The Linux file extension's shared mode (`fsSQ_crash_adequacyShared`, `GooseLang/Ext/Fs/AdequacyShared.lean`
on branch `wal-safe`, not on `lean`) switches each generation to the shared mode before its WP, which
needs one update of the extension's local interpretation at the generation's start. For one machine,
`wal-safe` copies `goose_crash_adequacy` into the repository (`CrashAdequacyAcc.lean`). For the
distributed theorem the same is missing: `goose_dist_mixed_crash_adequacy`'s `Hwp` (and `nodeStart`,
`nodeWpBody`) get `P i L` and `threadTok` only. Recorded in `notes/perennial-changes.md` ("Extension
state access at generation start, distributed"), with the design; D3 stops there (no local copy of the
distributed adequacy proof). D4 (shared-mode generations for etcd's bundle) needs it.

## Open

- The shared-mode bridge (`robust_of_netFsBootShared`): after the Perennial change, the same theorem
  with `CrashBootWp`'s WP given `osShared R V` and its frame returning `osTree R V''` (as
  `fsSQ_crash_adequacyShared`).
- The example keeps nothing on disk; an instance whose crashing machine uses its files across a crash
  (e.g. crashlog's log behind a network server) would exercise `crashRest`. Not needed for D3.
- `etc/tcb-report.py` does not see `echo_netfs_mixed_robust` as a root (`*Linked.lean` files are not
  roots, as `RobustLinked.lean`'s `echo_dist_robust`); its `#print axioms` is the check.

## Independent review of `NetFsDeploy` (2026-11-22)

Verdict: sound, not vacuous, the right strength; documentation fixes (report:
`/shared/tmp/coord-03/review-netfsdeploy.md`).
- F1 (fixed in the docstring): the start conditions are stated by `NetFsDeploy`, not by `Robust`; the
  extensions' `initLocal`/`initGlobal` are `True` at this pin. **Open:** `Robustness/Statement.lean`'s
  header (lines 26-30) claims `Robust`'s premises already give "no listener, no connection, files as on
  disk", which is false at this pin; to be corrected with the owner of `Robustness/` (#22). The proper fix is
  kvnet-robust-goal.md items 3-4 (the extensions' `initLocal`), after which `NetFsDeploy` is the address
  facts only.
- F2 (fixed in the docstring): each machine's roots are its own.
- F3 (reworded): the echo example proves the implication only. Satisfiability: `NetLocal.init ⟨∅⟩`,
  `NetGlobal.init ⟨∅⟩` (`Net/Impl.lean`), `fsInit0` (an empty root), `addrOk srvAddr` by `decide`; a Lean
  witness is not written.
- F4 (note): `DistDeploy`'s "no listener" conjunct is unused by every bridge; drop it with F1's plan.
- F5 (note): `FsInit` asks a stable machine's files to be durable, which no step reads.

## D4c: the bridge over any bundle (2026-11-24, branch `etcd-safe-d4c/2026-11-24`)

`robust_of_netFsBoot{,_addrs}` is hard-wired to `kvnetExts`. Its generalization, proved, untrusted (no new
trusted definition: it uses `Robust`, `DistBootWpSL`, Perennial's `goose_dist_mixed_crash_adequacy`):

- `Net/Statement/NetFsBridgeG.lean`, two layers.
  1. `robust_of_crashBootIL`: any `[GooseExts] [GooseSemantics] [GooseInterp] [GooseCrashInterp]` with
     `HasExt netExt`. Crashing machines: `CrashBootWpE lo bound e P` (the raw `extsCrashStart L L'` after a
     crash), first generation from the raw `extsLocalStart`; stable machines: `DistBootWpSL`. The
     initial-state conditions come from `Robust`'s premises through a hypothesis `HI`; bounds as
     `robust_of_distBootIL` (`max (n + 1) lo` receipts, a receipt floor `lo`, the thread bound one more,
     given to every obligation). `hasExt_localStart` (the local analog of `hasExt_globalStart`).
  2. `robust_of_netFsBootG Q X HC`: the bundle also has `fsExt` at any semantics with `FsSemOk`; `HC`
     splits the crash resources into `Fs.osCrashStart Q` and the other extensions' `X L L'`.
     `CrashBootWpG Q X` gets `osInv L'`, `crashRest Q … [] false V'` and `X L L'`; the first generation
     `fsStartResG` (from `FsInit`, which `HI` gives for each crashing machine: `fsSemWithS` has no
     `initLocal` until D4a). `StableBootWpG` → `DistBootWpSL` given `FsInit`.
- `Net/Statement/NetFsBridgeGKvnet.lean`: `robust_of_netFsBoot_addrs_ofG`, `robust_of_netFsBoot_addrs`'s
  exact statement re-derived from layer 2 (`Q := True`, `X := True`, `kvnetInitCompat`).
- `Proof/.../etcdstart/NetExtsCrash.lean`: `etcdNetExtsCrashInterp C` (`C` any `ExtCrashInterp` of the
  issue record at `idIssue_semantics`/`idIssue_interp`; the file extension's `fs_crash_interpS etcdSQ True`;
  the net extension's), `etcdNet_crashStart_split` (`X := etcdIdCrashRest C`, `C.crashStart` of the
  issue record's local ghost states), `etcdNetExts_crashInitP` (from `FsInit`) and the corollary
  `robust_of_etcdNetFsBoot C`. `idIssue_crash_interp_keep` (`crashStart L L' := ⌜L' = L⌝`) shows today's
  semantics already has one; D4b's incarnation-keyed record supplies the one the proofs use, of the same
  shape (any `@ExtCrashInterp idIssueExt S idIssue_interp'`; if D4b changes the semantics or interp
  instance, `etcdNetExtsCrashInterp`'s type follows them).

Not done: the shared-mode generation start (the Perennial gap above) is still missing; a crashing
member's proof (D6) is the first user.
