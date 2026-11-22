# etcd-dist D3: the crash bridge for `[netExt, fsExt]` (branch `dist-crash-bridge`, 2026-11-22)

D3 of `notes/etcd-dist-plan.md` (branch `etcd-dist`, section 9): the bridge from Perennial's
`goose_dist_mixed_crash_adequacy` to `Robust crashing stable g threads bound`
(`Robustness/Statement.lean`) for deployments in which some machines crash and restart and others
never crash, over the network and Linux file extensions together.

## What is there

- `Net/Statement/NetFsDeploy.lean` (**trusted**, one definition): `NetFsDeploy addrs crashing stable g`,
  the kits' `KitDeploy` of every machine and every machine's files as on disk (`Fs.FsInit`).
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
  (unlike `KitBootWp`): the WP is at `⟨G, L⟩` by a `letI` in the definition. A proof substitutes the
  statement's `lctx` by `L.goose_go_local_context` (`subst`), never destructuring `GooseLocalGS`
  positionally (Perennial branch `local-names` adds a field to it). Its users must `letI` the
  `HeapGS` again after `dsimp` (the example does).
- **The file system in its legacy mode** (`fs_crash_adequacy`'s resources: `osTree` at the start,
  `crashRest` after a crash) at the plain semantics `fs_semantics` (no `Q`/`SQ` premises): kvnet's
  `kvnetExts`. The shared mode needs a Perennial change (below). A premise on crashes or steps
  (`fsSemWith Q`, `fsSemWithS SQ Q`) would need a `kvnetExts` variant with that semantics; none has
  been needed yet.
- **Step and thread bounds as `robust_of_kitBootRB`**: the adequacy theorem at `n + 1` and `n + 2`
  for an execution of `n < bound` steps; `Hstart` gets `receiptBound GF ≤ bound`.
- **Placement**: in the `Net` part (`Net/Statement/`), beside `KitBridge.lean`, because it uses the
  kits' `KitDeploy` and `addrUnset` and the main tree cannot import the part. KvNet can copy it with
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
  roots, as `RobustLinked.lean`'s `echo_kit_robust`); its `#print axioms` is the check.
