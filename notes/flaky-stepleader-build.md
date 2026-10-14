# The flaky build of `stepLeader.lean` (diagnosis, 2026-10-14)

**Status: diagnosed, with high confidence. The fix is NOT applied**, neither to
`Proof/go_etcd_io/raft/v3/stepLeader.lean` nor to Perennial. It is proposed below.

Tested on `stepLeader.lean` at two versions. The first is `51e39de75`, before A3. The
second is `b2ee06944`, after A3's `ownRaftPhysC` rewrite (`e3639931c`). Both run against
Perennial `008979bd0` and Lean v4.34.1. Line numbers below are those of `b2ee06944`
unless marked "old".

## Symptom

Under a parallel full build, `stepLeader.lean` sometimes fails and then passes when
rebuilt alone. The first error is one of:

- `ipureintro: iprop(… "Hphys" ∷ ownRaftPhys… …) is not pure`, right after an
  `iframe` (old 711, 820, 436; now 796, 698/712);
- `unsolved goals` (now 1387).

These come with follow-on errors later in the same theorem: `unknown free variable
_fvar.…` (old 825/916, now 801/892) and `iapply: cannot apply Φ` (now 895). The
"unknown free variable" errors that were reported are these follow-ons, not the cause.
The earlier reports in `STATUS.md` fit the same mechanism. Among them: "not pure" at 239
(old), and `InvSTMRun.lean`'s "an `iframe` not framing `STMSt.empty.reads` against `∅`".

## Cause: a process-global reentrancy flag in Perennial's `iframe ∗`

`Perennial/Golang/Theory/IrisTactics.lean` (Perennial `008979bd0`, lines 311 and
380-393) wraps iris-lean's `iframe ∗` (which plain `iframe` expands to) with a prepass,
`iframePrep`. The prepass does three things:

- it replaces a goal conjunct by a hypothesis equal to it by computation;
- it makes a persistent hypothesis that is needed twice intuitionistic;
- it picks existential witnesses.

A reentrancy flag keeps the inner call from running the prepass again. That flag is a
process-global `IO.Ref`:

```lean
meta initialize inIframe : IO.Ref Bool ← IO.mkRef false
...
  | `(tactic| iframe $pats:selPat*) => do
    if ← inIframe.get then throwUnsupportedSyntax     -- falls through to iris-lean's iframe
    ...
    inIframe.set true
    try evalTactic (← `(tactic| iframe $pats:selPat*))
    finally inIframe.set false
```

Lean elaborates the bodies of a file's theorems in parallel: `Elab.async` is on by
default on the command line, and `stepLeader.lean` runs at about 580% CPU. Suppose
theorem A is inside its `iframe ∗` with the flag set when theorem B, on another thread,
starts an `iframe ∗`. B sees the flag and throws `unsupportedSyntax`, so B runs iris-lean's
bare `iframe ∗` without the prepass. Where the prepass was needed, the goal is left
different. In `stepLeader.lean` that is a conjunct `ownRaftPhys… (readRespondAll id s3
[])` against `Hphys : ownRaftPhys… s3`, or the record `{ sendMsgs s ms with prvals := pvs
}` in two different but defeq forms. The next tactic then fails.

The window is wide when threads are descheduled, as on a loaded machine. That is why the
failure shows up under a full parallel build and rarely alone. `lake build` runs every
module in its own process, so other modules cannot set the flag. Only theorems of the
same file race each other, and other processes add to the problem only through CPU load.

Neither of the other suspects explains it:

- **Memory:** Lean has no GC, and an out-of-memory condition would crash the process,
  not give these errors.
- **Heartbeats:** a heartbeat or `maxRecDepth` limit gives a "deterministic timeout"
  error, which never occurred.

## Evidence

The instrumentation is a module `Proof/go_etcd_io/raft/v3/FlakyInstr.lean`, not
committed; its text is at the end of this note. Each experiment compiles a copy of
`stepLeader.lean` whose line 46, a comment, is replaced by `public import
Proof.go_etcd_io.raft.v3.FlakyInstr`, so every line number is unchanged. The module adds
an `elab_rules` for `iframe ∗`, which Lean tries before Perennial's. Its behaviour depends
on `FLAKY_MODE`:

- `detect`: prints `FLAKY-RACE line N` to stderr when a top-level `iframe ∗` starts while
  `inIframe` is set (so Perennial's rule will skip the prepass), then hands over to
  Perennial's rule.
- `skip`: runs iris-lean's elaborator directly, with no prepass, at the lines in
  `FLAKY_SKIP_LINES` (or `all`). This reproduces the race on demand.
- `fix`: the prepass, then iris-lean's elaborator, with no global flag. This is the
  proposed fix.

Runs used `lake env lean <file>`, `N` rounds of `P` copies at once, on 24 cores shared
with other sessions (load average 20-33 during the 6-copy runs); the script is at the end
of this note. One copy alone takes 2 min wall, about 700 s CPU and 1.9 GB.

| version | mode | runs (P x N) | failed | notes |
|---|---|---|---|---|
| old `51e39de75` | plain (unmodified file) | 4 x 3 | 1 (8%) | first error 820 `ipureintro … not pure` |
| old | detect | 6 x 2 | 3 (25%) | **the 3 failing runs are exactly those with `FLAKY-RACE line 819`**; 6 other runs raced at harmless lines (374, 376, 910, 1092, 1098, 1159, 1161, 1385) and passed |
| old | skip 819, alone | 1 | 1 | the same 4 errors as the flaky failure (820, 825, 916, 919), deterministically |
| old | fix | 6 x 3 | **0** | |
| new `b2ee06944` | detect | 6 x 2 | 3 (25%) | failing runs raced at 795, at 709-718 and at 1390: each the vulnerable site of its first error; 5 passing runs raced at harmless lines |
| new | skip 795, alone | 1 | 1 | 796, 801, 892, 895: the old 820/825/916/919 |
| new | skip all 64 top-level `iframe ∗`, alone | 1 | 1 | errors at 698, 712, 796 (+ 801, 892, 895) and 1387: **the complete list of the file's race-sensitive sites** |
| new | fix | 6 x 3 | **0** | load average up to 88 during these runs |

The follow-on "unknown free variable" is not caused by the `iframe` at 795 itself. With
795 made robust (the stopgap below) and only 695-718 skipped, 801 still fails with it,
after the 698/712 errors. With only 795 skipped it passes. So it is a consequence of an
earlier error in the same theorem. Its exact mechanism (error recovery, a cached `word`
proof) was not pinned down.

## Proposed fix (in Perennial; not applied)

Make the guard local to the elaboration rather than to the process: an option set with
`withOptions` lives in the `Core.Context` of the task that runs the tactic. Against
`Perennial/Golang/Theory/IrisTactics.lean` at `008979bd0`:

```diff
-meta initialize inIframe : IO.Ref Bool ← IO.mkRef false
+meta register_option goose.iframe.inner : Bool := {
+  defValue := false
+  descr := "(internal) set while Perennial's `iframe ∗` runs iris-lean's, so that the \
+    inner call is iris-lean's; an option (per elaboration task), not a global `IO.Ref`: \
+    the bodies of a file's declarations are elaborated in parallel"
+}
 ...
   | `(tactic| iframe $pats:selPat*) => do
-    if ← inIframe.get then throwUnsupportedSyntax
+    if goose.iframe.inner.get (← getOptions) then throwUnsupportedSyntax
     ...
     if (← getGoals).length < n0 then return
-    inIframe.set true
-    try evalTactic (← `(tactic| iframe $pats:selPat*))
-    finally inIframe.set false
+    withOptions (goose.iframe.inner.set · true) <|
+      evalTactic (← `(tactic| iframe $pats:selPat*))
```

The patch itself was not compiled, because changing Perennial's `IrisTactics` rebuilds
everything. The `fix` mode tested its logic: the guard is per task and the inner call is
iris-lean's. It gave no failure in 18 runs per version under load (36 in all), where the unfixed file failed in 25% of runs at the lighter load.

The same pattern has other instances in Perennial (all `IO.Ref`s set by `initialize`).
None of them caused these failures, but they are worth fixing in the same change:

- **`ProofMode.lean`, `autoAngelicIf`:** a global flag that `wp_auto_angelic` sets. A
  `wp_auto` running at the same time in another declaration of the file would take
  angelic `if` steps.
- **`ProofMode.lean`, the `wp_auto` state** (`fvCache`, `closedCache`, `hoistCandidates`,
  `binderSteps`): it is cleared and read by every `wp_auto` (`Auto.lean`, line 565ff), so
  concurrent `wp_auto`s clear or steal each other's caches and hoisting candidates. As far
  as I can see this makes the proof terms and the timing nondeterministic but not wrong:
  the candidates are replaced by pointer, and caches keyed on expressions only hit on
  equal free variables.
- **`needsCache`, `laterCache`, `Word/Cache.lean`:** the cached values are context-checked
  or closed booleans. `pureWpCache` is already per thread.

A per-task state (an option, a `MonadReader` context, or an environment-extension-free
`StateRefT` threaded through `wp_auto`) would remove the cross-declaration interference
everywhere.

## Stopgaps without changing Perennial (not applied)

1. **Per site in `stepLeader.lean`:** make each sensitive `iframe` need no prepass. At
   795 (new; old 819) it is enough to unfold `readRespondAll` of `[]`:

   ```diff
   @@ -791,7 +791,7 @@ private theorem wp_stepLeader_hbresp
      · iexists W64 0, zero_val Loc
   -    rw [show (sint.Z (W64 0)).toNat = 0 from rfl, List.take_zero]
   +    rw [show (sint.Z (W64 0)).toNat = 0 from rfl, List.take_zero, readRespondAll, List.foldl_nil]
        iframe
   ```

   The patched file builds with `lake build` at `b2ee06944`. With all 64 `iframe ∗`
   skipped, the 796 error is gone, but 698, 712 and 1387 remain: the
   `{ sendMsgs s ms with prvals := pvs }` frames and an `iframe` around 1390. Each needs a
   similar `rw`/`show`. This is whack-a-mole, and it does nothing for other files
   (`InvSTMRun.lean` was hit the same way).
2. **Per file or per repository:** an `elab_rules` override, the `fix` mode of
   `FlakyInstr.lean` without the other modes, in a small module imported by the affected
   files. It takes precedence over Perennial's rule (later rules are tried first) and
   never reads `inIframe`. This is complete for the files that import it, and
   18 + 18 runs under load passed with it.
3. **`set_option Elab.async false`** in the file removes the race, but serializes about
   700 s of CPU work (the file would take about 10 minutes instead of 2). Not recommended.

Recommendation: land the Perennial patch and bump the pin. If that has to wait, use
stopgap 2, imported by `stepLeader.lean` and by any file that shows the symptom.

## Reproduction

`/tmp/flaky/run.sh TAG N P [lean args]` runs `N` rounds of `P` concurrent compiles of
`$FILE`, and passes the environment (`FLAKY_MODE`, `FLAKY_SKIP_LINES`) through:

```bash
#!/bin/bash
TAG=$1; N=$2; PAR=$3; shift 3
cd <worktree>
F=${FILE:-Proof/go_etcd_io/raft/v3/stepLeader.lean}
mkdir -p /tmp/flaky/$TAG
for r in $(seq 1 $N); do
  for p in $(seq 1 $PAR); do
    ( s=$(date +%s); lake env lean "$@" "$F" > /tmp/flaky/$TAG/r$r-p$p.log 2>&1; rc=$?
      e=$(grep -c 'error:' /tmp/flaky/$TAG/r$r-p$p.log)
      echo "r$r p$p rc=$rc errors=$e secs=$(( $(date +%s)-s ))" >> /tmp/flaky/$TAG/summary ) &
  done
  wait
done
```

Deterministic reproduction, with no load needed:
`FLAKY_MODE=skip FLAKY_SKIP_LINES=795 lake env lean <copy importing FlakyInstr>`.

`Proof/go_etcd_io/raft/v3/FlakyInstr.lean` (build it first with `lake build
Proof.go_etcd_io.raft.v3.FlakyInstr`):

```lean
module

public import Perennial.Golang.Theory.IrisTactics

@[expose] public section

open Lean Elab Tactic in
meta def flakyIrisIframe (stx : Syntax) : TacticM Unit := do
  let es := tacticElabAttribute.getEntries (← getEnv) stx.getKind
  let some e := es.find? (·.declName == `Iris.ProofMode._aux_Iris_ProofMode_Tactics_Frame___elabRules_Iris_ProofMode_tacticIframe____1)
    | throwError "flaky: iris-lean's iframe elaborator not found"
  e.value stx

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| iframe $pats:selPat*) => do
    if (← getOptions).getBool `flaky.nested false then throwUnsupportedSyntax
    unless pats.size == 1 && (pats[0]!.raw.getArg 0).isToken "∗" do
      throwUnsupportedSyntax
    let stx ← getRef
    let fm ← getFileMap
    let line := match stx.getPos? with
      | some p => (fm.toPosition p).line
      | none => 0
    let mode := (← IO.getEnv "FLAKY_MODE").getD "detect"
    if mode == "fix" then
      let saved ← saveState
      let n0 := (← getGoals).length
      try Perennial.IrisTactics.iframePrep n0 catch _ => saved.restore
      if (← getGoals).length < n0 then return
      flakyIrisIframe stx
    else if mode == "skip" then
      let lines := ((← IO.getEnv "FLAKY_SKIP_LINES").getD "").splitOn ","
      if lines.contains (toString line) || lines.contains "all" then
        IO.eprintln s!"FLAKY-SKIP line {line}"
        flakyIrisIframe stx
      else
        withOptions (fun o => o.setBool `flaky.nested true) (evalTactic stx)
    else
      if ← Perennial.IrisTactics.inIframe.get then
        IO.eprintln s!"FLAKY-RACE line {line} (inIframe already set: the prepass is skipped)"
      withOptions (fun o => o.setBool `flaky.nested true) (evalTactic stx)
```

(The `fix` mode honours `goose.iframe.prepass` only implicitly: it always runs the
prepass, which is the default.)
