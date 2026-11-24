# Tools: the ones the challenge has, and the ones worth building

The challenge comes with the tree's scripts (`etc/`); the ones below are those a kit's proof uses.
Each prints its usage with `--help` (or in its docstring). Use them before writing your own; build a
tool only for what none of them does, keep it generic (no kit names inside), and record it
(`REPORT.md`).

## Given

| tool | when | what it does |
|---|---|---|
| `etc/goose.py` | after a change to the kit's Go, its `Code/**.toml` or a prophecy patch | retranslates (`--project dsv-<kit>`); `--check` exits 1 if anything would change (`SETUP.md`) |
| `etc/proph_patch.py`, `etc/prophcheck` | writing a prophecy patch | applies and checks the patches against the prophecy-only rule (`CHALLENGE.md`) |
| `etc/gen-init.py` | after a translation or kit-file change | writes the packages' `Init.lean` and programs' `PkgTable.lean`; `--check` |
| `etc/dsv/kitgen.py` | kits with `KITGEN`: after a change to its proof parts | writes the deployment's plumbing; `--check`, `--audit KIT`, `--scaffold KIT`, `--list` |
| `etc/lean-check.py` | every edit of a proof | the edit loop through a running Lean server (`SETUP.md`, "Building and checking"); `--goal LINE`, `--fast`, `--split` for the longest proofs |
| `etc/importers.py` | before rebuilding after a statement change | from import lines, no build: `--leaves` the targets a change rebuilds, `--uses NAME` the modules that may need an edit, `--count` how much a change costs |
| `etc/tier-check.py` | before each merge; when placing a new file | the import tiers (`SETUP.md`); `--tier MODULE` a module's tier, importers and cone |
| `etc/tcb-report.py` | before a freeze; at the end | after a build, the axioms and `sorry`s the results rest on, per root; `--roots PATTERN` for some results only, `--per-root` which reach a `sorry` |
| `etc/theorem-loc.py`, `etc/theorem-tcb.py` | at the end, and to read the statement's premises | per top-level theorem, read off the source: the Lean lines it trusts (its premises included) and the Go lines it verifies; `theorem-tcb.py` writes that trusted base out to read |
| `etc/verified-code.py` | for the report | every Go function counted once in its best state (verified, unfinished, assumed, translated, not translated) |
| `etc/spec-churn.py`, `etc/spec-hubs.py` | after a few rounds of statement changes | from git history: statement changes per declaration; fan-out and fan-in; cost = changes × fan-in (`HUBS.md`) |
| `etc/bounds-check.py` | when threads or counters first appear in specs | `TRUST.md`, "Bounds" |

Notes:
- `etc/tcb-report.py` and `etc/verified-code.py` never build: they ask for an up-to-date
  `lake build` and refuse to run on a stale one. They share one Lean run (`--reuse`).
- A generated file is never edited by hand: change the generator's input.
- Scripts that run `lake` take extra Lake options from `LAKE_OPTS`.

## Worth building

| tool | when | what it does |
|---|---|---|
| **a link generator** for the kit | when the kit's proofs reach a few dozen functions | from a list `fn: callee callee …` (with markers for pending proofs), writes the kit's `Link.lean`; `--check`. Hand-written links are fine while they are short |
| **a review bundle** | before Review | one generated file with the interface's statements unfolded, the Go functions they are about and the callers' call sites (`SPEC-FIRST.md`, "Review") |
| **a sorry counter** for the goal path | from the first round of proofs | the `sorry`s the goal reaches (from `tcb-report --roots` or `#print axioms` of the linked results), per round |
