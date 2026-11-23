# etc/dsv: one file per dsverify kit

Each kit ported into the part `Dsverify/` (notes/dsv-paxos.md) has one file here, `<kit>.py`
(`paxos.py`), and edits no shared script: `etc/goose.py` and `etc/gen-init.py` load every `*.py`
here (`goose.dsv_kits()`, in name order; files starting with `_` are skipped). The `Dsverify` lib's
glob in `lakefile.toml` (`Dsverify.+`) already covers every kit's modules, and a kit's trust base is
its own `etc/tcb-collections/dsv-<kit>.txt` (the gates glob that directory).

A kit file is a plain Python module (it may `import os`; it must not import the scripts). Every
name is optional; a kit without `GOOSE` has no goose project.

| name | read by | meaning |
|---|---|---|
| `GOOSE` | goose.py | the kit's project: a dict of `Project`'s fields (`name="dsv-<kit>"`, `local`, `root="Dsverify"`, `lean_roots`, `packages`, `owned`, `std_models`, `module_models`, `expand_comment_tabs`, ...), placed before project `models-net` |
| `PKGS` | gen-init.py | the packages whose `Init.lean` is generated into `Dsverify/Proof/` (those with a `Dsverify/Code/<pkg>.lean`; a `HYP_INITS` package never) |
| `PROGRAMS` | gen-init.py | program package -> its `PkgTable.lean` path, relative to `Dsverify/` |
| `HYP_INITS` | gen-init.py | the packages whose `wp_initialize'` is a hypothesis (the class `InitHyp` of their hand-written `Dsverify/Proof/<pkg>/Init.lean`): external here, and every generated file of the kit whose package's closure holds one imports that `Init` and takes `[<pkg>.InitHyp GF]` as a section variable |
| `HYP_IMPORTS` | gen-init.py | the `HYP_INITS` packages' imports as the closure sees them: `'all'` (default), `'known'` (those in the inventory), `'none'` (none, and their `PkgInfo` imports none: programs' tables stop there) |
| `MAIN` | gen-init.py | main-tree packages the kit's closure adds to `NET_MAIN` (always the main tree's inventory and instances, with those of their imports `Net/` lacks; not raft's `Init` if listed in `RAFT_INIT`) |
| `MAIN_GEN` | gen-init.py | the `MAIN` packages whose `Init.lean` is generated into the part (default: all of `MAIN`) |
| `OWN` | gen-init.py | the part's own translations of packages the main tree translates otherwise: the main tree's `SPECIAL` does not apply to them |
| `special(g)` | gen-init.py | returns `{package: configuration}` for the kit's packages, added to `SPECIAL` (`g`: gen-init.py's globals, `g.newvars_cfg`, `g.FIN_PRE`, ...); a package configured twice is an error |

Each kit is generated in a context of its own (`gen-init.py`'s `dsv_kit_raw`): one kit's
`HYP_INITS`, `MAIN` and `OWN` never change another's files. Two kits that generate the same file
(`Dsverify/Proof/bufio/Init.lean`) must generate it identically, or gen-init stops.

Tabs: Lean rejects a tab in a doc comment goose copies from Go. Keep the fork's Go as it is and set
`expand_comment_tabs=True` in `GOOSE`: goose.py replaces the tabs in the translation's comments by
four spaces (a tab elsewhere is an error), in `--check` too.
