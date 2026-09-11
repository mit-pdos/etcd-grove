# Decisions

Why the development is the way it is. Newest last.

Record a decision when you pick a specification, an invariant, an abstraction
boundary, or a trust boundary, **and there was a real alternative** — the point
is to stop the next agent from silently re-deciding it the other way. Say what
was rejected and the cost that killed it; that is the part that saves time. Skip
routine choices with an obvious answer.

To revisit one, add a new entry and put a "Superseded by …" line on the old one
rather than editing it.

---

## Keep upstream Go module and Rocq logical paths

**2026-09-11 · accepted**

`etcd-grove` is a fork of `mit-pdos/perennial`. When setting the fork up, the
obvious sweep is to rename every `mit-pdos/perennial` reference to
`upamanyus/etcd-grove`. Two of those references are not URLs but identifiers
the build depends on:

- the Go module path `github.com/mit-pdos/perennial` in `go.mod`, which Goose
  embeds in its output, so it appears in ~71 files and names three generated
  directory trees (`new/code/github_com/mit_pdos/perennial/...`, likewise under
  `new/generatedproof/`, and `goose/testdata/**/*.gold.v`);
- the Rocq logical paths `Perennial` and `New` in `_RocqProject` and
  `perennial.opam`, which every `From Perennial Require` / `From New Require`
  in the repo depends on.

**Decision:** leave both alone. Rebrand only things that identify *the
repository* — README and its CI badge, `perennial.opam` metadata,
`CONTRIBUTING.md`, `docs/`, the flake description, the GitHub workflows.

**Rejected — rename the Go module to `github.com/upamanyus/etcd-grove`.**
Cost/benefit. The benefit is zero for the etcd work: the etcd Go code lives in
separate repos and translates to `go_etcd_io/...` paths, so this module path
only ever names Goose's own test fixtures. The cost is real and recurring —
every future `git merge upstream/master` would conflict across all of
`goose/*.go` and every `.gold.v`, since Goose is actively developed upstream.

**Rejected — rename the Rocq logical path `Perennial` → `EtcdGrove`.** Rewrites
the import line of essentially every `.v` file, guarantees a conflict on every
upstream merge, buys nothing. The framework genuinely is Perennial.

**Rejected — rename `perennial.opam` to `etcd-grove.opam`.** `flake.nix`
derives its package name from that filename via opam-nix, and
`etc/install.sh`, the Makefile, CI and the docs all name it. The package still
installs logpaths `Perennial` and `New`, so the name is not wrong.

**Consequences:** upstream merges stay mechanical — `git fetch upstream && git
merge upstream/master` touches only files we actually edited. Anyone reading
`go.mod` or an import line sees `mit-pdos/perennial` and may think the fork is
misconfigured; `README.md` says why, and so does this entry. If the fork ever
diverges enough that upstream merges stop happening, this is cheap to revisit:
a scripted `sed`, three `git mv`s, and a Goose regeneration.

---

## Keep the notes plaintext; no hooks or scripts

**2026-09-11 · accepted**

The notes system was first built with `topics/`, `decisions/` and `journal/`
subdirectories, a README and template in each, two Python hook scripts
(`etc/agent-notes/session-start.py` injecting `STATUS.md` into each session,
`etc/agent-notes/stop-check.py` nudging when `.v` files changed but `notes/`
did not), a `.claude/settings.json` wiring them up, and a Claude-Code-specific
`/notes` skill.

**Decision:** delete all of it. Seven flat markdown files in `notes/`, and
plain instructions in `AGENTS.md`. The general principle, from Upamanyu: **only
add structure where there is a demonstrated benefit.**

**Why the hooks lost.** Two independent reasons. They are Claude-Code-specific,
and this project will see other coding agents, so behaviour encoded in
`.claude/settings.json` silently does not happen under a different tool —
whereas a sentence in `AGENTS.md` or `notes/README.md` is read by all of them.
And they were speculative: nobody had yet skipped writing notes, so a `Stop`
hook was solving a problem that had not been observed, at the cost of two
scripts to maintain and a blocking interaction to get wrong.

Same reasoning killed the subdirectory scaffolding: `topics/README.md`,
`decisions/README.md` and `journal/README.md` were index and template files
with no content, and indexes that have to be hand-maintained go stale.

**Consequences:** nothing guarantees the notes get updated — it rests on
`AGENTS.md` and habit. That is the accepted trade. Revisit only with evidence:
if notes are demonstrably being skipped, automate *that one step*. Likewise
split a file into a directory when the file is actually unwieldy, not in
anticipation.
