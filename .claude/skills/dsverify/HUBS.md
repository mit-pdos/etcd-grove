# Hubs: map them before planning per package

## What a hub is

A **hub** is a statement with high fan-out: it mentions the facts of many subsystems. In a challenge
the hubs are predictable:

- **the deployment's start** (the start obligation of the bridge, `NET.md`; a kit's `kit_start`
  lemma): from the addresses unset, it allocates every subsystem's ghost state and every address's
  protocol, and hands each machine its share;
- **each machine's share and its `main`'s spec** (`Mains.lean`'s `wp_main`, the kit's
  `Orch`/`Client`/`Server` specs): each names the start resources of every subsystem the machine
  runs;
- **the server's constructor** and **the client's constructor** (`newClient`, a one-shot resource):
  they take every subsystem's start resources and return every subsystem's running state;
- **the ghost-name records**: the bundle of ghost names threaded everywhere;
- **the state-machine aggregators**: the apply loop's invariant, the store's abstract state that the
  client spec's atomic updates are over;
- **the core protocol invariant** (the consensus log's, the quorum's).

The top-level statement itself is given and fixed: it names no subsystem, so it is not a hub you
manage. What you manage is everything between it and the code.

**Churn follows fan-out, not fan-in**: a statement used by many is stable if it mentions few things; a
statement that mentions many changes whenever any of them does: each time a subsystem adds or changes
one fact, every hub naming that fact changes with it, along with every caller's glue.

## Finding them

- **At the start** (before the first interface): from the code and the statement, list the
  functions that construct many subsystems (each machine's `main`, the constructors) and the
  statements that will carry them.
- **Once there is history**: `etc/spec-churn.py` and `etc/spec-hubs.py` (`TOOLS.md`) compute, per
  declaration, its fan-out, fan-in and number of statement changes. Sort by changes × fan-in (cost)
  and by fan-out (aggregators). Re-run them every few rounds.

## The slot convention: one sealed slot per subsystem

Each subsystem `<sub>` exposes a small fixed set of **sealed** predicates (`@[no_expose]`, in the
subsystem's API module, used only through laws):

| slot | is |
|---|---|
| `<sub>.Names` | the subsystem's ghost names, one record |
| `<sub>.bootCfg …` | its pure boot premise; its arguments are what it reads (the configuration, the peers' addresses); a premise of the hub only when needed |
| `<sub>.bootRes cfg` | the resources it needs at start (an address's listen right, call units, tokens) |
| `<sub>.bootOk` | what its start gives back |
| `<sub>.runInv` | its part of the running system's invariant |

A hub names the subsystem **only** through its slots: a server's constructor takes
`log.bootRes cfg ∗ transport.bootRes …` and returns `log.runInv … ∗ transport.runInv …`, never the
facts inside. A change inside a subsystem then changes its slot's body and laws, not the hub or the
hub's callers.

Rules:
- **Elimination laws are narrow**: one law per fact a client actually extracts, not an unfolding.
- **A coupling between subsystems** (the transport's peers must be exactly the protocol's members) is
  owned by one subsystem's slot, or stated by a named cross-slot predicate; never repeated inline in
  each hub.
- **A slot a subsystem does not need is omitted**, not defined as `True`.
- **Mixing inline premises and slots is allowed** during adoption.
- **Modes generalize; no twins**: a hub with modes is one general statement with the modes as
  parameters, the special cases one-line instances (`PRINCIPLES.md`).

## The deployment's start boundary

Each machine's `main` names its start resources (its address's listen right, the addresses it may
dial, its call units, its configuration). Each new start resource otherwise threads through the
start lemma, every share, and every `wp_main`. The start owns the boundary: a sealed bundle per
machine kind (`serverStartRes id`, `clientStartRes c`), produced once by the start lemma and
consumed by that machine's `main`. When the kit's plumbing is generated (`SETUP.md`, kitgen), the
bundle is what you put in the kit file's per-role share, so the generated files never change when a
subsystem's start resources do.

## Incremental adoption

Do not rewrite all hubs at once. Convert a subsystem to slots **the next time its hub statements must
change anyway**: the round of edits that would have touched every hub instead introduces the slot, and
the next change lands inside it. Order:

1. write the convention down in your notes;
2. on the next change to a subsystem's hub facts, introduce its slots;
3. collapse twin triples when the hub is quiet;
4. re-run the hub scripts and compare churn before and after.
