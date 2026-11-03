# `bootstrap`'s contracts reviewed as a whole (2026-11-03)

`bootOk`, the trusted post of etcd's untranslated `bootstrap` (`bootstrapContract`, a premise of
`NewServer.spec`), had changed in five stages, each reviewed for its own part. Reviewed whole, with a
Go test at the pinned fork checking every Go-checkable conjunct in every mode
(`etc/spec-test/bootstrap/`), it held of no run of `bootstrap`, so every closed server result was
vacuous. Three fresh spec-reviewer rounds over a scratch candidate; the user approved candidate 3
and its seven recommendations (`notes/decisions.md`, "The whole-`bootOk` review").

## The first version (round 0, the statements at `b28007bd7c`)

- `Hnew ∷ backend.newPost …` (every write-back token, `ownToks γ.wb wbInit`), `%HN ∷ ⌜N + 7 ≤ wbInit⌝`
  in the post; `#Hclose ∷ □ {{ True }} b.Close() {{ True }}`.
- `lateWB`'s unregistered arm at an empty `Key` bucket (`pvckEmpty`), in `bootOk` and in the restart
  case `bootOkR`.
- The contract for every configuration `bootCfgRO` reads; `bootOkR`'s members fixed to `ps` while
  its member records come from the image's log; `#Hbh` stated twice.

## The critiques, and what each changed

1. **Round 1** (a fresh reviewer, given the targets, the Go code and the callers): `newPost`'s every
   token forces the read buffer's version to `0` through the batch lock's bound, and `bootstrap`
   writes back twice (confirmed by the Go test: `bufVersion = 2`); `pvckEmpty` false at a restart;
   configurations where Go panics (nil logger); a second `Close` panics; no fresh-directory
   resource; two contracts of one function. The candidate: `newPostK … (bootLeft N)` with
   `N + 7 + bootWB ≤ wbInit` a precondition, configuration premises, a one-shot `Hclose`, a
   fresh-directory token.
2. **Round 2**: the fresh-directory token minted by adequacy is not exclusive (premises enter as
   `⊢ premises`, which mints it twice): withdrawn, E left open for a semantic extension; a missed
   field (`DedicatedWALDir`: the WAL elsewhere than the image's files say); `lateWB` changed only for
   the false case (`bootOkR`'s own `lateWBR`), the general change (`NewStore` learning the values
   under the lock) deferred to the contracts' merge.
3. **Round 3**: one more unconstrained field the post relies on (`BackendBatchLimit`, through
   `d.P.Wf`); fields only the examples' `cfgOk` fixed (`ElectionTicks`, `TickMs`, `NewCluster`)
   moved into the contract's premises; the static-cluster premise on whole member records is false
   once a member has published its attributes: ids and peer URLs only.

## The approved spec

- `Hnew ∷ backend.newPostK … (bootLeft N) d.be D` (`N + 7` tokens and the open token); the bound a
  precondition `⌜N + 7 + bootWB ≤ wbInit⌝`, `bootWB := 4` (two needed); `%HN` gone.
- `bootstrapContract`'s pre `⌜bootCfgOk cfg ∧ bootCfgFresh cfg U ∧ N + 7 + bootWB ≤ wbInit⌝ ∗ …`;
  the restart contract's premise adds `ForceNewCluster = false`, `DedicatedWALDir = ""` and the
  members' ids and peer URLs the boot log's; `NewServer.spec` takes the new conditions as premises.
- `bootOkR` over `lateWBR`; one `#Hbh`.
- Deferred, each with its reason: the one-shot `Hclose` (a store closer must give its reader tokens
  back first), the fresh directory (a semantic extension), the merge of the two contracts.

**Principles shown**: a trusted post is checked as a whole, against Go, conjunct by conjunct, in every
mode ("Sound: true of the code"; a test whose known-false list shrinks as repairs land); a bound the
caller must meet is a precondition, not a post conjunct about the caller's own parameter ("Pure
premises go in the precondition"); a resource total fixed at creation is false once the function has
already spent some of it ("Read the definitions of the resources a spec takes"); an exclusivity
token from an entailment premise is not exclusive; every configuration field a trusted post relies
on is a premise of the contract, not of one client's configuration predicate.
