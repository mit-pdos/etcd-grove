# Brief: an integration agent

Every batch (`batches.md`) has been drafted, reviewed by separate agents and repaired at least
once. The batches were written in parallel, so the names one batch cites of another, the
provisional names one batch declared for another's predicate, and the proof sketches' assumptions
about callees have drifted. Your job is to close that gap for the directories you own, so that
**every spec in them is provable from the specs it cites, as those specs now are**.

Read first: `notes/specs-only/README.md`, the batch reports (`notes/specs-only/batch-*.md`) of
your batches and of the batches they call or are called by (the "Round N repairs" sections and the
rename tables, especially W0's rounds 1-6 in `batch-W0.md`), and the `req/` files addressed to your
batches.

## Do

1. **Build.** `etc/specs-build.sh --dir <each directory you own>` must pass. Fix what fails in your
   directories.
2. **Provisional names.** Every name your batches declared for another batch's predicate
   ("provisional", "placeholder", "slot for 3h", ...): replace it by the owner's real name (import
   the owner's `Api.lean`), or, if the owner has no such predicate, keep it and record the gap.
   Every name in a proof sketch or docstring that does not exist any more: fix it.
3. **Sketches against callees.** For each spec in your directories, read its proof sketch and check
   each step against the callee spec it uses *as it now is*: premises the caller can establish,
   posts that give what the next step needs, laws that exist. Where they do not fit, fix the side
   you own (restate your spec, or your sketch) or, if the callee is wrong or too weak, record it.
4. **Requests both ways.** Read every `req/` section addressed to your batches and check it is met
   by your specs now; meet it or say why not. Check the requests your batches made of others are
   met by the others' current specs.
5. **Snippets.** `cd examples && go vet ./specreq/<your aliases>/...` (or `gofmt -l` for
   `//go:build ignore` files) still passes.

## Don't

Edit outside your directories (and their `examples/specreq/` aliases, and `notes/specs-only/`).
Proofs, axioms, theorems, sorry. Git commands that change anything. Re-open a decision recorded as
the coordinator's or the user's in a batch report (say if you think one is wrong).

## Report

`notes/specs-only/integration-<id>.md`: what you changed (by file), the provisional names resolved
and those left (with why), the sketches you found not to fit and how you fixed each, what you need
from directories you don't own (precisely, by file and name), and the build result of every
directory you own. Final message: the same, short.
