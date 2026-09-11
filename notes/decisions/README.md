# Decisions

One file per durable decision: `NNNN-kebab-slug.md`, numbered in order.

Record a decision when you pick a specification, an invariant, an abstraction
boundary, or a trust boundary, **and there was a real alternative**. The point
is to stop the next agent from silently re-deciding it the other way, and to
make it possible to revisit deliberately.

Do not record routine choices with an obvious answer.

## Template

```markdown
# NNNN. Short imperative title

- **Date:** YYYY-MM-DD
- **Status:** accepted | superseded by NNNN

## Context

What forced a choice. Include the constraints that actually bound it.

## Decision

What we do.

## Alternatives considered

What else was on the table and why it lost. Be specific about the cost that
killed it — this is the part that saves the next person time.

## Consequences

What this makes easy, what it makes hard, and what would have to change to
revisit it.
```

## Index

- [0001 — Keep upstream Go module and Rocq logical paths](0001-keep-upstream-module-and-logical-paths.md)
