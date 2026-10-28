# Examples

Specs the user reviewed: each file gives the first version, the user's critiques in order with what
each changed, and the spec after them. Read this index, then open only the examples whose kind or
principles match your target.

| Example | Kind | Shows |
|---|---|---|
| [put.md](put.md) | a write through a replicated server (atomic update, fired at most once) | API not implementation; vocabulary in scope; no vacuous disjunct; a thread token for reader slots; the update in the triple; no slack constants |
| [range.md](range.md) | a read, linearizable or stale (persistent atomic update) | the result predicate carries the facts; a stale read fires at the current state; compare whole specs; no disjunction of alternative specs |

Keep it small: an example is readable in one sitting; when a newer example shows the same principles
better, remove the older one from this index (git keeps it).
