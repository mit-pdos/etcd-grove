# Examples

Specs the user reviewed: each file gives the first version, the user's critiques in order with what
each changed, and the spec after them. Read this index, then open only the examples whose kind or
principles match your target.

| Example | Kind | Shows |
|---|---|---|
| [put.md](put.md) | a write through a replicated server (atomic update, fired at most once) | API not implementation; vocabulary in scope; no vacuous disjunct; a thread token for reader slots; the update in the triple; no slack constants |
| [range.md](range.md) | a read, linearizable or stale (persistent atomic update) | the result predicate carries the facts; a stale read fires at the current state; compare whole specs; no disjunction of alternative specs |
| [authinfo.md](authinfo.md) | two specs of one function (plain and bound) merged into one | a mode gate as a named margin, not two specs; know the margin |
| [admin-history.md](admin-history.md) | requests that change shared state, and a client that concludes the state stays put (the auth history, `SetUp`) | say who may change shared state (an exclusive view, the update a resource); the atomic precondition the resource alone, the admission in the post; the client's post the abstract state |
| [auth-history-tie.md](auth-history-tie.md) | a cap tying a library's ghost history to the server's model, and a client's read law over it | a premise its supplier can prove (at the actual state, not every state); guard by the check where the code has done it; use only what the client's spec exports; masks as subset premises |

Keep it small: an example is readable in one sitting; when a newer example shows the same principles
better, remove the older one from this index (git keeps it).
