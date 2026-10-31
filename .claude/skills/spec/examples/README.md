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
| [watch-auth.md](watch-auth.md) | a proved spec that must gain a fact only axioms give (the watch with auth on) | strengthen axioms in place when one proof forbids a split, listing collections; the gate over a named environment; check what an axiom admits before strengthening it |
| [auth-history-tie.md](auth-history-tie.md) | a cap tying a library's ghost history to the server's model, and a client's read law over it | a premise its supplier can prove (at the actual state, not every state); guard by the check where the code has done it; use only what the client's spec exports; masks as subset premises |
| [apply-uber-contract.md](apply-uber-contract.md) | a function calling through an interface, three specs of it at three contracts; a server that needs the on contracts | one spec parametric in the method's contract; the constructor establishes the contract; store it at the level called, for every object the field may hold |
| [apply-loop-merge.md](apply-loop-merge.md) | a pair of specs (mode off and on) merged into one at the environment's mode, callers in another track's proof | the restoring corollary states the old spec exactly, deriving the merged premises from the old precondition; check a "callers untouched" claim against the order the caller's proof obtains its facts |
| [compaction-in-place.md](compaction-in-place.md) | a new mode (compaction) in a family of shared predicates and the specs over them; a library spec with an unreachable error arm | redefine in place, not mode-indexed copies; no arm the precondition excludes |
| [member-auth-facts.md](member-auth-facts.md) | a getter over a read-only field, and a fact exported up a constructor chain to a started member | export where Go makes it true, gated by the mode; keep an exported restatement unchanged by dropping the new conjunct |
| [irr-depth.md](irr-depth.md) | a trust-boundary axiom false at deep inputs, repaired by a premise carried up to a configuration bound | a premise, not a post that claims termination Go does not give; a contract states the receiver's need, not the supplier's mechanism; a configuration bound exactly as strict as the code; a fact kept in the object that copied it |
| [reply-size.md](reply-size.md) | two trust-boundary axioms false at huge replies, repaired by an opaque workload premise on the constructor of the tokens they consume | a workload premise on the resource's only producer, carried by the resource; take it where the proof reaches the producer, not beside a sibling premise; check fast paths for aliasing before a fresh-copies size argument |

Keep it small: an example is readable in one sitting; when a newer example shows the same principles
better, remove the older one from this index (git keeps it).
