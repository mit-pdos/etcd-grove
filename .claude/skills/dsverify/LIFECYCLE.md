# Objects that change hands: design the lifecycle before proving

An object that passes between threads during its life (a request run by its own goroutine and
recycled through a pool, a buffer sent over channels, a connection with a reader and a writer) needs
an invariant that covers its whole life; otherwise its gaps surface one proof round at a time. Before
a proof relies on it, its package writes one table per such object type, pooled messages included.

- **Shrink it first** (`PRINCIPLES.md`, Resources): fields fixed before publication are persistent
  facts, fields that always move together are one bundle, a field one thread alone touches stays out.
  Add a ghost name only for what no fact about the fields and the transitions can say.
- **Rows: the states** (free, created, owned, queued, running, borrowed inline, stopping, stopped,
  retired). Each gives the object's parts (points-to's, ghost shares, tokens), the enclosing fields
  its holder reads and the loan they come from, the facts a stopped row keeps for later readers, and
  who may still hold a stale pointer.
- **Transitions: every code point that moves it**, read off the Go: allocation and reuse, publication,
  sends and receives, spawn and exit, stop, error paths, a send to a retired incarnation. Each gives
  the rows before and after, the shares that change hands, and what orders it against racing ones.
  Where a method of the object (or of a library object inside it) can retire it, the rest of the
  caller holds only a persistent fact.
- **Columns over the proof's state.** Once the ghost carriers are chosen, derive the share columns
  over them, per owner kind, not only over the Go fields: proof-only state changes hands too. Mark
  each access atomic or not, and give each carrier's source conjunct by conjunct.
- **Name agreement, generated.** For every `∃` in the definitions and specs the rows mention, a script
  lists the persistent fact that identifies that name or value across its holders.
- **Checked against the code**: a fresh agent, given the table and the Go code (not the proofs), walks
  every function that touches the object and reports code points with no transition and shares given
  twice, lost or missing at a use. Each (re-)derivation first books the open requests in the notes.
- **Repair the table, then its neighbours, then the Lean.** After each repair, re-check the
  transitions that race with it and the later steps that meet the state it leaves: repairs carry
  defects, and this check finds them before a proof does.
- **Converge on structure.** Structure settles early; cells keep changing. Only a structural gap (a
  missing row or transition) counts: when two rounds in a row each find one, stop proving against the
  table, re-derive it in one pass over every function that touches the object, and check it. A gap in
  one cell is a local repair with the neighbour re-check.
- **After two re-derivations, simplify**: propose a smaller design or a code change to the user
  (fewer holders, a fresh immutable header per incarnation), not another revision. A table of many
  hundreds of lines for one object means too many holders.
