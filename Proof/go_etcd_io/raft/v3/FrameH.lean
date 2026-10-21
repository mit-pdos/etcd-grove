/-
`frameH`: Iris's frame pattern `$H` for use inside a tactic macro's quotation.

In an Iris spec pattern `$H` frames the hypothesis `H` (`wp_apply foo $$ [$H]`). Inside a
syntax quotation (`` `(tactic| …) ``, a `macro`'s body) Lean reads `$H` as an antiquotation
instead, so a proof block that frames a hypothesis cannot become a macro body as written. The
macro writes ``$(frameH `H)`` there: `frameH` builds the node the parser makes for `$H` in a
proof. The file-local macros that factor a block repeated across a proof's branches use it
(notes/decisions.md, "Repeated proof blocks as file-local macros"); the general fix is a frame
syntax in Iris-Lean that works inside a quotation, which would make this unnecessary.
-/
module

public import Lean

@[expose] public section

namespace Perennial.EtcdGrove

open Lean

/-- `$H` (frame `H`) in an Iris spec pattern, for a tactic macro's quotation, where `$H` would
parse as an antiquotation. -/
meta def frameH (n : Name) : TSyntax `frameIdent :=
  ⟨Syntax.mkAntiquotNode `ident (mkIdent n)⟩

end Perennial.EtcdGrove
