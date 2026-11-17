/-
Lean-first (no Rocq counterpart).

# The member's raft-like state after a restart (`member.resume`, W4c U5)

`resume(c)` (`examples/etcd/wal/wal.go`) sets the member's raft-like fields from what the restart read:
the term (at least 1), the vote, the base, the last index (`tResumeLast`: the last entry's, or the
base's), the terms of the base and of each entry (`tResumeTerms`), the commit clamped to the last index.
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI

section pure
variable [GooseExts]

/-- `resume`'s term: the read's, or 1 if 0. -/
def tResumeTerm (c : TContents) : w64 := if c.hs.term' = W64 0 then W64 1 else c.hs.term'

/-- `resume`'s last index: the last entry's, or the base's. -/
def tResumeLast (c : TContents) : w64 := c.ents.foldl (fun _ e => e.index') c.baseIdx

/-- `resume`'s terms: the base's, then each entry's (a later one overriding). -/
def tResumeTerms (c : TContents) : GMap w64 w64 :=
  c.ents.foldl (fun M e => <[e.index' := e.term']> M) (<[c.baseIdx := c.baseTerm]> ∅)

/-- `resume`'s commit: the read's, at most the last index. -/
def tResumeCommit (c : TContents) : w64 :=
  if uint.nat (tResumeLast c) < uint.nat c.hs.commit' then tResumeLast c else c.hs.commit'

end pure

end etcd_wal
end EtcdGrove
end Perennial
