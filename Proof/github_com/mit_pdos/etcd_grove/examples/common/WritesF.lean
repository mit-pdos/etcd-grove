/-
**The writers' log, generic in what a logged Put is known to be** (2026-10-26). Lean-first (no
Rocq counterpart).

`wsInvF w OkF`: the lock invariant of the log `w` (a `Writes`): its slice of successful Puts
(`wrec`: the reply's header revision, the key, the value), each with the caller's persistent fact
`OkF` (what `Writer`'s caller's write update gives, `Writer.spec`): watchkv's of its own invariant
over the KV state, cachekv's of the clients' model (`okFactKM`, `WritesKM.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.WatchBase

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The log's lock invariant** (see the file header). -/
def wsInvF (w : Loc) (OkF : wrec → IProp GF) : IProp GF :=
  iprop(∃ (sl : GoSlice) (oks : List wrec),
    structFieldRef github_com.mit_pdos.etcd_grove.examples.common.Writes go!"Ok" w ↦ sl ∗
    sl ↦* oks ∗ ownSliceCap wrec sl (DFrac.own 1) ∗
    □ [∗list] p ∈ oks, OkF p)

end defs

end common
end EtcdGrove
end Perennial
