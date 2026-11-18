/- Lean-first (no Rocq counterpart).

# The examples' extensions (2026-10-26; since 2026-11-02 the request ids' issue record)

Perennial's semantics runs a program against a closed list of GooseLang extensions (Perennial
`4ce1bd4da`, `GooseLang/Ext.lean`), which replaced the single FFI. The examples use no extension
operation: their proofs are generic over the list (`[GooseExts] [GooseSemantics] [GooseInterp]`),
and their closed theorems (`examples/*/Adequacy.lean`) close it as `[trivialExt]`, an extension
with no operations, no values and no state, whose ghost state is trivial. (Before, they closed it
with the disk FFI, whose operations they did not use either; Perennial removed it, `7b607280f`.)

Since the restart plan's R2c stage 2 (2026-11-02) the closure, still named `trivialExts` (the
examples' adequacy files use the names), is `[idIssueExt]`: the request ids' issue record
(`GooseLang/Ext/IdIssue`), the model-only state the trusted `idutil` `Generator.Next` steps through.
Its only operation is that model's; a program that never runs it sees GooseLang's semantics alone,
as with `trivialExt`, which stays defined here, unused.

Since 2026-11-15 (`wal-lean`, the user's decision (A)) the etcd and Kubernetes examples, whose
initialization runs `fileutil`'s (an `F_OFD_GETLK` probe over the Linux file extension), close it as
`FsExts.lean`'s `etcdFsExts` (`[idIssueExt, fsExt]`) instead; the raft, mvcc and lintest examples keep
this one.
-/
module

public import Perennial.GooseLang.Adequacy
public import Perennial.GooseLang.Lifting
public import Perennial.GooseLang.Countable
public import Perennial.Ghost.GhostVar
public import Perennial.Golang.Defn.PostLang
public import GooseLang.Ext.IdIssue.Impl

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-- **The examples' extensions: the request ids' issue record alone** (since 2026-11-02, the restart
plan's R2c stage 2; until then `trivialExt`). The record (`GooseLang/Ext/IdIssue`) is what the
trusted model of `idutil`'s `Generator.Next` steps through; a program that never calls it sees
GooseLang's semantics, as with `trivialExt`. The names stay (`trivialExts`, ...), so that the
examples' closures need not change but for the extension's ghost state (`goosePreGExts`: the
universal camera, `IdIssueGpreS`) and its `HasExt` (`trivialExts_hasExt`). -/
@[reducible] def trivialExts : GooseExts := ⟨[idIssueExt]⟩

attribute [local instance] trivialExts

@[reducible] def trivialExtsSemantics : GooseSemantics := ⟨(idIssue_semantics, ⟨⟩)⟩

attribute [local instance] trivialExtsSemantics

end EtcdGrove
end Perennial
