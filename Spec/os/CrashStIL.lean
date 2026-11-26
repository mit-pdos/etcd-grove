/-
The vocabulary of the local crash specs (`Spec/os/CrashStILR.lean`) of the `os`, `syscall` and
`golang.org/x/sys/unix` calls on a file in the inode-keyed crash invariant, from **the local caller's
part** `csOwnIL i γ γa s a` (`Proof/os/CrashStIL.lean`: the token, half of the `OsMeta`, the state idle
with nothing frozen; no bytes). (W3, 2026-11-26: the specs over `csInvI` that this file held were
retired, unused, once bbolt moved to their versions over `csInvIR`.) Lean-first (no Rocq counterpart).
-/
module

public import Spec.os.CrashStI
public import Proof.os.CrashStIL

@[expose] public section

noncomputable section

namespace Perennial

open Fs

namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

end spec

end EtcdGrove
end Perennial
