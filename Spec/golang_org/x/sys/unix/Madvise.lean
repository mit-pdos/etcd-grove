/-
`unix.Madvise(b, advice)` with a paging hint (`MADV_NORMAL`, `MADV_RANDOM`, `MADV_SEQUENTIAL`,
`MADV_WILLNEED`; minibolt passes `MADV_RANDOM`) (this repository's `golang.org/x/sys/unix`,
project `bboltfs`): the model (`TrustedCode/golang_org/x/sys/unix.lean`) returns `nil` or an
arbitrary `Errno`, with no effect (the extension's `Madvise` step, since 2026-11-17: hence `osInv`).
A client that names the mapping `b` is (`M = some (p, dq, m)`: `b` starts a mapping of `m`, held
with the file's `OsMeta` at any fraction, and is non-empty) learns that an error witnesses that
**the file system can fail** (`⌜¬ FsNoErr⌝`: under the premises `FsNoErr` names, `madvise` of a
mapping returns 0; session S6 folded the former `specNoErr`/`specW` into this spec,
`notes/bbolt-integration-plan.md`); one that does not (`M = none`) learns nothing.
Proved in `Proof/golang_org/x/sys/unix/Madvise.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import GeneratedProof.golang_org.x.sys.unix
public import Proof.syscall.Base
public import GooseLang.Ext.Fs.FsNoErr

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [golang_org.x.sys.unix.Assumptions]

/-- See the file header. -/
abbrev golang_org.x.sys.unix.Madvise.spec : Prop :=
  ∀ (sl : GoSlice) (advice : w64) (M : Option (Ino × DFrac × OsMeta)),
  advice.toNat ≤ 3 → 0 ≤ sl.len.toInt →
  (∀ p dq m, M = some (p, dq, m) →
    0 < sl.ptr.addr ∧ 0 < sl.len.toInt ∧ ∃ n, m.maps !! sl.ptr = some n) →
  {{ osInv (GF := GF) ∗
      (match M with | none => iprop(emp) | some (p, dq, m) => osMeta (GF := GF) p dq m) }}
    (App (App (Val (@! golang_org.x.sys.unix.Madvise)) (Val #sl)) (Val #advice))
  {{ (e : w64), RET #(errnoErr e);
      (match M with | none => iprop(emp) | some (p, dq, m) => osMeta (GF := GF) p dq m) ∗
      ⌜M = none ∨ e = 0 ∨ ¬ FsNoErr⌝ }}

end spec

end EtcdGrove
end Perennial
