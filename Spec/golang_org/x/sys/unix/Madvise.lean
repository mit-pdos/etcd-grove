/-
`unix.Madvise(b, advice)` with a paging hint (`MADV_NORMAL`, `MADV_RANDOM`, `MADV_SEQUENTIAL`,
`MADV_WILLNEED`; minibolt passes `MADV_RANDOM`) (this repository's `golang.org/x/sys/unix`,
project `bboltfs`): the model (`TrustedCode/golang_org/x/sys/unix.lean`) returns `nil` or an
arbitrary `Errno`, with no effect. Proved in `Proof/golang_org/x/sys/unix/Madvise.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import GeneratedProof.golang_org.x.sys.unix
public import Proof.syscall.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [golang_org.x.sys.unix.Assumptions]

/-- See the file header. -/
abbrev golang_org.x.sys.unix.Madvise.spec : Prop :=
  ∀ (sl : GoSlice) (advice : w64), advice.toNat ≤ 3 →
  {{ (emp : IProp GF) }}
    (App (App (Val (@! golang_org.x.sys.unix.Madvise)) (Val #sl)) (Val #advice))
  {{ (e : w64), RET #(errnoErr e); emp }}

end spec

end EtcdGrove
end Perennial
