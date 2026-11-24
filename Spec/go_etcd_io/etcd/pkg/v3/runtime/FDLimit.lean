/-
`runtime.FDLimit` (etcd's `go.etcd.io/etcd/pkg/v3/runtime`, `fds_linux.go`): over its trusted model
(`TrustedCode/go_etcd_io/etcd/pkg/v3/runtime.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.fmt.ErrorOk
public import GeneratedProof.go_etcd_io.etcd.pkg.v3.runtime

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `runtime.FDLimit()` (etcd's `pkg/runtime`, `fds_linux.go`) returns the soft `RLIMIT_NOFILE`, or `0` and an error `fmt` formats (`getrlimit`'s `syscall.Errno`). Over its trusted model (`TrustedCode/go_etcd_io/etcd/pkg/v3/runtime.lean`; prove-ps2-srvgoroutines, 2026-11-24, etcd-grove#42). -/
abbrev runtime.FDLimit.spec : Prop :=
  {{ (iprop(True) : IProp GF) }}
    (App (Val (@! go_etcd_io.etcd.pkg.v3.runtime.FDLimit)) (Val #()))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ⌜err = GoInterface.nil ∨ n = W64 0⌝ ∗ fmtErrorOkOrNil err }}

end spec

end EtcdGrove
end Perennial
