/-
`(*status.Status).Code()` (grpc's `internal/status`, names only) of a read-only status
(`grpcStatusRO`; k8s 7f-5a-P step 5, E1 (b), approved by etcd-grove-81 2026-11-15,
`notes/k8s-7f5a-draft.md` §11.2): its code. The trust boundary (an axiom,
`Proof/google_golang_org/grpc/status/Status__Code.lean`), for the etcd3 watcher's `isCancelError`
and `interpretWatchError` (`grpcError`'s `GRPCStatus().Code()`, `kErrOk`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

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

/-- `s.Code()` of a read-only status of code `c` returns `c`. Go (`internal/status/status.go`):
`if s == nil || s.s == nil { return codes.OK }; return codes.Code(s.s.Code)`, for a non-nil `s`
with a non-nil `s.s`, as every constructor builds it: a read of a status whose code never changes
(`grpcStatusRO`). -/
abbrev status.Status.Code.spec : Prop :=
  ∀ (s : Loc) (c : w32),
  {{ grpcStatusRO (PROP := IProp GF) s c }}
    (App (Val (s @!! go.GoType.PointerType google_golang_org.grpc.status.Status.ty @!! go!"Code"))
      (Val #()))
  {{ RET #c; True }}

end spec

end EtcdGrove
end Perennial
