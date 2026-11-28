/-
grpc's `status.Error(c, msg)` (`google.golang.org/grpc/status`), called by
`clientv3.WatchResponse.Err`. grpc is not translated (`Code/google_golang_org/grpc/status.toml`
declares only the names), so it is an axiom (`Proof/google_golang_org/grpc/status/Error.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `status.Error(c, msg)` (`New(c, msg).Err()`) for a code other than `codes.OK` returns a
non-nil error (a `*status.Error`), one grpc's `status` accepts (`statusErrOk`, unit P3a; it was
`errStrOk`): a leaf error whose `Error()` (it formats the code and the message) and `GRPCStatus()`
return; its description (`descIs`, what `status.FromError(err).Message()` and
`rpctypes.ErrorDesc` return) is `msg` (errdesc stage 2b, 2026-11-21: the per-run relation `descIs err msg`
of the status the error holds, until then `errDesc err = msg` of the pure `errDesc`, which no
implementation can meet for the error it allocates) (k8s etcd3 7c-2: `togRPCError`'s fallback
`status.Error(codes.Unknown, err.Error())` carries the message as its description); its dynamic
type is `*status.Error` of grpc's `internal/status` (k8s 7e-1, 2026-11-10, approved by
etcd-grove-81: `status.New(c, msg).Err()` returns `&Error{s: s}` for `c ≠ OK`, the first of
`clientErrTys`); and its value is that fresh pointer `#l` (prove-initmisc, 2026-11-20, a pure
strengthening: grpc v1.84.0 `internal/status/status.go:129`, `func (s *Status) Err() error`'s
`return &Error{s: s}` after `if s.Code() == codes.OK { return nil }`, which the pre's `c ≠ OK`
excludes; `status.go:58`, `Error` is `New(c, msg).Err()`), so a pointer error
(`errors.IsPointerError`, `rpctypes.ErrGRPCNotSupportedForLearner`'s fact). Nothing about `codes.OK`
(for which it returns `nil`).
(grpc-trusted-T, T1, 2026-11-24; interim, retired by the `status-bodies` stage, which proves this
triple over the bodies) The error's code is `c` (`statusCodeIs err c`: what `status.Code(err)` and
`status.FromError(err)`'s `Code()` return) and it carries a status (`hasGRPCStatus`: `*status.Error`
has `GRPCStatus() *Status`, `internal/status/status.go:216`, returning `e.s`, the status `New(c, msg)`
built with code `c`). Until then nothing was said of the code. -/
abbrev status.Error.spec : Prop :=
  ∀ (c : w32) (msg : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗
      ⌜(#c : val) ≠ google_golang_org.grpc.codes.OK⌝ }}
    (App (App (Val (@! google_golang_org.grpc.status.Error)) (Val #c)) (Val #msg))
  {{ (err : GoError), RET #err; ⌜err ≠ interface.nil⌝ ∗ statusErrOk err ∗ descIs err msg ∗
      ⌜∀ ii, err = GoInterface.ok ii →
        ii.ty = go.GoType.PointerType google_golang_org.grpc.internal.status.Error.ty⌝ ∗
      ⌜∀ ii, err = GoInterface.ok ii → ∃ l : Loc, ii.v = #l⌝ ∗
      statusCodeIs err c ∗ ⌜hasGRPCStatus err⌝ }}

end spec

end EtcdGrove
end Perennial
