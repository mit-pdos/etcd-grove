/-
`status.Errorf` (grpc's `status`, translated with its body since status-bodies, 2026-11-25; until then
the trust boundary, an axiom). Lean-first (no Rocq counterpart); the request path
(`notes/decisions.md`, "The request path").
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Spec.fmt.Sprintf

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `status.Errorf(c, format)` with no arguments (`a` is `nil`: etcd's calls, `key.go:174,177`) and a
format without `%`, for a code other than `codes.OK`: `status.Error(c, format)` (`status/status.go:63-65`:
`Error(c, fmt.Sprintf(format, a...))`, and `Sprintf` of such a format returns it), whose post it has
(`Error.spec`). (status-bodies, 2026-11-25: proved over the body, SpecPlan's statement; until then an
axiom for any `format` and any `args`, unowned, which `fmt.Sprintf` reads, with the post `err ≠ nil`
only: a premise added, which the one caller, `checkRangeStreamRequest`, meets, and a post
strengthened; `notes/specs-only/ledger.md`.) -/
abbrev status.Errorf.spec : Prop :=
  ∀ (c : w32) (format : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗
      ⌜(#c : val) ≠ google_golang_org.grpc.codes.OK ∧ W8 37 ∉ format⌝ }}
    (App (App (App (Val (@! google_golang_org.grpc.status.Errorf)) (Val #c)) (Val #format)) (Val #slice.nil))
  {{ (err : GoError), RET #err; ⌜err ≠ interface.nil⌝ ∗ statusErrOk err ∗ descIs err format ∗
      ⌜∀ ii, err = GoInterface.ok ii →
        ii.ty = go.GoType.PointerType google_golang_org.grpc.internal.status.Error.ty⌝ ∗
      ⌜∀ ii, err = GoInterface.ok ii → ∃ l : Loc, ii.v = #l⌝ ∗
      statusCodeIs err c ∗ ⌜hasGRPCStatus err⌝ }}

/-- `status.Errorf(c, format, args...)` for a code other than `codes.OK`, a format of the pieces `ps`
and arguments that are the `args` (`fmt.isArg`), in `fmt.Sprintf`'s verified subset (`fmt.Fits`):
`status.Error(c, s)` (`status/status.go:63-65`) for the string `s` `Sprintf` returns
(`fmt.Out ps args s`), with `Error.spec`'s post for it; the arguments' slice and what `isArg` holds come
back. `spec` is the case without arguments; this one is for grpc's `createHeaderFields`
(`"transport: per-RPC creds failed due to error: %v"` of the credentials' error). -/
abbrev status.Errorf.spec_args : Prop :=
  ∀ (c : w32) (format : GoString) (ps : List _root_.Perennial.fmt.Piece) (args_sl : GoSlice)
    (xs : List GoInterface) (args : List _root_.Perennial.fmt.Arg) (dq : DFrac),
    format = _root_.Perennial.fmt.encode ps → _root_.Perennial.fmt.Fits ps args →
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗
      ⌜(#c : val) ≠ google_golang_org.grpc.codes.OK⌝ ∗ args_sl ↦*{dq} xs ∗
      [∗list] x;a ∈ xs;args, _root_.Perennial.fmt.isArg x a }}
    (App (App (App (Val (@! google_golang_org.grpc.status.Errorf)) (Val #c)) (Val #format))
      (Val #args_sl))
  {{ (err : GoError), RET #err; ∃ s : GoString, args_sl ↦*{dq} xs ∗
      ([∗list] x;a ∈ xs;args, _root_.Perennial.fmt.isArg x a) ∗ ⌜_root_.Perennial.fmt.Out ps args s⌝ ∗
      ⌜err ≠ interface.nil⌝ ∗ statusErrOk err ∗ descIs err s ∗
      ⌜∀ ii, err = GoInterface.ok ii →
        ii.ty = go.GoType.PointerType google_golang_org.grpc.internal.status.Error.ty⌝ ∗
      ⌜∀ ii, err = GoInterface.ok ii → ∃ l : Loc, ii.v = #l⌝ ∗
      statusCodeIs err c ∗ ⌜hasGRPCStatus err⌝ }}

end spec

end EtcdGrove
end Perennial
