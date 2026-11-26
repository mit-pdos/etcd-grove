/-
`status.Errorf` (grpc's `status`, translated with its body since status-bodies, 2026-11-25; until then
the trust boundary, an axiom). Lean-first (no Rocq counterpart); the request path
(`notes/decisions.md`, "The request path").
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

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

end spec

end EtcdGrove
end Perennial
