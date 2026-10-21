/-
`strconv.FormatUint`: the trust boundary (Perennial translates `strconv` names-only). Lean-first
(no Rocq counterpart); the request path's unit 4a (the read loop's trace field).
(The copy for the parallel tree `RaftWitness/` of `Spec/strconv/FormatUint.lean`, importing the
part's raft `Base` (`strconv`'s package instance)
instead of the server's `BaseApply`.)
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `strconv.FormatUint(i, base)` of a base in `2..36`: a string (the digits of `i`; the read
loop's trace field, which the model does not read); it returns. (Go panics on any other base,
`internal/strconv/itoa.go`; the premise since audit B4b, 2026-10-18.) -/
abbrev strconv.FormatUint.spec : Prop :=
  ∀ (i : w64) (base : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.strconv ∗ ⌜2 ≤ sint.Z base ∧ sint.Z base ≤ 36⌝ }}
    (App (App (Val (@! _root_.Perennial.strconv.FormatUint)) (Val #i)) (Val #base))
  {{ (str : GoString), RET #str; True }}

end spec

end EtcdGrove
end Perennial
