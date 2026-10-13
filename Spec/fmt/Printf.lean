/-
`fmt.Printf`: the trust boundary, for arguments that are not all of predeclared basic types
(as `fmt.Errorf`, `Spec/fmt/Errorf.lean`, whose `fmt.argsOk` it shares). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.fmt.Errorf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-- **`fmt.Printf(format, args...)`** returns (a count and an error, not modelled), for
arguments that are `fmt.argsOk`; the arguments' slice comes back. The output is not
modelled. -/
abbrev fmt.Printf.spec : Prop :=
  ∀ (format : GoString) (args_sl : GoSlice) (xs : List GoInterface) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs ∗ fmt.argsOk xs }}
    (App (App (Val (@! _root_.Perennial.fmt.Printf)) (Val #format)) (Val #args_sl))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err); args_sl ↦*{dq} xs }}

end spec

end EtcdGrove
end Perennial
