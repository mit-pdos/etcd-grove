/- Lean-first (no Rocq counterpart).

`closure(s)` (linkv.go): a new state holding the configurations of `s` and, up to the pending
puts' order, every configuration a pending put reaches from them (`ClosureOk`), closed under
pending puts (`GClosed`). Its premise bounds `s`'s configurations' lengths by `n ≤ 2^63`
(`Bounded n`, for `set`'s premise), and so are the result's (`bounded_succAt`: a configuration
it pushes is no longer than its parent).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.linkv

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv.Assumptions]

/-- See the file header. -/
abbrev closure.spec : Prop :=
  ∀ (s : GoSlice) (cs : List kvConfig) (gs : List GCfg) (dq : DFrac) (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv ∗
      s ↦*{dq} cs ∗ ([∗list] c;g ∈ cs;gs, cfgOwn c g) ∗ ⌜n ≤ 2 ^ 63 ∧ ∀ g ∈ gs, Bounded n g⌝ }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv.closure)) (Val #s))
  {{ (out : GoSlice) (cs' : List kvConfig) (gs' : List GCfg), RET #out;
      s ↦*{dq} cs ∗ out ↦* cs' ∗ ownSliceCap kvConfig out (DFrac.own 1) ∗
      ([∗list] c;g ∈ cs';gs', cfgOwn c g) ∗
      ⌜ClosureOk gs gs' ∧ GClosed gs' ∧ ∀ g ∈ gs', Bounded n g⌝ }}

end spec

end linkv
end EtcdGrove
end Perennial
