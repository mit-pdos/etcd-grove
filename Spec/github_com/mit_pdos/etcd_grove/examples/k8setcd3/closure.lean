/- Lean-first (no Rocq counterpart).

`closure(s)` (k8setcd3.go): `s` with every configuration reachable by pending writes taking
effect (`ClosureOk`), closed (`GClosed`), and the bound `Bounded n` kept (its premise: the
configurations of `s` keep it; `mstep`'s premise follows).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.MDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.k8setcd3


section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

/-- See the file header. -/
abbrev closure.spec : Prop :=
  ∀ (st0 : GSt) (s : GoSlice) (cs : List mcfg) (gs : List GCfg) (dq : DFrac) (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 ∗
      s ↦*{dq} cs ∗ ([∗list] c;g ∈ cs;gs, cfgOwn c g) ∗ ⌜n < 2 ^ 63 ∧ ∀ g ∈ gs, Bounded n g⌝ }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8setcd3.closure)) (Val #s))
  {{ (out : GoSlice) (cs' : List mcfg) (gs' : List GCfg), RET #out;
      s ↦*{dq} cs ∗ out ↦* cs' ∗ ownSliceCap mcfg out (DFrac.own 1) ∗
      ([∗list] c;g ∈ cs';gs', cfgOwn c g) ∗
      ⌜ClosureOk st0 gs gs' ∧ GClosed st0 gs' ∧ ∀ g ∈ gs', Bounded n g⌝ }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
