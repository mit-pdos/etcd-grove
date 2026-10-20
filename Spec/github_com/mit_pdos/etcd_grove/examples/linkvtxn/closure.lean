/- Lean-first (no Rocq counterpart).

`closure(s)` (linkvtxn.go): `s` with every configuration reachable by pending writes taking
effect (`ClosureOk`), closed (`GClosed`), and the invariant `Bounded n` kept (its premise: the
configurations of `s` keep it, `mstep`'s bound follows).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.linkvtxn


section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

/-- See the file header. -/
abbrev closure.spec : Prop :=
  ∀ (s : GoSlice) (cs : List mcfg) (gs : List GCfg) (dq : DFrac) (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkvtxn ∗
      s ↦*{dq} cs ∗ ([∗list] c;g ∈ cs;gs, cfgOwn c g) ∗ ⌜n < 2 ^ 63 ∧ ∀ g ∈ gs, Bounded n g⌝ }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkvtxn.closure)) (Val #s))
  {{ (out : GoSlice) (cs' : List mcfg) (gs' : List GCfg), RET #out;
      s ↦*{dq} cs ∗ out ↦* cs' ∗ ownSliceCap mcfg out (DFrac.own 1) ∗
      ([∗list] c;g ∈ cs';gs', cfgOwn c g) ∗
      ⌜ClosureOk gs gs' ∧ GClosed gs' ∧ ∀ g ∈ gs', Bounded n g⌝ }}

end spec

end linkvtxn
end EtcdGrove
end Perennial
