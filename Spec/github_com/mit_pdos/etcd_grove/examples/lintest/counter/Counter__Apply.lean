/- Lean-first (no Rocq counterpart).

`(*Counter).Apply` (counter.go): the method value `c.Apply` is logically atomic against the
counter's model (`applySpec`, `Proof/.../lintest/Defs.lean`), over the counter's abstract state
(`counterState γ`), with no invariant of its own (`Eapp = ∅`: its linearization point is in
the critical section, which the mutex guards), for any input.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.counter.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace counter

open Iris Iris.BI github_com.anishathalye.porcupine

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.counter.Assumptions]

/-- See the file header. -/
abbrev Counter.Apply.spec : Prop :=
  ∀ (γ : GName) (c : Loc),
  ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest.counter -∗
    isCounter γ c -∗
    applySpec (counterS (GF := GF)) (counterState γ) ∅
      (methods (go.GoType.PointerType
        github_com.mit_pdos.etcd_grove.examples.lintest.counter.Counter.ty) go!"Apply" #c)

end spec

end counter
end lintest
end EtcdGrove
end Perennial
