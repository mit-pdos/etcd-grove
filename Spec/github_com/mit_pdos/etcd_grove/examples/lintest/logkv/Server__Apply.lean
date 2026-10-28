/- Lean-first (no Rocq counterpart).

`(*Server).Apply` (logkv.go): the method value `s.Apply` is logically atomic against the
register's model (`applySpec`, `Proof/.../lintest/Defs.lean`; the caller's thread token is lent and given
back untouched), over the register's abstract state
(`regState γ`), with no invariant of its own (`Eapp = ∅`), for a boxed `Op` input (`regInOk`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.logkv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace logkv

open Iris Iris.BI github_com.anishathalye.porcupine

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.logkv.Assumptions]

/-- See the file header. -/
abbrev Server.Apply.spec : Prop :=
  ∀ (γ : GName) (s : Loc),
  ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest.logkv -∗
    isServer γ s -∗
    applySpec (regS (GF := GF)) regInOk (regState γ) ∅
      (methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.lintest.logkv.Server.ty) go!"Apply" #s)

end spec

end logkv
end lintest
end EtcdGrove
end Perennial
