/-
`encoding/hex`'s package initialization (names only otherwise; `Code/encoding/hex.toml`,
`TrustedCode/encoding/hex.lean`): its `isPkgInit` is `True` (it imports nothing and the trusted
initializers allocate nothing), and `initialize'` runs the trusted initializers, which do nothing.
What a target that imports `encoding/hex` without calling it needs to prove its own initialization
(kits/epaxos-net/ISSUES.md; as `Proof/encoding/gob.lean`).
-/
module

public import Perennial.Proof.ProofPrelude
public import Harness.GeneratedProof.encoding.hex

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace encoding.hex

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `encoding/hex`'s package-initialized state: nothing (no variable is allocated). -/
instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.encoding.hex :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.encoding.hex :=
  build_get_is_pkg_init_wf

end wps

end encoding.hex

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [encoding.hex.Assumptions]

/-- `encoding/hex`'s `initialize'`: the trusted initializers, which do nothing. -/
abbrev encoding.hex.initialize'.spec : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp GF),
  GetIsPkgInitProp pkg_id.encoding.hex get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }}
      (App (Val encoding.hex.initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.encoding.hex }}

theorem encoding.hex.initialize'.wp_proof : encoding.hex.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  repeat (first | wp_call | wp_auto)
  repeat (first | wp_func_call | wp_call | wp_auto)
  iframe Hown
  is_pkg_init_finish

end spec

end Perennial
