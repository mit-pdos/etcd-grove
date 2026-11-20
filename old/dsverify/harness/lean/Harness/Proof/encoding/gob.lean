/-
`encoding/gob`'s package initialization (names only otherwise; `Code/encoding/gob.toml`,
`TrustedCode/encoding/gob.lean`): its `isPkgInit` is `True` beyond `io`'s (the trusted
initializers allocate nothing), and `initialize'` runs `io`'s and the trusted initializers that do
nothing. What a target that imports gob without calling it (go-craq's `store`) needs to prove its
own initialization (notes/craq-net.md).
-/
module

public import Perennial.Proof.io.Base
public import Perennial.Spec.io.initialize
public import Harness.GeneratedProof.encoding.gob

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace encoding.gob

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- gob's package-initialized state: nothing (no variable is allocated). -/
instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.encoding.gob :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.encoding.gob :=
  build_get_is_pkg_init_wf

end wps

end encoding.gob

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [encoding.gob.Assumptions]

/-- `encoding/gob`'s `initialize'`: `io`'s, then the trusted initializers (which do nothing). -/
abbrev encoding.gob.initialize'.spec : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp GF),
  GetIsPkgInitProp pkg_id.encoding.gob get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }}
      (App (Val encoding.gob.initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.encoding.gob }}

theorem encoding.gob.initialize'.wp_proof
    (wp_io_initialize : io.initialize'.spec (GF := GF) (hG := hG)) :
    encoding.gob.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_io_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Hio⟩
  repeat (first | wp_call | wp_auto)
  -- init.0, init.1, init.2: their trusted models do nothing
  repeat (first | wp_func_call | wp_call | wp_auto)
  iframe Hown
  is_pkg_init_finish

end spec

end Perennial
