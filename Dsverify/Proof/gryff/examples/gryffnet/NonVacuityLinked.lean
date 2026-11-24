/-
**Test only** (the NON-VACUITY rule; dsv-gryff, 2026-11-24): the hypothesis-class premises of
`gryff_remote_robust.spec` (`Dsverify/Spec/gryff/examples/gryffnet/TopLevelRobustness.lean`) that
have an instance built **without a new axiom**, as `theorem`s (no `instance` of an `InitHyp`
anywhere):
* `math.rand.InitHyp`: the main tree's walk (`Proof/math/rand/Init.lean`, over Perennial's
  `sync`/`sync/atomic` initializers) restated on `Net/`'s `PkgInitExt`. (Not discharged in the
  statement: the shared class `Dsverify/Proof/math/rand/Init.lean` is being replaced by
  math-rand-isinit, which makes `math/rand` Perennial's; gryff drops the premise when that lands.)
* `lib.MathPowHyp`: the main tree's interim axiom `EtcdGrove.math.Pow.wp_proof` (an existing axiom
  of the trust base, not a new one).
(`netN.StringsIndexHyp` is no longer a premise: its instance `stringsIndexHyp_holds`, over Perennial's
`strings.Index` since `fce59af75`, moved to `StrIndexHolds.lean` and discharges it in the proof.)
The other classes have no axiom-free instance at the pin b3f2fc485 (notes/dsv-gryff.md, "Session
11"): `net.rpc.InitHyp`/`net.http.InitHyp` (their closure reaches names-only initializers),
`replica2.SortSliceHyp`, `lib.RandSeedHyp` (`sort.Slice`, `math/rand.Seed` names only), `RpcHttpHyp` (net/http's server, `rpc.HandleHTTP`: not in Net),
`RpcBootHyp` (net/rpc's and net/http's owned initializations). The ninth agent's instances of
those over local axioms are in history (a5f91c8e46). No statement or proof imports this module.
-/
module

public import Dsverify.Spec.gryff.examples.gryffnet.TopLevelRobustness
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Proof.math.Pow
public import Proof.runtime.PkgInitExt

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace gryff.examples.gryffnet.instances

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Perennial.gryff Perennial.net.rpc

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ### `math.rand.InitHyp`: the main tree's walk, on `Net/`'s `PkgInitExt` -/

section mrand
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [_root_.Perennial.math.rand.Assumptions]

theorem mrand_wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.math.rand get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val math.rand.initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.math.rand }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := _) math.rand.globalRandGenerator _ as HglobalRandGenerator
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync.atomic _root_.Perennial.sync.atomic.initialize'
      EtcdGrove.ExternalInit.sync_atomic _root_.Perennial.sync.atomic.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  iframe Hown
  is_pkg_init_finish

theorem mrand_initHyp_holds : math.rand.InitHyp GF :=
  ⟨fun g Hinit => EtcdGrove.wp_init_of_lb _ _ _ (mrand_wp_initialize'_lb g Hinit)⟩

end mrand

/-! ### `lib.MathPowHyp`: the main tree's `math.Pow` -/

section libs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

theorem mathPow_holds : lib.MathPowHyp GF := ⟨EtcdGrove.math.Pow.wp_proof⟩

end libs

/-! ### At the statement's heaps -/

section statement
open github_com.mit_pdos.etcd_grove.examples.lib.remote.counter (remoteGF)
attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
variable [GoGlobalContext] [lctx : GoLocalContext] [go.Semantics]
variable [cmd.server1.Assumptions]
variable [net.FieldAssumptions] [go.BasicIntoValInj] [net.rpc.Assumptions]

/-- **The non-vacuity instances** (the NON-VACUITY rule) of the classes that have one without a new
axiom (the file header), in the statement's own form (at `remoteGF` and every machine's heap). -/
theorem nonvacuous_premises :
    (∀ G L, letI := heapAt G L; math.rand.InitHyp remoteGF) ∧
    (∀ G L, letI := heapAt G L; lib.MathPowHyp remoteGF) :=
  ⟨fun G L => mrand_initHyp_holds (hG := heapAt G L), fun G L => mathPow_holds (hG := heapAt G L)⟩

end statement

end gryff.examples.gryffnet.instances
end Perennial
