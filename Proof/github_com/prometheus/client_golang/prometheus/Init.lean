/-
Package initialization of `github_com.prometheus.client_golang.prometheus`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`promInit γ`, `PkgInit.lean`, at the run's registry ghost name `γ`, the parameter
`PromRegGS` of the package's fact; route (b), Option 4, 2026-11-22, notes/prom-registry.md): `defaultRegistry`
and `DefaultRegisterer` hold the default registry, read-only, a registry over `γ` (`isRegistry`). Its
initializer initializes its imports and runs its translated variable initializers (the others are goose
`[[skip]]` entries, mit-pdos/etcd-grove#23): `defaultRegistry = NewRegistry()` (stepped into) and `DefaultRegisterer`/`DefaultGatherer`,
`defaultRegistry` converted to an interface; then its `init()`, whose trusted model inserts the built-in
collectors' descriptor IDs, names and collector IDs into the registry's maps
(`EtcdGrove.prometheus.wp_seed_insertAll`); the registry's lock is then made the guard of its invariant
(`EtcdGrove.prometheus.isRegistry_init`: the built-ins need no right). (Until 2026-11-22 its fact was `True`;
until step 1 of route (b) `defaultRegistry.init`, `DefaultRegisterer.init` and `DefaultGatherer.init` were
among `opaqueInitsOk`, and `init.«0»` was the trust-boundary axiom `initFuncsOk`.)
-/
module

public import Proof.github_com.prometheus.client_golang.prometheus.PkgInit
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.math.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Proof.github_com.prometheus.client_model.go''.Init
public import Proof.github_com.prometheus.client_golang.prometheus.Seed
public import Proof.runtime.PkgInitExt

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.github_com.prometheus.client_golang.prometheus.Assumptions]
variable [promreg_gs : EtcdGrove.prometheus.PromRegGS GF]

namespace github_com.prometheus.client_golang.prometheus

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.prometheus.client_golang.prometheus get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoInterface) DefaultGatherer _ as HDefaultGatherer
  wp_apply wp_GlobalAlloc (V := GoInterface) DefaultRegisterer _ as HDefaultRegisterer
  wp_apply wp_GlobalAlloc (V := Loc) defaultRegistry _ as HdefaultRegistry
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (_root_.Perennial.github_com.prometheus.client_model.go''.wp_initialize'_lb _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync.atomic _root_.Perennial.sync.atomic.initialize'
      EtcdGrove.ExternalInit.sync_atomic _root_.Perennial.sync.atomic.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.math _root_.Perennial.math.initialize'
      EtcdGrove.ExternalInit.math _root_.Perennial.math.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of defaultRegistry))
  try wp_auto
  wp_func_call
  wp_call
  try wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := GoInterface) go.uint64 github_com.prometheus.client_golang.prometheus.Collector.ty) as %mC HmC
  try wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Unit) go.uint64 (go.GoType.StructType [])) as %mD HmD
  try wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := w64) go.string go.uint64) as %mN HmN
  try wp_auto
  -- translated initializer of DefaultRegisterer))
  -- translated initializer of DefaultGatherer))
  -- the translated init.«0»
  wp_func_call
  wp_call
  try wp_auto
  simp only [EtcdGrove.prometheus.seed_Registry_eq, EtcdGrove.prometheus.seed_Collector_eq, EtcdGrove.prometheus.seed_defaultRegistry_eq]
  try wp_auto
  wp_apply (EtcdGrove.prometheus.wp_seed_insertAll (K := w64) (V := Unit) go.uint64 (fun id => (id, ())) github_com.prometheus.client_golang.prometheus.seed.descIDs) $$ HmD as HmD
  try wp_auto
  wp_apply (EtcdGrove.prometheus.wp_seed_insertAll (K := GoString) (V := w64) go.string (fun nd => nd) github_com.prometheus.client_golang.prometheus.seed.dims) $$ HmN as HmN
  try wp_auto
  wp_apply (EtcdGrove.prometheus.wp_seed_insertAll (K := w64) (V := GoInterface) go.uint64 (fun id => (id, (interface.nil : GoInterface))) github_com.prometheus.client_golang.prometheus.seed.collectorIDs) $$ HmC as HmC
  try wp_auto
  -- the registry: its fields, and its lock the guard of its invariant (`isRegistry`)
  irename «$r0» => Hreg0
  iStructNamed Hreg0
  imod (EtcdGrove.prometheus.isRegistry_init (GF := GF) (EtcdGrove.prometheus.PromRegGS.γ (GF := GF)) _ mC mD mN _ _ _ EtcdGrove.prometheus.seed_C_builtin EtcdGrove.prometheus.seed_D_builtin EtcdGrove.prometheus.seed_N_builtin) $$ mtx collectorsByID descIDs dimHashesByName HmC HmD HmN with #Hreg
  ipersist HdefaultRegistry
  ipersist HDefaultRegisterer
  -- translated initializer of defaultRegistry))
  -- translated initializer of defaultRegistry))
  ihave #Hfact : (github_com.prometheus.client_golang.prometheus.promInit (EtcdGrove.prometheus.PromRegGS.γ (GF := GF)) : IProp GF) $$ []
  · iunfold github_com.prometheus.client_golang.prometheus.promInit
    iexists _
    iframe #
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.prometheus.client_golang.prometheus get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end github_com.prometheus.client_golang.prometheus

end init

end Perennial
