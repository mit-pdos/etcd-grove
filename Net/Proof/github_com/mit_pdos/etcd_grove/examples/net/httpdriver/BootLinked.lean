/- Lean-first (no Rocq counterpart).

# `net/httpdriver`: a machine's first initialization

Both commands import `httpdriver` only, whose initializer runs, innermost first, `primitive`, `sync`,
`strconv`, net/http's (its first run on the machine, over the interim axiom `net.http.wp_init_first`:
its `use121` is `false` under the environment premise `GodebugHttpmuxgo121Not1`, and the server's
variables, `httpSrvEnv`, as `wp_init_first_mux` builds them), `net`, `io`, `bufio`; then allocates and
stores its variable (`drvFacts`). Here from a table in which the owned packages are not initialized yet
(`gOff ownedPkgs G`, `BootTable.lean`), as rpcdriver's boot. A linking module: it composes the
initializers' proofs.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.BootTable
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.PkgInitFirst
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.BootDefs
public import Net.Proof.net.http.InitFirst
public import Proof.bufio.Init
public import Proof.net.Init
public import Perennial.Proof.sync.Link
public import Perennial.Proof.strconv.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.github_com.goose_lang.primitive.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.github_com.mit_pdos.etcd_grove.examples.net.httpdriver

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.mit_pdos.etcd_grove.examples.net.rpcdriver (wp_package_init_first)

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : Assumptions] [net.FieldAssumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- A machine's empty package state is `ownInitializing` of any table. -/
theorem ownInitializing_of_empty (g : GoString → IProp GF) :
    ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ ⊢ ownInitializing g := by
  rw [ownInitializing_unseal]
  unfold ownInitializingDef
  iintro Hg
  iexists ∅
  iframe Hg
  iintro !>
  iapply BigSepM.bigSepM_empty.2
  iempintro

theorem httpLe : ∀ q ∈ [pkg_id.net.http], q ∈ ownedPkgs := by decide

variable {G : GoString → IProp GF} (hk : KitG G) (HEnv : net.http.GodebugHttpmuxgo121Not1)
include hk HEnv

set_option goose.wp.extras true

/-- **`httpdriver`'s first initialization** (see the file header). -/
theorem boot_httpdriver :
    {{ ownInitializing (gOff ownedPkgs G) }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing G ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.httpdriver ∗
        bootRes }} := by
  wp_start as Hown
  iapply wp_package_init_first (pkg_id.github_com.mit_pdos.etcd_grove.examples.net.httpdriver)
    (gA := gOff ownedPkgs G) (gB := gOff [pkg_id.net.http] G) (gC := G)
    (hA := gOff_off _ _ _ (by decide)) (hAB := gOff_sub _ _ _ (by decide))
    (heq := hk.e_github_com_mit_pdos_etcd_grove_examples_net_httpdriver) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  iapply wp_fupd
  try wp_auto
  wp_apply wp_GlobalAlloc (V := _) reached _ as Hreached
  wp_apply github_com.goose_lang.primitive.wp_initialize' _
    (wfO_github_com_goose_lang_primitive hk _ httpLe) $$ Hown as ⟨Hown, #H1⟩
  wp_apply sync.wp_initialize' _ (wfO_sync hk _ httpLe) $$ Hown as ⟨Hown, #H2⟩
  wp_apply strconv.wp_initialize' _ (wfO_strconv hk _ httpLe) $$ Hown as ⟨Hown, #H3⟩
  wp_apply (net.http.wp_init_first (gOff [pkg_id.net.http] G) G (gOff_off _ _ _ (by decide))
      (wf_net_http hk) (fun p hp => (gOff_ne _ _ _ (by simp [hp])).symm)) $$ Hown
    as ⟨Hown, #Hpkg, Hres⟩
  iunfold net.http.initFirstRes at Hres
  icases Hres with ⟨-, ⟨%b, #Hu, %Hb⟩, #Hms, #Hse, #Hck, #Htm, #Hwp, #Hrp⟩
  have hb : b = false := by
    cases b
    · rfl
    · exact absurd (Hb rfl) HEnv
  subst hb
  wp_apply net.wp_initialize' _ (wf_net hk) $$ Hown as ⟨Hown, #H5⟩
  wp_apply io.wp_initialize' _ (wf_io hk) $$ Hown as ⟨Hown, #H6⟩
  wp_apply bufio.wp_initialize' _ (wf_bufio hk) $$ Hown as ⟨Hown, #H7⟩
  try wp_auto
  imod (typedPointsto_dfractional _ _).dfractional_persist $$ Hreached with #Hreached
  imodintro
  iframe Hown
  isplitl []
  · iunfold bootRes
    iframe Hu
    isplitr
    · iexists _; iexact Hms
    isplitr
    · iunfold net.http.httpSrvEnv
      iframe #
      isplitl []
      · iapply net.http.httpEnv_access $$ Hpkg
      iapply net.http.readEnv_of_init $$ Hpkg
    iunfold drvFacts
    iexists _
    iframe Hreached
    imodintro
    iintro %s
    wp_auto
    ipureintro; rfl
  isplitr
  · ipureintro; exact isPanic_intoVal ()
  is_pkg_init_finish

end boot

end Perennial.github_com.mit_pdos.etcd_grove.examples.net.httpdriver
