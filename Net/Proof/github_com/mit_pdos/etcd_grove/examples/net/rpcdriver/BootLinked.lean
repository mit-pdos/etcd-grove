/- Lean-first (no Rocq counterpart).

# `net/rpcdriver`: a machine's first initialization

Both commands import `rpcdriver` only, whose initializer runs, innermost first, `primitive`, `sync`,
`strings`, net/http's (its first run on the machine: `muxOwn (globalAddr net.http.defaultServeMux) []`, `net.http.wp_init_first`, an
interim axiom), `net`, net/rpc's (its first run: `codecUnset` and `DefaultServer`'s owned registry,
`net.rpc.wp_init_first`, an interim axiom), `service`, `errors`; then allocates and stores its
variables (`drvFacts`). Here from a table in which the owned packages are not initialized yet
(`gOff ownedPkgs G`, `BootTable.lean`), as the dsverify kits' boots (`BootLinked.lean`). A linking
module: it composes the initializers' proofs.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.BootTable
public import Proof.runtime.PkgInitFirst
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.BootDefs
public import Net.Proof.net.rpc.InitFirst
public import Net.Proof.net.rpc.Results
public import Net.Proof.net.http.InitFirst
public import Perennial.Proof.sync.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.github_com.goose_lang.primitive.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net EtcdGrove

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

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

theorem rpcLe : ∀ q ∈ [pkg_id.net.rpc], q ∈ ownedPkgs := by decide
theorem rpcHttpLe : ∀ q ∈ [pkg_id.net.rpc, pkg_id.net.http], q ∈ ownedPkgs := by decide

variable {G : GoString → IProp GF} (hk : KitG G) (hT : threadBound GF ≤ 2 ^ 30)
include hk hT

set_option goose.wp.extras true

/-- **`rpcdriver`'s first initialization** (see the file header). -/
theorem boot_rpcdriver :
    {{ ownInitializing (gOff ownedPkgs G) }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing G ∗ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver ∗
        bootRes }} := by
  wp_start as Hown
  iapply wp_package_init_first (pkg_id.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver)
    (gA := gOff ownedPkgs G) (gB := gOff [pkg_id.net.rpc, pkg_id.net.http] G) (gC := G)
    (hA := gOff_off _ _ _ (by decide)) (hAB := gOff_sub _ _ _ (by decide))
    (heq := hk.e_github_com_mit_pdos_etcd_grove_examples_net_rpcdriver) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  iapply wp_fupd
  try wp_auto
  wp_apply wp_GlobalAlloc (V := _) failMsgs _ as HfailMsgs
  wp_apply wp_GlobalAlloc (V := _) reached _ as Hreached
  wp_apply github_com.goose_lang.primitive.wp_initialize' _
    (wfO_github_com_goose_lang_primitive hk _ rpcHttpLe) $$ Hown as ⟨Hown, #H1⟩
  wp_apply sync.wp_initialize' _ (wfO_sync hk _ rpcHttpLe) $$ Hown as ⟨Hown, #H2⟩
  wp_apply strings.wp_initialize' _ (wfO_strings hk _ rpcHttpLe) $$ Hown as ⟨Hown, #H3⟩
  wp_apply (net.http.wp_init_first (gOff [pkg_id.net.rpc, pkg_id.net.http] G)
      (gOff [pkg_id.net.rpc] G) (gOff_off _ _ _ (by decide))
      (wfX_net_http hk _ rpcLe (by decide))
      (fun p hp => by unfold gOff; by_cases h : p = pkg_id.net.rpc <;> simp [h, hp])) $$ [$Hown]
    as ⟨Hown, #H4, Hmux⟩
  · ipureintro; exact hT
  wp_apply net.wp_initialize' _ (wfO_net hk _ rpcLe) $$ Hown as ⟨Hown, #H5⟩
  wp_apply (net.rpc.wp_init_first net.rpc.NewServer.wp_owned (gOff [pkg_id.net.rpc] G) G (gOff_off _ _ _ (by decide))
      (wf_net_rpc hk) (fun p hp => (gOff_ne _ _ _ (by simp [hp])).symm)) $$ Hown
    as ⟨Hown, #H6, Hrf⟩
  wp_apply service.wp_initialize' _ (wf_github_com_mit_pdos_etcd_grove_examples_net_rpcdriver_service hk)
    $$ Hown as ⟨Hown, #H7⟩
  wp_apply errors.wp_initialize' _ (wf_errors hk) $$ Hown as ⟨Hown, #H8⟩
  try wp_auto
  wp_apply (wp_slice_literal (l := failList))
  isplitr
  · ipureintro; rfl
  iintro %sf ⟨Hsf, -⟩
  try wp_auto
  imod (typedPointsto_dfractional _ _).dfractional_persist $$ HfailMsgs with #HfailMsgs
  imod (typedPointsto_dfractional _ _).dfractional_persist $$ Hreached with #Hreached
  imod ownSlice_persist $$ Hsf with #Hsf
  imodintro
  iframe Hown
  isplitl [Hmux Hrf]
  · iunfold bootRes
    iframe Hmux Hrf
    iunfold drvFacts
    isplitr
    · iexists _; iframe HfailMsgs Hsf
    · iexists _
      iframe Hreached
      imodintro
      iintro %s
      wp_auto
      ipureintro; rfl
  isplitr
  · ipureintro; exact isPanic_intoVal ()
  is_pkg_init_finish

end boot

end Perennial.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
