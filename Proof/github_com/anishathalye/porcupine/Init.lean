/- Lean-first (no Rocq counterpart).

# Porcupine's package initialization, with `context`'s `isClosedchanInit` (2026-10-19)

Porcupine's specs (`CheckOperations*`) take `context.isClosedchanInit` (`closedchan` is
closed, an invariant: `WithCancel(Background())` needs it), which `context`'s `isPkgInit` does
not give and Perennial's `context.wp_initialize'` does not return: its proof closes
`closedchan` and drops the channel's state. A closed program built on porcupine must get it
from its initialization, so this file proves the initialization again with it:

- `context_wp_initialize'_closedchan`: `context`'s initialization (the proof of Perennial's
  `context.initialize'.wp_proof`, plus the invariant `inv closedchanN (ownChan γ (Closed []))`
  allocated once `init` has closed the channel) at a `get_is_pkg_init` whose entry for
  `context` is `isPkgInit context ∗ isClosedchanInit`; it returns both.
- `wp_initialize'`: porcupine's (which runs `context`'s first), at a table
  (`PorcupineInitTable`) whose entries for `context` and porcupine carry `isClosedchanInit`
  (so a second initialization, from the map, gives it too) and whose entries for the other
  packages it reaches (`errors`, `sync`, `sync/atomic`, `time`, `sort`, `fmt`, `strings`,
  which do not import `context`) are their `isPkgInit` (`GetIsPkgInitProp`).

The clean fix is in Perennial: `context`'s `isPkgInit` could include `isClosedchanInit`
(its `isInit` is stated at any `HasLC`, `isClosedchanInit` at `HasLC.hasLC`), and then no
spec would take it as a premise.
-/
module

public import Proof.github_com.anishathalye.porcupine.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.context.NewErrorString
public import Perennial.Proof.sort.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.time.Link
public import Proof.runtime.PkgInitExt

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section ctx
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

open context in
/-- `context`'s initialization, returning `isClosedchanInit` (see the file header). -/
theorem context_wp_initialize'_closedchan [hErr : ErrorStringIsError]
    [hDE : DeadlineExceededIsError] (get_is_pkg_init : GoString → IProp GF)
    (Hctx : get_is_pkg_init pkg_id.context =
      iprop(isPkgInit (PROP := IProp GF) pkg_id.context ∗ isClosedchanInit))
    (Herr : GetIsPkgInitProp pkg_id.errors get_is_pkg_init)
    (Hsync : GetIsPkgInitProp pkg_id.sync get_is_pkg_init)
    (Hatomic : GetIsPkgInitProp pkg_id.sync.atomic get_is_pkg_init)
    (Htime : GetIsPkgInitProp pkg_id.time get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        (isPkgInit (PROP := IProp GF) pkg_id.context ∗ isClosedchanInit) }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hctx) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoChan) closedchan _ as Hcl
  wp_apply wp_GlobalAlloc (V := w64) cancelCtxKey go.int as _
  wp_apply wp_GlobalAlloc (V := sync.atomic.Int32) goroutines sync.atomic.Int32.ty as Hgo
  wp_apply wp_GlobalAlloc (V := GoInterface) DeadlineExceeded go.error as HDE
  wp_apply wp_GlobalAlloc (V := GoInterface) Canceled go.error as HC
  wp_apply time.wp_initialize' _ Htime $$ Hown as ⟨Hown, #H1⟩
  wp_apply sync.atomic.wp_initialize' _ Hatomic $$ Hown as ⟨Hown, #H2⟩
  wp_apply sync.wp_initialize' _ Hsync $$ Hown as ⟨Hown, #H3⟩
  wp_apply errors.wp_initialize' _ Herr $$ Hown as ⟨Hown, #H4⟩
  wp_apply wp_New_errorString as %x _
  wp_apply chan.wp_make1 (V := Unit) as %ch %γ ⟨#His_ch, %Hcap, Hch⟩
  ipersist HC
  ipersist HDE
  ipersist Hcl
  ihave Hgo : sync.atomic.ownInt32 (globalAddr goroutines) (DFrac.own 1) (W32 0) $$ [Hgo]
  · rw [sync.atomic.ownInt32_unseal]
    unfold sync.atomic.ownInt32Def
    rw [show ({ _0' := zero_val _, v' := W32 0 } : sync.atomic.Int32) =
      zero_val sync.atomic.Int32 from rfl]
    iexact Hgo
  imod inv_alloc nroot ⊤ iprop(∃ g, sync.atomic.ownInt32 (globalAddr context.goroutines)
    (DFrac.own 1) g) $$ [Hgo] with #Hginv
  · inext
    iexists _
    iexact Hgo
  -- context's init.0 (`closedchan` closed)
  wp_func_call
  wp_call
  wp_auto
  wp_apply_core chan.wp_close (V := Unit) ch γ $$ His_ch
  iintro -
  unfold closeAu
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists .Idle
  iframe Hch
  dsimp only
  iintro Hch
  imod Hmask with -
  imod inv_alloc closedchanN ⊤ (ownChan γ Unit (.Closed [])) $$ [Hch] with #Hccinv
  · inext
    iexact Hch
  imodintro
  wp_auto
  iframe Hown
  imodintro
  isplitl
  · isPkgInit_unfold
    iframe #
    isplitr
    · iexact Hginv
    isplitr
    · iexists ch
      iexact Hcl
    isplitr
    · iexists _
      iframe HC
      ipureintro
      exact hErr.is_error
    isplitr
    · iexists _
      iframe HDE
      ipureintro
      exact hDE.is_error
    itrivial
  · unfold isClosedchanInit
    iexists ch, γ
    iframe #

end ctx

namespace github_com.anishathalye.porcupine

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- What porcupine's initialization needs of `get_is_pkg_init` (see the file header):
`context`'s and porcupine's entries carry `isClosedchanInit`, the other packages' are their
`isPkgInit`. -/
structure PorcupineInitTable (get_is_pkg_init : GoString → IProp GF) : Prop where
  self : get_is_pkg_init pkg_id.github_com.anishathalye.porcupine =
    iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗
      context.isClosedchanInit)
  context : get_is_pkg_init pkg_id.context =
    iprop(isPkgInit (PROP := IProp GF) pkg_id.context ∗ context.isClosedchanInit)
  errors : GetIsPkgInitProp pkg_id.errors get_is_pkg_init
  sync : GetIsPkgInitProp pkg_id.sync get_is_pkg_init
  atomic : GetIsPkgInitProp pkg_id.sync.atomic get_is_pkg_init
  time : GetIsPkgInitProp pkg_id.time get_is_pkg_init
  sort : GetIsPkgInitProp pkg_id.sort get_is_pkg_init
  fmt : GetIsPkgInitProp pkg_id.fmt get_is_pkg_init
  strings : GetIsPkgInitProp pkg_id.strings get_is_pkg_init

/-- Porcupine's initialization, returning `context`'s `isClosedchanInit` (see the file
header). -/
theorem wp_initialize' [context.ErrorStringIsError] [context.DeadlineExceededIsError]
    (get_is_pkg_init : GoString → IProp GF) (Ht : PorcupineInitTable get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        (isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗
          context.isClosedchanInit) }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Ht.self) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply strings.wp_initialize' _ Ht.strings $$ Hown as ⟨Hown, #H5⟩
  wp_apply fmt.wp_initialize' _ Ht.fmt $$ Hown as ⟨Hown, #H4⟩
  wp_apply time.wp_initialize' _ Ht.time $$ Hown as ⟨Hown, #H3⟩
  wp_apply sort.wp_initialize' _ Ht.sort $$ Hown as ⟨Hown, #H2⟩
  wp_apply context_wp_initialize'_closedchan _ Ht.context Ht.errors Ht.sync Ht.atomic Ht.time
    $$ Hown as ⟨Hown, #H1, #Hcc⟩
  iframe Hown
  imodintro
  iframe #
  is_pkg_init_finish

end init

end github_com.anishathalye.porcupine

/-! The ordinary form (decision D19e), for a package of the ordinary form importing this one, at
a table of its closure's `isPkgInit`s (see `CLOSEDCHAN` in `etc/gen-init.py`). -/
section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.github_com.anishathalye.porcupine.Assumptions]
variable [_root_.Perennial.context.ErrorStringIsError]
  [_root_.Perennial.context.DeadlineExceededIsError]

namespace github_com.anishathalye.porcupine

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.anishathalye.porcupine get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strings _root_.Perennial.strings.initialize'
      EtcdGrove.ExternalInit.strings _root_.Perennial.strings.wp_initialize' _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sort _root_.Perennial.sort.initialize'
      EtcdGrove.ExternalInit.sort _root_.Perennial.sort.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  iframe Hown
  is_pkg_init_finish

end github_com.anishathalye.porcupine

end init

end Perennial
