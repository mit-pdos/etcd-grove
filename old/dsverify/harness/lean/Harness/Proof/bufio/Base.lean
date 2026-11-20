/-
Go's `bufio` (Go 1.27.3, real code translated by goose into `Harness/Code/bufio.lean`,
`Code/bufio.toml`): its package-initialized state and the proof of its `initialize'`.

**`isPkgInit pkg_id.bufio`** (`isInit`, persistent): each error variable made by `errors.New`
holds its error (`errors.newVar`), as for Perennial's `io`. `errorRune` is not part of it (its
initializer is trusted to do nothing, `TrustedCode/bufio.lean`). `isPkgInit pkg_id.bufio` gives
`isPkgInit pkg_id.io` (`io_init_of_bufio`): `fill` sets `io.ErrNoProgress`.
-/
module

public import Harness.GeneratedProof.bufio
public import Perennial.Proof.io
public import Perennial.Spec.errors.initialize
public import Perennial.Spec.io.initialize
public import Perennial.Proof.errors.NewVar

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace bufio

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The package-initialized state of `bufio` (persistent); see the file header. -/
abbrev isInit : IProp GF :=
  iprop("#HErrInvalidUnreadByte" ∷
      errors.newVar ErrInvalidUnreadByte go!"bufio: invalid use of UnreadByte" ∗
    "#HErrInvalidUnreadRune" ∷
      errors.newVar ErrInvalidUnreadRune go!"bufio: invalid use of UnreadRune" ∗
    "#HErrBufferFull" ∷ errors.newVar ErrBufferFull go!"bufio: buffer full" ∗
    "#HErrNegativeCount" ∷ errors.newVar ErrNegativeCount go!"bufio: negative count" ∗
    "#HerrNegativeRead" ∷
      errors.newVar errNegativeRead go!"bufio: reader returned negative count from Read" ∗
    "#HerrNegativeWrite" ∷
      errors.newVar errNegativeWrite go!"bufio: writer returned negative count from Write" ∗
    "#HErrTooLong" ∷ errors.newVar ErrTooLong go!"bufio.Scanner: token too long" ∗
    "#HErrNegativeAdvance" ∷
      errors.newVar ErrNegativeAdvance go!"bufio.Scanner: SplitFunc returns negative advance count" ∗
    "#HErrAdvanceTooFar" ∷
      errors.newVar ErrAdvanceTooFar go!"bufio.Scanner: SplitFunc returns advance count beyond input" ∗
    "#HErrBadReadCount" ∷
      errors.newVar ErrBadReadCount go!"bufio.Scanner: Read returned impossible count" ∗
    "#HErrFinalToken" ∷ errors.newVar ErrFinalToken go!"final token" ∗
    "_" ∷ True)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.bufio :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.bufio :=
  build_get_is_pkg_init_wf

theorem isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.bufio ⊢ isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.bufio

theorem io_init_of_bufio :
    isPkgInit (PROP := IProp GF) pkg_id.bufio ⊢ isPkgInit (PROP := IProp GF) pkg_id.io := by
  refine (isPkgInit_unfold_deps (PROP := IProp GF) pkg_id.bufio).trans ?_
  show iprop(isPkgInit pkg_id.errors ∗ isPkgInit pkg_id.io ∗ True) ⊢ _
  iintro ⟨-, H, -⟩
  iexact H

end init

end bufio

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [bufio.Assumptions]

/-- `bufio`'s package initializer: from `ownInitializing`, it returns with
`isPkgInit pkg_id.bufio` (after initializing `io` and `errors`). -/
abbrev bufio.initialize'.spec : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp GF),
  GetIsPkgInitProp pkg_id.bufio get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }}
      (App (Val bufio.initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [bufio.Assumptions]

theorem bufio.initialize'.wp_proof
    (wp_io_initialize : io.initialize'.spec (GF := GF) (hG := hG))
    (wp_errors_initialize : errors.initialize'.spec (GF := GF) (hG := hG)) :
    bufio.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoInterface) bufio.ErrFinalToken go.error as H11
  wp_apply wp_GlobalAlloc (V := GoInterface) bufio.ErrBadReadCount go.error as H10
  wp_apply wp_GlobalAlloc (V := GoInterface) bufio.ErrAdvanceTooFar go.error as H9
  wp_apply wp_GlobalAlloc (V := GoInterface) bufio.ErrNegativeAdvance go.error as H8
  wp_apply wp_GlobalAlloc (V := GoInterface) bufio.ErrTooLong go.error as H7
  wp_apply wp_GlobalAlloc (V := GoInterface) bufio.errNegativeWrite go.error as H6
  wp_apply wp_GlobalAlloc (V := GoInterface) bufio.errNegativeRead go.error as H5
  wp_apply wp_GlobalAlloc (V := GoInterface) bufio.ErrNegativeCount go.error as H4
  wp_apply wp_GlobalAlloc (V := GoInterface) bufio.ErrBufferFull go.error as H3
  wp_apply wp_GlobalAlloc (V := GoInterface) bufio.ErrInvalidUnreadRune go.error as H2
  wp_apply wp_GlobalAlloc (V := GoInterface) bufio.ErrInvalidUnreadByte go.error as H1
  wp_apply wp_io_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hio⟩
  wp_apply wp_errors_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Herrors⟩
  wp_apply errors.wp_New_errorString as %x1 #E1
  ipersist H1
  wp_apply errors.wp_New_errorString as %x2 #E2
  ipersist H2
  wp_apply errors.wp_New_errorString as %x3 #E3
  ipersist H3
  wp_apply errors.wp_New_errorString as %x4 #E4
  ipersist H4
  wp_apply errors.wp_New_errorString as %x5 #E5
  ipersist H5
  wp_apply errors.wp_New_errorString as %x6 #E6
  ipersist H6
  wp_apply errors.wp_New_errorString as %x7 #E7
  ipersist H7
  wp_apply errors.wp_New_errorString as %x8 #E8
  ipersist H8
  wp_apply errors.wp_New_errorString as %x9 #E9
  ipersist H9
  wp_apply errors.wp_New_errorString as %x10 #E10
  ipersist H10
  iapply wp_fupd
  wp_apply errors.wp_New_errorString as %x11 #E11
  ipersist H11
  unfold bufio.errorRune.init
  wp_auto
  imodintro
  isplitr
  · ipureintro; exact isPanic_intoVal ()
  iframe Hown
  is_pkg_init_finish
  imodintro
  unfold bufio.isInit errors.newVar
  isplitl; · iexists x1; iframe H1 E1
  isplitl; · iexists x2; iframe H2 E2
  isplitl; · iexists x3; iframe H3 E3
  isplitl; · iexists x4; iframe H4 E4
  isplitl; · iexists x5; iframe H5 E5
  isplitl; · iexists x6; iframe H6 E6
  isplitl; · iexists x7; iframe H7 E7
  isplitl; · iexists x8; iframe H8 E8
  isplitl; · iexists x9; iframe H9 E9
  isplitl; · iexists x10; iframe H10 E10
  isplitl; · iexists x11; iframe H11 E11
  itrivial

end proof

end Perennial
