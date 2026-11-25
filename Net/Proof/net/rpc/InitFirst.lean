/-
net/rpc's **first** initialization on a machine: its initializer, run when net/rpc is not yet
initialized, also returns the exclusive state it makes (`rpcFirstRes`): the codec registry at
`nil` (`codecUnset`, the half of `codec` that `SetCodec` takes) and `DefaultServer`'s registry,
empty, owned (`defaultServerO γ γf ∗ svcOwn γf ∅`: the right to register a fresh name, which
`Register.spec_fresh` takes). Proved from net/rpc's initializer, given `NewServer`'s spec with an
owned registry (`NewServer.spec_owned`, which the linking modules pass): `wp_init_first` (net/rpc
not initialized, `ownInitializing g` with `g pkg_id.net.rpc ⊢ False`; net/http's initializer, which
net/rpc's runs, by net/http's `wp_initialize'`) and `wp_init_first_http` (net/http not initialized
either: net/http's first initialization, `net.http.wp_init_first`, whose `muxOwn` it also returns,
on a machine of at most `2 ^ 30` threads). Both rest on `wp_init_core`, net/rpc's initializer with
net/http's run as a premise.
-/
module

public import Net.Proof.net.rpc.Init
public import Net.Proof.net.http.InitFirst
public import Net.Spec.net.rpc.NewServer
public import Net.Proof.go.token.Init
public import Proof.net.Init
public import Proof.bufio.Init
public import Proof.runtime.PkgInitFirst
public import Perennial.Proof.errors.NewVar
public import Perennial.Proof.io.Base
public import Perennial.Proof.log.Link
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section init
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions] [π : NetProtoGS]

/-- What net/rpc's first initialization returns besides its fact (see the file header). -/
def rpcFirstRes : IProp GF :=
  iprop(codecUnset ∗ ∃ γ γf : GName, defaultServerO γ γf ∗ svcOwn γf ∅)

/-- `internal/poll`'s `ErrDeadlineExceeded` holds some error, for good. -/
theorem errDeadlineExceeded_of_pkgInit : isPkgInit (PROP := IProp GF) pkg_id.internal.poll ⊢
    ∃ e : GoInterface, globalAddr internal.poll.ErrDeadlineExceeded ↦□ e := by
  refine (isPkgInit_access (PROP := IProp GF) pkg_id.internal.poll).trans ?_
  show iprop((∃ e : GoInterface, typedPointsto (globalAddr internal.poll.ErrNoDeadline) e DFrac.discard) ∗
    (∃ e : GoInterface, typedPointsto (globalAddr internal.poll.ErrDeadlineExceeded) e DFrac.discard) ∗
    (∃ x : Loc, typedPointsto (globalAddr internal.poll.ErrFileClosing)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard)) ⊢ _
  iintro ⟨-, He, -⟩
  iexact He

theorem io_isInit_of_pkgInit :
    isPkgInit (PROP := IProp GF) pkg_id.io ⊢ _root_.Perennial.io.isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.io

/-- net/rpc's initializer, run when net/rpc is not initialized (`hA`), with net/http's
initializer (which it runs after `go/token`'s and `sync`'s, and before its other imports') as a
premise (`Hhttp`, from the table `gB` to `gC`, returning `X`). -/
theorem wp_init_core (wp_NewServer : NewServer.spec_owned (GF := GF) (hG := hG))
    (gA gB gC : GoString → IProp GF) (X : IProp GF)
    (hA : gA pkg_id.net.rpc ⊢ iprop(False)) (hAB : ∀ p, gA p ⊢ gB p)
    (heq : gC pkg_id.net.rpc = isPkgInit (PROP := IProp GF) pkg_id.net.rpc)
    (Htoken : GetIsPkgInitProp pkg_id.go.token gB) (Hsync : GetIsPkgInitProp pkg_id.sync gB)
    (Hhttp : {{ ownInitializing gB }} (App (Val net.http.initialize') (Val #()))
      {{ RET #(); ownInitializing gC ∗ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ X }})
    (Hnet : GetIsPkgInitProp pkg_id.net gC) (Hlog : GetIsPkgInitProp pkg_id.log gC)
    (Hio : GetIsPkgInitProp pkg_id.io gC) (Herrors : GetIsPkgInitProp pkg_id.errors gC)
    (Hbufio : GetIsPkgInitProp pkg_id.bufio gC) :
    {{ ownInitializing gA }} (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing gC ∗ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗
        rpcFirstRes ∗ X }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_first (Q := iprop(rpcFirstRes ∗ X)) (hA := hA) (hAB := hAB)
    (heq := heq) $$ [Hown]
  · iframe Hown
    iintro Hown
    wp_auto
    wp_apply wp_GlobalAlloc (V := GoString) connected go.string as Hconn
    wp_apply wp_GlobalAlloc (V := Unit) invalidRequest (go.StructType []) as Hinv
    wp_apply wp_GlobalAlloc (V := Loc) DefaultServer _ as Hds
    wp_apply wp_GlobalAlloc (V := Bool) debugLog go.bool as Hdbg
    wp_apply wp_GlobalAlloc (V := GoInterface) errFrame go.error as HeF
    wp_apply wp_GlobalAlloc (V := Loc) codec _ as Hcodec
    wp_apply wp_GlobalAlloc (V := sync.Mutex) codecMu sync.Mutex.ty as HcMu
    wp_apply wp_GlobalAlloc (V := GoInterface) ErrShutdown go.error as HeS
    wp_apply go.token.wp_initialize' _ Htoken $$ Hown as ⟨Hown, #Htok⟩
    wp_apply sync.wp_initialize' _ Hsync $$ Hown as ⟨Hown, #Hsy⟩
    wp_apply Hhttp $$ Hown as ⟨Hown, #Hht, HX⟩
    wp_apply net.wp_initialize' _ Hnet $$ Hown as ⟨Hown, #Hnt⟩
    wp_apply log.wp_initialize' _ Hlog $$ Hown as ⟨Hown, #Hlg⟩
    wp_apply io.wp_initialize' _ Hio $$ Hown as ⟨Hown, #Hio⟩
    wp_apply errors.wp_initialize' _ Herrors $$ Hown as ⟨Hown, #Her⟩
    wp_apply bufio.wp_initialize' _ Hbufio $$ Hown as ⟨Hown, #Hbu⟩
    wp_apply errors.wp_New_errorString as %xS #ES
    ipersist HeS
    wp_apply errors.wp_New_errorString as %xF #EF
    ipersist HeF
    try wp_auto
    iapply wp_fupd
    wp_apply wp_NewServer as %s ⟨%γ, %γf, #Hsrv, Hsown⟩
    ipersist Hds
    ipersist Hinv
    ipersist Hconn
    ipersist Hdbg
    -- the codec registry: one half for the mutex, `codecUnset` the other
    icases (typedPointsto_half_split (globalAddr codec) (zero_val Loc) 1).1 $$ Hcodec with ⟨Hc1, Hc2⟩
    imod _root_.Perennial.sync.init_Mutex (codecInv (GF := GF)) ⊤ _ $$ HcMu [Hc1] with #HMu
    · inext
      iunfold codecInv
      iexists _
      iexact Hc1
    ihave #Hpoll : isPkgInit (PROP := IProp GF) pkg_id.internal.poll $$ []
    · solve_pkg_init
    ihave #Hpi := errDeadlineExceeded_of_pkgInit $$ Hpoll
    ihave #Hioi := io_isInit_of_pkgInit $$ Hio
    iNamed Hioi
    icases Hpi with ⟨%ed, #Hed⟩
    iunfold errors.newVar at HEOF HErrUnexpectedEOF
    icases HEOF with ⟨%xe, #Heof, -⟩
    icases HErrUnexpectedEOF with ⟨%xu, #Hueof, -⟩
    ihave #HdO : defaultServerO (GF := GF) γ γf $$ []
    · iunfold defaultServerO
      iexists s
      iframe Hds Hsrv
    imodintro
    isplitl [Hc2 Hsown HX]
    · iframe HX
      iunfold rpcFirstRes
      isplitl [Hc2]
      · iunfold codecUnset
        iexact Hc2
      iexists γ, γf
      iframe Hsown HdO
    isplitr
    · ipureintro; exact isPanic_intoVal ()
    iframe Hown
    is_pkg_init_finish
    imodintro
    iunfold rpcInit
    isplitr
    · iexists γ
      iapply defaultServerO_any $$ HdO
    isplitr
    · iunfold srvEnv
      isplitr
      · iunfold cliEnv
        iexists _, _, _
        iframe Hio Hsy Heof Hueof Hed Hdbg
        isplitr
        · iunfold errors.newVar
          iexists xF
          iframe HeF EF
        · iunfold errors.newVar
          iexists xS
          iframe HeS ES
      · iexact Hinv
    isplitr
    · unfold connectedStatus
      iexact Hconn
    · iexact HMu
  · iintro ⟨Hown, #Hpk, Hres, HX⟩
    iapply HΦ
    iframe Hown Hres HX
    iexact Hpk

/-- **net/rpc's first initialization** (see the file header): net/rpc not initialized (`hnot`); the
nested run of net/http's initializer by net/http's `wp_initialize'`. -/
theorem wp_init_first (wp_NewServer : NewServer.spec_owned (GF := GF) (hG := hG))
    (g g' : GoString → IProp GF)
    (hnot : g pkg_id.net.rpc ⊢ iprop(False))
    (Hinit : GetIsPkgInitProp pkg_id.net.rpc g')
    (hsame : ∀ p, p ≠ pkg_id.net.rpc → g' p = g p) :
    {{ ownInitializing g }} (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing g' ∗ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ rpcFirstRes }} := by
  have hAB : ∀ p, g p ⊢ g' p := fun p => by
    by_cases h : p = pkg_id.net.rpc
    · subst h; exact hnot.trans false_elim
    · rw [hsame p h]
  have Hhttp : {{ ownInitializing g' }} (App (Val net.http.initialize') (Val #()))
      {{ RET #(); ownInitializing g' ∗ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗
          iprop(True) }} := by
    iintro %Φ Hown HΦ
    iapply (net.http.wp_initialize' g' Hinit.2.2.2.2.2.2.1) $$ Hown
    iintro !> ⟨Hown, #Hht⟩
    iapply HΦ
    iframe Hown Hht
  iintro %Φ Hown HΦ
  iapply (wp_init_core wp_NewServer g g' g' iprop(True) hnot hAB Hinit.1 Hinit.2.2.2.2.2.2.2.2.1
    Hinit.2.2.2.2.2.2.2.1 Hhttp Hinit.2.2.2.2.2.1 Hinit.2.2.2.2.1 Hinit.2.2.2.1 Hinit.2.2.1
    Hinit.2.1) $$ Hown
  iintro !> ⟨Hown, #Hpk, Hres, -⟩
  iapply HΦ
  iframe Hown Hpk Hres

/-- **net/rpc's and net/http's first initializations** (see the file header): neither is
initialized (`hnot`, `hnoth`); on a machine of at most `2 ^ 30` threads (net/http's,
`net.http.wp_init_first`), it also returns net/http's fact and the right to register on
`DefaultServeMux`, no pattern registered. -/
theorem wp_init_first_http (wp_NewServer : NewServer.spec_owned (GF := GF) (hG := hG))
    (g g' : GoString → IProp GF)
    (hnot : g pkg_id.net.rpc ⊢ iprop(False)) (hnoth : g pkg_id.net.http ⊢ iprop(False))
    (Hinit : GetIsPkgInitProp pkg_id.net.rpc g')
    (hsame : ∀ p, p ≠ pkg_id.net.rpc → p ≠ pkg_id.net.http → g' p = g p) :
    {{ ownInitializing g ∗ ⌜threadBound GF ≤ 2 ^ 30⌝ }} (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing g' ∗ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ rpcFirstRes ∗
        isPkgInit (PROP := IProp GF) pkg_id.net.http ∗
        net.http.muxOwn (globalAddr net.http.defaultServeMux) [] }} := by
  let gB : GoString → IProp GF := fun p => if p = pkg_id.net.http then iprop(False) else g' p
  have hAB : ∀ p, g p ⊢ gB p := fun p => by
    by_cases h : p = pkg_id.net.http
    · subst h; exact hnoth.trans false_elim
    by_cases h' : p = pkg_id.net.rpc
    · subst h'; exact hnot.trans false_elim
    · simp only [gB, h, ↓reduceIte]; rw [hsame p h' h]
  have Htoken : GetIsPkgInitProp pkg_id.go.token gB := by
    have h := Hinit.2.2.2.2.2.2.2.2.1
    simp only [GetIsPkgInitProp, gB] at h ⊢
    revert h
    repeat dsimp only [GetIsPkgInitWf.get_is_pkg_init_prop_def, GetIsPkgInitProp]
    intro h
    simp (config := {decide := true}) only [ite_false, _root_.and_true] at h ⊢
    exact h
  have Hsync : GetIsPkgInitProp pkg_id.sync gB := by
    have h := Hinit.2.2.2.2.2.2.2.1
    simp only [GetIsPkgInitProp, gB] at h ⊢
    revert h
    repeat dsimp only [GetIsPkgInitWf.get_is_pkg_init_prop_def, GetIsPkgInitProp]
    intro h
    simp (config := {decide := true}) only [ite_false, _root_.and_true] at h ⊢
    exact h
  iintro %Φ ⟨Hown, %hT⟩ HΦ
  have Hhttp : {{ ownInitializing gB }} (App (Val net.http.initialize') (Val #()))
      {{ RET #(); ownInitializing g' ∗ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗
          iprop(isPkgInit (PROP := IProp GF) pkg_id.net.http ∗
            net.http.muxOwn (globalAddr net.http.defaultServeMux) []) }} := by
    iintro %Ψ Hown HΨ
    iapply (net.http.wp_init_first gB g' (by simp only [gB, ↓reduceIte]; exact .rfl)
      Hinit.2.2.2.2.2.2.1 (fun p hp => by simp only [gB, hp, ↓reduceIte])) $$ [Hown]
    · iframe Hown; ipureintro; exact hT
    iintro !> ⟨Hown, #Hht, Hmux⟩
    iapply HΨ
    iframe Hown Hht Hmux
  iapply (wp_init_core wp_NewServer g gB g' _ hnot hAB Hinit.1 Htoken Hsync Hhttp
    Hinit.2.2.2.2.2.1 Hinit.2.2.2.2.1 Hinit.2.2.2.1 Hinit.2.2.1 Hinit.2.1) $$ Hown
  iintro !> ⟨Hown, #Hpk, Hres, #Hht, Hmux⟩
  iapply HΦ
  iframe Hown Hpk Hres Hht Hmux

end init

end net.rpc
end Perennial
