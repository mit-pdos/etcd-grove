/-
net/http's **first** initialization on a machine: its initializer, run when net/http is not yet
initialized, also returns what it leaves (`wp_init_first`, an interim trust-boundary axiom): the zero
`defaultServeMux` (owned, the one exclusive part: the right to register is made from it), and
persistent facts about package variables it sets once and nothing writes again. Its shape is the
swiftpaxos kit's `RpcFirstInit` (`ownInitializing g`; `g pkg_id.net.http ⊢ False`: net/http not
initialized, so this runs once per machine), for net/http alone. Reviewed:
`/shared/tmp/ps2/revinit/review.md` (2026-11-25, sound; `notes/axiom-review/net-http-interim.md`).

Each conjunct, from the line that sets it in the model's Go source `models/net/http` (go1.27.3's
`net/http` has the same initializers):

* `defaultServeMux` (`server.go:2613`, `var defaultServeMux ServeMux`, no initializer): the zero
  `ServeMux`, owned. Safe only while no other trusted spec writes the mux: a package whose
  initializer registers on `DefaultServeMux` (expvar, net/http/pprof, x/net/trace) needs a first-init
  spec that consumes it; a standard-shape `wp_initialize'` axiom for one would contradict this one.
* `use121` (`servemux121.go:27`, `var use121 bool`; set to `true` only by `init`, `servemux121.go:31-36`,
  the approved model `Net/TrustedCode/net/http.lean`): some boolean, `true` only if the run's
  `httpmuxgo121` setting is `"1"` (`godebugHttpmuxgo121`; the model's `init` stores `true` only then:
  httpdriver, 2026-11-25, so that under the environment premise `GodebugHttpmuxgo121Not1` the
  program learns `use121 = false`, #18's option (a)).
* `maxSlice` (`mapping.go:22`, `var maxSlice int = 8`, translated): `8`.
* `serveEnv` (`ServeLoopDefs.lean`): `testHookServerServe` `nil` (`server.go:3430`, no initializer,
  assigned only by net/http's tests) and `DefaultServeMux = &defaultServeMux` (`server.go:2611`,
  translated).
* `ctxKeys` (`ServeDefs.lean`): `ServerContextKey`, `LocalAddrContextKey` hold some pointer each
  (`server.go:245`, `server.go:251`: `&contextKey{...}`).
* `aLongTimeAgo` (`http.go:108`, `time.Unix(1, 0)`): some `time.Time`.
* `wPools`, `rPool` (`ServerConn.lean`): `bufioWriter2kPool`, `bufioWriter4kPool`, `bufioReaderPool`
  (`server.go:871-873`, `sync.Pool`, no initializer: zero, `New` nil, which is Perennial's
  `init_Pool`'s premise) as pools of raw buffered writers (2048, 4096 bytes) and readers. The pools'
  predicates are chosen here, as an `init_Pool` would: sound only because these variables are
  untranslated and allocated inside their opaque initializers, so nothing else yields their
  points-to; translating them reopens the question.

`readEnv` is not claimed: it follows from net/http's `isPkgInit` (`readEnv_of_init`).
`wp_init_first_mux` (proved) makes the right to register on `DefaultServeMux` (`muxOwn … []`) and
`httpSrvEnv` from it.

**Interim trust-boundary axiom**, retired by L2 step 6 (net/http's initializer proved;
notes/library-drivers.md). Until 2026-11-25 its post was `muxOwn (globalAddr defaultServeMux) []`
over an invariant on the mux's tree alone, and it took `threadBound GF ≤ 2 ^ 30` (now
`wp_init_first_mux`'s, for the mux's reader-slot pools).
-/
module

public import Net.Proof.net.http.Init
public import Net.Proof.net.http.MuxDefs
public import Perennial.Proof.io.Base
public import Proof.internal.poll.PkgInit

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http

section init
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

/-- What net/http's first initialization leaves (see the file header). -/
def initFirstRes : IProp GF :=
  iprop(globalAddr net.http.defaultServeMux ↦ (zero_val net.http.ServeMux) ∗
    (∃ b : Bool, globalAddr net.http.use121 ↦□ b ∗ ⌜b = true → godebugHttpmuxgo121 = go!"1"⌝) ∗
    globalAddr net.http.maxSlice ↦□ (W64 8) ∗
    serveEnv ∗ ctxKeys ∗ (∃ tm : time.Time, globalAddr net.http.aLongTimeAgo ↦□ tm) ∗ wPools ∗ rPool)

/-- **Trust-boundary axiom, interim** (see the file header): net/http's first initialization: its
package fact, and `initFirstRes`. Interim, retired by L2 step 6 (net/rpc's and net/http's
initializers proved; notes/library-drivers.md). -/
axiom wp_init_first (g g' : GoString → IProp GF)
    (hnot : g pkg_id.net.http ⊢ iprop(False))
    (Hinit : GetIsPkgInitProp pkg_id.net.http g')
    (hsame : ∀ p, p ≠ pkg_id.net.http → g' p = g p) :
    {{ ownInitializing g }} (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing g' ∗ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗
        initFirstRes (GF := GF) (hG := hG) }}

/-- `poll.ErrDeadlineExceeded` holds some error, for good (internal/poll's package fact). -/
theorem pollDeadline_of_init : isPkgInit (PROP := IProp GF) pkg_id.internal.poll ⊢
    ∃ e : GoInterface, globalAddr internal.poll.ErrDeadlineExceeded ↦□ e := by
  refine (isPkgInit_access (PROP := IProp GF) pkg_id.internal.poll).trans ?_
  show iprop((∃ e : GoInterface, typedPointsto (globalAddr internal.poll.ErrNoDeadline) e DFrac.discard) ∗
    (∃ e : GoInterface, typedPointsto (globalAddr internal.poll.ErrDeadlineExceeded) e DFrac.discard) ∗
    (∃ x : Loc, typedPointsto (globalAddr internal.poll.ErrFileClosing)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard)) ⊢ _
  iintro ⟨-, He, -⟩
  iexact He

/-- `readEnv` from net/http's package fact: io's errors (`httpEnv` holds io's fact) and internal/poll's
`ErrDeadlineExceeded` (net's dependency). -/
theorem readEnv_of_init :
    isPkgInit (PROP := IProp GF) pkg_id.net.http ⊢ readEnv (GF := GF) := by
  iintro #H
  ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  ihave #Hpoll : isPkgInit (PROP := IProp GF) pkg_id.internal.poll $$ []
  · iPkgInit
  ihave #Hi := io.isInit_access $$ Hio
  icases Hi with ⟨-, -, -, -, #HEOF, #HUEOF, -⟩
  ihave #Hed := pollDeadline_of_init $$ Hpoll
  iunfold readEnv
  iframe #

/-- net/http's first initialization, with the right to register on `DefaultServeMux` (no pattern
registered) and the server's variables: from `wp_init_first` and `muxOwnS_init` (the reader-slot pools
of the mux's lock need the machine's thread bound). -/
theorem wp_init_first_mux (g g' : GoString → IProp GF)
    (hnot : g pkg_id.net.http ⊢ iprop(False))
    (Hinit : GetIsPkgInitProp pkg_id.net.http g')
    (hsame : ∀ p, p ≠ pkg_id.net.http → g' p = g p) :
    {{ ownInitializing g ∗ ⌜threadBound GF ≤ 2 ^ 30⌝ }} (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing g' ∗ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗
        muxOwn (GF := GF) (hG := hG) (globalAddr net.http.defaultServeMux) [] ∗
        httpSrvEnv (GF := GF) }} := by
  iintro %Φ ⟨Hown, %Hb⟩ HΦ
  iapply wp_fupd
  iapply (wp_init_first g g' hnot Hinit hsame) $$ Hown
  inext
  iintro ⟨Hown, #Hpkg, Hres⟩
  iunfold initFirstRes at Hres
  icases Hres with ⟨Hm, ⟨%b, #Hu, %_⟩, #Hms, #Hse, #Hck, #Htm, #Hwp, #Hrp⟩
  imod muxOwnS_init (GF := GF) (hG := hG) (E := ⊤) _ b (W64 8) Hb $$ Hm Hu Hms with Hmux
  imodintro
  iapply HΦ
  iframe Hown
  iframe #
  isplitl [Hmux]
  · iunfold muxOwn; iframe Hmux; iexact Hse
  iunfold httpSrvEnv
  iframe #
  isplitl []
  · iapply httpEnv_access $$ Hpkg
  iapply readEnv_of_init $$ Hpkg
end init

end net.http
end Perennial
