/-
Shared definitions of the proofs of the lab's model of `net/http` (`harness/rpcmodel/src/net/http`,
`notes/craq-net.md` decision 1): its package-initialized state and the default mux.

**`isPkgInit pkg_id.net.http`** (`isInit`, persistent), stated with no parameter, so that any
package importing `net/http` gets its `IsPkgInit` instance:
* `errHead` holds `errors.New("http: malformed request head")` (`errors.newVar`), and `errStatus`
  `errors.New("http: malformed HTTP response")` (`ReadResponse`'s error);
* `DefaultServeMux` holds a fixed `*ServeMux` `mux` (`↦□`) that is a mux with ghost names `γ`
  (`isMux`): its map `m` is fixed (`↦□`) and owned by the invariant of its mutex `mu`
  (`muxInv`), which keeps a ghost map of the routes equal to the Go map (`γ.routes`, its
  elements persistent: a route is never removed), and half of a ghost variable holding the
  list of registered paths (`γ.owner`);
* an invariant (`ownerInv`) holding the other half of `γ.owner` at `[]`, until a node trades
  its `ownGoState` for it (`muxOwner_claim`).

**`muxRoute p h`** (persistent): the default mux routes `p` to `h`, for good. **`muxOwner R`**
(exclusive): the right to register new paths, `R` the paths registered so far (Go's mux panics
on a duplicate pattern, so `Handle` needs it). A node claims `muxOwner []` once, with its
`ownGoState` (which it still holds after its package initialization: `ownInitializing`), since
two `ownGoState` of a node are exclusive (`ownGoState_excl`: each has the full authority of the
map of initialized packages).

Both carry the mux's pointer, its `isMux` and its names, so neither needs agreement with
another copy of the names.
-/
module

public import Harness.GeneratedProof.net.http
public import Harness.Proof.net.Base
public import Harness.Proof.bufio.Base
public import Perennial.Proof.errors.NewVar
public import Perennial.Proof.sync.Base
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.GhostVar

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace net.http

/-- The ghost names of a mux: the ghost map of its routes, the ghost variable of its
registered paths. -/
abbrev MuxNames := GName × GName

namespace MuxNames
abbrev routes (γ : MuxNames) : GName := γ.1
abbrev owner (γ : MuxNames) : GName := γ.2
end MuxNames

def muxN : Namespace := ndot nroot "net.http.mux"

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The invariant of a mux's mutex, whose map is `mp`: the Go map `M`, the ghost map of the
routes (equal to `M`), half of the registered paths `R` (the keys of `M`). -/
def muxInv (mp : Loc) (γ : MuxNames) : IProp GF :=
  iprop(∃ (M : GMap GoString GoInterface) (R : List GoString),
    ownMap mp (DFrac.own 1) M ∗ ghostMapAuth γ.routes 1 M ∗
    ghostVar γ.owner (1 : Qp).half R ∗ ⌜∀ p, p ∈ R ↔ (M !! p).isSome⌝)

/-- `mux` is a mux with map `mp` and names `γ` (persistent). -/
def isMux (mux mp : Loc) (γ : MuxNames) : IProp GF :=
  iprop(structFieldRef net.http.ServeMux go!"m" mux ↦□ mp ∗
    sync.isMutex (structFieldRef net.http.ServeMux go!"mu" mux) (muxInv mp γ))

instance isMux_persistent (mux mp : Loc) (γ : MuxNames) :
    Persistent (isMux (GF := GF) mux mp γ) := by
  unfold isMux; infer_instance

/-- The owner's half of the registered paths, unclaimed (`[]`), or the `ownGoState` of the node
that claimed it. -/
def ownerInv (γ : MuxNames) : IProp GF :=
  iprop(ghostVar γ.owner (1 : Qp).half ([] : List GoString) ∨
    ∃ σ : GMap GoString Bool, ownGoState σ)

instance ownerInv_timeless (γ : MuxNames) : Timeless (ownerInv (GF := GF) γ) := by
  unfold ownerInv; infer_instance

/-- The default mux: `DefaultServeMux` holds `mux`, a mux with map `mp` and names `γ`
(persistent). -/
def defaultMux (mux mp : Loc) (γ : MuxNames) : IProp GF :=
  iprop(globalAddr DefaultServeMux ↦□ mux ∗ isMux mux mp γ)

instance defaultMux_persistent (mux mp : Loc) (γ : MuxNames) :
    Persistent (defaultMux (GF := GF) mux mp γ) := by
  unfold defaultMux; infer_instance

/-- The package-initialized state of `net/http` (persistent); see the file header. -/
abbrev isInit : IProp GF :=
  iprop("#HerrHead" ∷ errors.newVar errHead go!"http: malformed request head" ∗
    "#HerrStatus" ∷ errors.newVar errStatus go!"http: malformed HTTP response" ∗
    "#HDefaultServeMux" ∷ (∃ (mux mp : Loc) (γ : MuxNames), defaultMux mux mp γ ∗
      inv muxN (ownerInv γ)) ∗
    "_" ∷ True)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.net.http :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.net.http :=
  build_get_is_pkg_init_wf

theorem isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.net.http ⊢ isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.net.http

/-- The default mux routes path `p` to the handler `h`, for good (persistent). -/
def muxRoute (p : GoString) (h : GoInterfaceOk) : IProp GF :=
  iprop(∃ (mux mp : Loc) (γ : MuxNames), defaultMux mux mp γ ∗
    ghostMapElem γ.routes p .discard (interface.ok h))

/-- The right to register new paths at the default mux, `R` the paths registered so far
(exclusive). -/
def muxOwner (R : List GoString) : IProp GF :=
  iprop(∃ (mux mp : Loc) (γ : MuxNames), defaultMux mux mp γ ∗
    ghostVar γ.owner (1 : Qp).half R)

instance muxRoute_persistent (p : GoString) (h : GoInterfaceOk) :
    Persistent (muxRoute (GF := GF) p h) := by
  unfold muxRoute; infer_instance

/-- Two `ownGoState` are exclusive: each holds the full authority of the map of initialized
packages. -/
theorem ownGoState_excl (σ1 σ2 : GMap GoString Bool) :
    ⊢@{IProp GF} ownGoState σ1 -∗ ownGoState σ2 -∗ False := by
  letI := hG.goose_localGS.goose_go_stateGS.package_mono_allG
  unfold ownGoState
  iintro ⟨-, H1, -⟩ ⟨-, H2, -⟩
  ihave %h := ghostMapAuth_valid_2 _ _ _ _ _ $$ H1 H2
  exfalso
  have h1 := h.1
  simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at h1
  grind

/-- A node claims the right to register paths at the default mux, once: with its
`ownGoState`, which the invariant keeps (a second claim would need a second `ownGoState`). -/
theorem muxOwner_claim (σ : GMap GoString Bool) :
    ⊢@{IProp GF} isPkgInit pkg_id.net.http -∗ ownGoState σ ={⊤}=∗ muxOwner [] := by
  iintro #Hpkg Hown
  ihave #Hi := isInit_access $$ Hpkg
  icases Hi with ⟨-, -, ⟨%mux, %mp, %γ, #Hd, #Hinv⟩, -⟩
  iinv Hinv with Hi Hclose
  unfold ownerInv
  imod Hi with (Ho | ⟨%σ', Ho⟩)
  · imod Hclose $$ [Hown] with -
    · inext; iright; iexists σ; iexact Hown
    imodintro
    unfold muxOwner
    iexists mux, mp, γ
    iframe Hd Ho
  · iexfalso
    iapply ownGoState_excl σ σ' $$ Hown Ho

/-- `muxOwner_claim` from `ownInitializing`. -/
theorem muxOwner_claim_init (get_is_pkg_init : GoString → IProp GF) :
    ⊢@{IProp GF} isPkgInit pkg_id.net.http -∗ ownInitializing get_is_pkg_init ={⊤}=∗
      muxOwner [] := by
  iintro #Hpkg Hown
  rw [ownInitializing_unseal]
  unfold ownInitializingDef
  icases Hown with ⟨%σ, Hown, -⟩
  iapply muxOwner_claim σ $$ Hpkg Hown

end init

end net.http

end Perennial
