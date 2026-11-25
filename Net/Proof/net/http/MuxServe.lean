/-
The `use121` glue of net/http's `ServeMux` on literal path patterns: the mux's state over both
matchers (Go 1.22's `tree`/`index`, `Mux22.lean`, and `serveMux121`, `Mux121.lean`), chosen by
`use121` (fixed by net/http's `init` from `GODEBUG`), and `http.Handle` over it.

* `muxSh m b γ` (persistent): `use121 ↦□ b`, `DefaultServeMux ↦□ m`, and the chosen matcher's lock
  guard and reader-slot pool (`muxPoolN m`).
* `muxOwnS m Ps` (the registering owner): `muxSh`, `maxSlice ↦□`, and the owner's half of the chosen
  matcher's state (for Go 1.22, its index too), whose patterns are `Ps`.
* `muxRouteS m p h` (persistent): `muxSh`, and `p`'s route to `h` in the chosen matcher.
* `muxOwnS_init`: from the zero `ServeMux` at `m` (owned) and the three variables, `muxOwnS m []`.
* `wp_Handle_lit`: `http.Handle(p, h)` of a literal pattern not yet registered, by the owner.

Defs (no axiom): the restatement of `MuxDefs`' `muxOwn`/`muxRoute` (phase 7 S5, #24) is to be these.
-/
module

public import Net.Proof.net.http.Mux22
public import Net.Proof.net.http.Mux121
public import Net.Proof.net.http.MuxDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http

/-- The ghost names of a `ServeMux`: both matchers' and their reader pools'. -/
structure MuxAllNames where
  n121 : Mux121Names
  p121 : GName
  n22 : Mux22Names
  p22 : GName

/-- The namespace of a mux's reader-slot pool. -/
def muxPoolN (m : Loc) : Namespace := (nroot.@"net.http.muxpool").@m

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]

/-- The mux's `mux121` field. -/
abbrev mux121Loc [GoGlobalContext] [GoSemanticsFunctions] (m : Loc) : Loc := structFieldRef net.http.ServeMux go!"mux121" m
/-- The Go 1.22 matcher's lock, the mux's `mu`. -/
abbrev muxMu [GoGlobalContext] [GoSemanticsFunctions] (m : Loc) : Loc := structFieldRef net.http.ServeMux go!"mu" m
/-- The Go 1.21 matcher's lock. -/
abbrev mux121Mu [GoGlobalContext] [GoSemanticsFunctions] (m : Loc) : Loc := structFieldRef net.http.serveMux121 go!"mu" (mux121Loc m)
/-- The Go 1.22 matcher's index, the mux's `index`. -/
abbrev muxIdx [GoGlobalContext] [GoSemanticsFunctions] (m : Loc) : Loc := structFieldRef net.http.ServeMux go!"index" m

/-- The mux's shared part (see the file header). -/
def muxSh (m : Loc) (b : Bool) (γ : MuxAllNames) : IProp GF :=
  iprop(globalAddr net.http.use121 ↦□ b ∗ globalAddr net.http.DefaultServeMux ↦□ m ∗
    if b then
      sync.isRWMutexGuard (mux121Mu m) (mux121P (GF := GF) (hG := hG) γ.n121 (mux121Loc m)) ∗
      threadPool.isThreadPool (muxPoolN m) γ.p121
        (sync.ownRWMutex (mux121Mu m) (mux121P (GF := GF) (hG := hG) γ.n121 (mux121Loc m)))
    else
      sync.isRWMutexGuard (muxMu m) (mux22P (GF := GF) (hG := hG) γ.n22 m) ∗
      threadPool.isThreadPool (muxPoolN m) γ.p22 (sync.ownRWMutex (muxMu m) (mux22P (GF := GF) (hG := hG) γ.n22 m)))

instance muxSh_persistent (m : Loc) (b : Bool) (γ : MuxAllNames) :
    Persistent (muxSh (GF := GF) (hG := hG) m b γ) := by
  unfold muxSh; cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

/-- The right to register on `m`, its patterns `Ps` (see the file header). -/
def muxOwnS (m : Loc) (Ps : List GoString) : IProp GF :=
  iprop(∃ (b : Bool) (γ : MuxAllNames) (ms : w64), muxSh (GF := GF) (hG := hG) m b γ ∗ globalAddr net.http.maxSlice ↦□ ms ∗
    if b then ∃ st : Mux121St, ghostVar γ.n121.st (1 : Qp).half st ∗ ⌜st.pats = Ps⌝
    else ∃ S : TreeSt, ghostVar γ.n22.st (1 : Qp).half S ∗ idxRep (muxIdx m) (S.pats.map Prod.fst) ∗
      ⌜S.pats.map Prod.fst = Ps⌝)

/-- `m` routes the literal path `p` to `h` (persistent; see the file header). -/
def muxRouteS (m : Loc) (p : GoString) (h : GoInterface) : IProp GF :=
  iprop(∃ (b : Bool) (γ : MuxAllNames), muxSh (GF := GF) (hG := hG) m b γ ∗
    if b then p ↪[γ.n121.r]□ h else p ↪[γ.n22.r]□ h)

instance muxRouteS_persistent (m : Loc) (p : GoString) (h : GoInterface) :
    Persistent (muxRouteS (GF := GF) (hG := hG) m p h) := by
  unfold muxRouteS
  have : ∀ b γ, Persistent (iprop(muxSh (GF := GF) (hG := hG) m b γ ∗
      if b then p ↪[γ.n121.r]□ h else p ↪[γ.n22.r]□ h)) := by
    intro b γ; cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance
  infer_instance

/-- **A fresh mux** (see the file header): the zero `ServeMux` at `m`, owned, with `use121`, `DefaultServeMux`
and `maxSlice`'s values, gives the right to register on it, no pattern registered. -/
theorem muxOwnS_init {E : CoPset} (m : Loc) (b : Bool) (ms : w64) (Hb : threadBound GF ≤ 2 ^ 30) :
    ⊢ m ↦ (zero_val net.http.ServeMux) -∗ globalAddr net.http.use121 ↦□ b -∗
      globalAddr net.http.DefaultServeMux ↦□ m -∗ globalAddr net.http.maxSlice ↦□ ms ={E}=∗
      muxOwnS (GF := GF) (hG := hG) m [] := by
  iintro Hm #Hu #Hd #Hms
  iStructNamed Hm
  cases b
  · imod mux22_init (GF := GF) (hG := hG) (E := E) (muxPoolN m) m Hb $$ mu tree index
      with ⟨%γ, %γp, #Hg, #Hp, Hv, Hidx⟩
    imodintro
    iunfold muxOwnS
    iexists false, ⟨⟨γ.st, γ.r⟩, γp, γ, γp⟩, ms
    iunfold muxSh
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe; iframe #
    simp only [treeSt0, List.map_nil]
    iframe
  · imod mux121_init (GF := GF) (hG := hG) (E := E) (muxPoolN m) (mux121Loc m) Hb $$ mux121
      with ⟨%γ, %γp, #Hg, #Hp, Hv⟩
    imodintro
    iunfold muxOwnS
    iexists true, ⟨γ, γp, ⟨γ.st, γ.r⟩, γp⟩, ms
    iunfold muxSh
    simp only [↓reduceIte]
    iframe; iframe #
    ipureintro; rfl

end defs

section wp
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]

/-- `http.Handle(p, h)` by the owner, of a literal pattern not yet registered and a handler that
`Handle` accepts (non-nil; a `HandlerFunc` a non-nil function): `p` registered for `h`. -/
theorem wp_Handle_lit (wp_Search : sort.Search.spec (GF := GF) (hG := hG))
    (wp_IndexAny : strings.IndexAny.spec (GF := GF) (hG := hG))
    (wp_IndexByte : strings.IndexByte.spec (GF := GF) (hG := hG))
    (wp_PathUnescape : net.url.PathUnescape.spec (GF := GF) (hG := hG))
    (wp_Caller : runtime.Caller.spec (GF := GF) (hG := hG))
    (wp_Sprintf : fmt.Sprintf.spec (GF := GF) (hG := hG))
    (m : Loc) (Ps : List GoString) (p : GoString) (h : GoInterface)
    (hp : litPattern p) (hnew : p ∉ Ps) (hh : h ≠ interface.nil)
    (hfn : ∀ v, h = interface.mkOk net.http.HandlerFunc.ty v → ∃ fv : GoFunc, v = #fv ∧ fv ≠ func.nil) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        isPkgInit (PROP := IProp GF) pkg_id.strings ∗ isPkgInit (PROP := IProp GF) pkg_id.net.url ∗
        isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ muxOwnS (GF := GF) (hG := hG) m Ps }}
      (App (App (Val (@! net.http.Handle)) (Val #p)) (Val #h))
    {{ RET #(); muxOwnS (GF := GF) (hG := hG) m (p :: Ps) ∗ muxRouteS (GF := GF) (hG := hG) m p h }} := by
  unfold muxOwnS
  wp_start as Hown
  icases Hown with ⟨%b, %γ, %ms, Hsh, #Hms, Hst⟩
  iunfold muxSh at Hsh
  icases Hsh with ⟨#Hu, #Hd, Hshb⟩
  wp_auto
  cases b
  · irevert Hshb Hst
    simp only [Bool.false_eq_true, ↓reduceIte]
    iintro ⟨#Hg, #Hp⟩ ⟨%S, Hv, Hidx, %HPs⟩
    subst HPs
    wp_auto
    wp_apply (wp_register_lit wp_IndexAny wp_IndexByte wp_PathUnescape wp_Caller wp_Sprintf m γ.n22 S ms
      p h hp hnew hh hfn) $$ [Hv Hidx] as ⟨%S', %pp, Hv, Hidx, #Hel, %HS'⟩
    · iframe; iframe #
    iapply HΦ
    isplitl [Hv Hidx]
    · iexists false, γ, ms
      iunfold muxSh
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe; iframe #
      ipureintro; rw [HS']; rfl
    · iunfold muxRouteS
      iexists false, γ
      iunfold muxSh
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe #
  · irevert Hshb Hst
    simp only [↓reduceIte]
    iintro ⟨#Hg, #Hp⟩ ⟨%st, Hv, %HPs⟩
    subst HPs
    wp_auto
    wp_apply (wp_mux121_handle wp_Search (mux121Loc m) γ.n121 st p h hp.1 hh hnew) $$ [Hv]
      as ⟨%st', Hv, #Hel, %Hst'⟩
    · iframe; iframe #
    iapply HΦ
    isplitl [Hv]
    · iexists true, γ, ms
      iunfold muxSh
      simp only [↓reduceIte]
      iframe; iframe #
      ipureintro; exact Hst'
    · iunfold muxRouteS
      iexists true, γ
      iunfold muxSh
      simp only [↓reduceIte]
      iframe #

end wp

end net.http
end Perennial
