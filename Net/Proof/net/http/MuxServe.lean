/-
The `use121` glue of net/http's `ServeMux` on literal path patterns: the mux's state over both
matchers (Go 1.22's `tree`/`index`, `Mux22.lean`, and `serveMux121`, `Mux121.lean`), chosen by
`use121` (fixed by net/http's `init` from `GODEBUG`), and `http.Handle` over it.

* `muxSh m b γ` (persistent): `use121 ↦□ b`, and the chosen matcher's lock guard and reader-slot
  pool (`muxPoolN m`). Any mux, `DefaultServeMux` or one of the program's (`NewServeMux`; until
  2026-11-25 it also held `DefaultServeMux ↦□ m`, which only `http.Handle` reads: `wp_Handle_lit` takes it).
* `muxOwnS m Ps` (the registering owner): `muxSh`, `maxSlice ↦□`, and the owner's half of the chosen
  matcher's state (for Go 1.22, its index too), whose patterns are `Ps`.
* `muxRouteS m p h` (persistent): `muxSh`, and `p`'s route to `h` in the chosen matcher.
* `muxOwnS_init`: from the zero `ServeMux` at `m` (owned) and the two variables, `muxOwnS m []`.
* `wp_Handle_lit`: `http.Handle(p, h)` of a literal pattern not yet registered, by the owner
  (`DefaultServeMux ↦□ m`).
* `wp_ServeMux_ServeHTTP_connect`: `mux.ServeHTTP(w, r)` of a `CONNECT` request for a registered
  literal path (the request net/http's parser makes of `CONNECT p HTTP/1.x`): a reader slot from the
  chosen matcher's pool for the lookup (Go 1.22: `findHandler` → `matchOrRedirect` twice, an exact
  match, no redirect; Go 1.21: `wp_mux121_findHandler_connect`), `r.Pattern`/`pat`/`matches` written
  (1.22), then `p`'s handler serves the request with the thread token. A routed node's `pattern` and
  `handler` fields are persistent (`pfrac`, `MuxTree.lean`), since `findHandler` reads them after the
  lock is released. Only this case: the other requests (unrouted paths, redirects, 404) are not
  needed by net/rpc over HTTP and are not proved here.

Defs (no axiom): `MuxDefs`' `muxOwn`/`muxRoute` are these (phase 7 S5, #24).
-/
module

public import Net.Proof.net.http.Mux22
public import Net.Proof.net.http.Mux121
public import Proof.net.url.Escape
public import Spec.net.url.URL__EscapedPath

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
  iprop(globalAddr net.http.use121 ↦□ b ∗
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

/-- **A fresh mux** (see the file header): the zero `ServeMux` at `m`, owned, with `use121`'s and
`maxSlice`'s values, gives the right to register on it, no pattern registered. -/
theorem muxOwnS_init {E : CoPset} (m : Loc) (b : Bool) (ms : w64) (Hb : threadBound GF ≤ 2 ^ 30) :
    ⊢ m ↦ (zero_val net.http.ServeMux) -∗ globalAddr net.http.use121 ↦□ b -∗
      globalAddr net.http.maxSlice ↦□ ms ={E}=∗
      muxOwnS (GF := GF) (hG := hG) m [] := by
  iintro Hm #Hu #Hms
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
    (hp : litPat p) (hnew : p ∉ Ps) (hh : h ≠ interface.nil)
    (hfn : ∀ v, h = interface.mkOk net.http.HandlerFunc.ty v → ∃ fv : GoFunc, v = #fv ∧ fv ≠ func.nil) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        isPkgInit (PROP := IProp GF) pkg_id.strings ∗ isPkgInit (PROP := IProp GF) pkg_id.net.url ∗
        isPkgInit (PROP := IProp GF) pkg_id.fmt ∗
        (globalAddr net.http.DefaultServeMux ↦□ m ∗ muxOwnS (GF := GF) (hG := hG) m Ps) }}
      (App (App (Val (@! net.http.Handle)) (Val #p)) (Val #h))
    {{ RET #(); muxOwnS (GF := GF) (hG := hG) m (p :: Ps) ∗ muxRouteS (GF := GF) (hG := hG) m p h }} := by
  unfold muxOwnS
  wp_start as Hown
  icases Hown with ⟨#Hd, %b, %γ, %ms, Hsh, #Hms, Hst⟩
  iunfold muxSh at Hsh
  icases Hsh with ⟨#Hu, Hshb⟩
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

section dispatch
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]

/-- A route of the tree's state is one of its patterns. -/
theorem routesOk_found (S : TreeSt) (Rt : GMap GoString GoInterface) (p : GoString) (h : GoInterface)
    (hR : routesOk Rt S) (hRp : Rt !! p = some h) : ∃ pp, (p, pp, h) ∈ S.pats := by
  rw [hR p] at hRp
  cases hf : S.pats.find? (fun e => decide (e.1 = p)) with
  | none => rw [hf] at hRp; simp at hRp
  | some e =>
    rw [hf] at hRp
    have hm := List.mem_of_find?_eq_some hf
    have he := List.find?_some hf
    obtain ⟨a, b, c⟩ := e
    simp only [Option.map_some, Option.some.injEq] at hRp
    simp only [decide_eq_true_eq] at he
    subst he hRp
    exact ⟨b, hm⟩

/-- A set node's `pattern` and `handler` fields (persistent). -/
def nodeFix (l pp : Loc) (h : GoInterface) : IProp GF :=
  iprop(structFieldRef net.http.routingNode go!"pattern" l ↦□ pp ∗
    structFieldRef net.http.routingNode go!"handler" l ↦□ h)

instance nodeFix_persistent (l pp : Loc) (h : GoInterface) :
    Persistent (nodeFix (GF := GF) (hG := hG) l pp h) := by
  unfold nodeFix; infer_instance

/-- A registered pattern's node, from the tree: its set fields and its `*pattern` (persistent). -/
theorem treeRep_fix (dq : DFrac) (root : Loc) (S : TreeSt) (hok : S.ok root)
    (e : List w8 × Loc × GoInterface) (he : e ∈ S.pats) :
    treeRep (GF := GF) (hG := hG) dq S ⊢ treeRep dq S ∗
      (nodeFix (locOf (S.nodes !! patKeys e.1)) e.2.1 e.2.2 ∗ patRep e.2.1 e.1 ∗
        ⌜locOf (S.nodes !! patKeys e.1) ≠ null⌝) := by
  obtain ⟨dP, hdP⟩ := hok.node_of_prefix he (k := patKeys e.1) (List.prefix_refl _)
  obtain ⟨hlP, -, -, -, hpatP, -⟩ := hok.2.2.2.2.2 _ dP hdP
  obtain ⟨hppP, hhP⟩ := hpatP e he rfl
  rw [hdP, show locOf (some dP) = dP.l from rfl]
  unfold treeRep
  iintro ⟨HN, #HP⟩
  ihave #Hpe := BigSepL.bigSepL_mem (Φ := fun e => patRep (GF := GF) (hG := hG) e.2.1 e.1) he $$ HP
  ihave %hpp : ⌜e.2.1 ≠ null⌝ $$ [Hpe]
  · iunfold patRep at Hpe
    icases Hpe with ⟨%sl, %loc, Hpp, -⟩
    iapply typedPointsto_not_null _ _ _ $$ Hpp
  have hdisc : pfrac dq dP.pat = DFrac.discard := by simp [pfrac, hppP, hpp]
  icases (BigSepM.bigSepM_delete (Φ := fun _ d => nodeRep (GF := GF) (hG := hG) dq d) hdP).1 $$ HN
    with ⟨Hd, HN⟩
  iunfold nodeRep at Hd
  rw [hdisc]
  icases Hd with ⟨#Hp, #Hh, Hc, Hm, He⟩
  isplitl [HN Hc Hm He]
  · isplitl [HN Hc Hm He]
    · iapply (BigSepM.bigSepM_delete (Φ := fun _ d => nodeRep (GF := GF) (hG := hG) dq d) hdP).2
      iunfold nodeRep; rw [hdisc]
      iframe; iframe #
    · iexact HP
  iunfold nodeFix
  rw [← hppP, ← hhP]
  iframe #
  ipureintro; exact hlP

/-- `escapedPathF` of a literal path with no `RawPath`: the path. -/
theorem escapedPathF_lit (p : List w8) (hp : litPat p) : net.url.escapedPathF [] p = p := by
  have hesc : ∀ c : w8, pathByte c = true → net.url.shouldEscapeRef c net.url.mPath = false := by
    decide
  have hnone : net.url.escapeF p net.url.mPath = p := by
    have : ∀ l : List w8, (∀ c ∈ l, pathByte c = true) → net.url.escapeF l net.url.mPath = l := by
      intro l hl
      induction l with
      | nil => rfl
      | cons c l ih =>
        have h1 := hesc c (hl c List.mem_cons_self)
        have h2 : (net.url.mPath == net.url.mQueryComponent) = false := by decide
        have ih' := ih (fun b hb => hl b (List.mem_cons_of_mem _ hb))
        unfold net.url.escapeF at ih' ⊢
        simp only [List.flatMap_cons, h2, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at ih' ⊢
        simp only [h1, Bool.false_eq_true, ↓reduceIte, List.singleton_append, ih']
    exact this p hp.2
  have hne : p ≠ [W8 42] := by
    intro h0; rw [h0] at hp; have := hp.1; simp at this
  unfold net.url.escapedPathF
  simp only [List.isEmpty_nil, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    beq_iff_eq, hne]
  exact hnone

/-- `mux.matchOrRedirect("", m, p, u)` of a registered literal path, by a reader of the Go 1.22
matcher (`meth` neither `""` nor `HEAD`): `p`'s node, no matches, no redirect; and the node's set
fields and `*pattern` (persistent), which `findHandler` reads after the lock is released. -/
theorem wp_matchOrRedirect_found (wp_PathUnescape : net.url.PathUnescape.spec (GF := GF) (hG := hG))
    (wp_IndexByte : strings.IndexByte.spec (GF := GF) (hG := hG))
    (wp_Count : strings.Count.spec (GF := GF) (hG := hG))
    (m : Loc) (γ : Mux22Names) (p : GoString) (h : GoInterface) (meth : GoString) (u : Loc)
    (hm : meth ≠ []) (hhead : meth ≠ go!"HEAD") :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isPkgInit (PROP := IProp GF) pkg_id.net.url ∗
        isPkgInit (PROP := IProp GF) pkg_id.strings ∗
        sync.ownRWMutex (muxMu m) (mux22P (GF := GF) (hG := hG) γ m) ∗ p ↪[γ.r]□ h }}
      (App (App (App (App (Val (m @!! go.GoType.PointerType net.http.ServeMux.ty @!! go!"matchOrRedirect"))
        (Val #([] : List w8))) (Val #meth)) (Val #p)) (Val #u))
    {{ (n : Loc), RET (PairV (PairV #n #slice.nil) #(null : Loc)); ∃ pp : Loc,
        sync.ownRWMutex (muxMu m) (mux22P γ m) ∗ nodeFix n pp h ∗ patRep pp p ∗ ⌜n ≠ null⌝ }} := by
  wp_start as ⟨Hrw, #Hel⟩
  try wp_auto
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrw] as ⟨Hrl, HP⟩
  iunfold mux22P at HP
  icases HP with ⟨%S, %Rt, Hv, HA, Hrep, %HS⟩
  ihave %HRp := ghost_map_lookup $$ HA Hel
  obtain ⟨pp, he⟩ := routesOk_found S Rt p h HS.2.1 HRp
  icases treeRep_fix _ (muxRoot m) S HS.1 (p, pp, h) he $$ Hrep with ⟨Hrep, #Hfix, #Hpr, %hn⟩
  try wp_auto
  wp_apply wp_tree_match_found wp_PathUnescape wp_IndexByte _ (muxRoot m) S HS.1 (p, pp, h) he meth hm
    hhead $$ [$Hrep] as Hrep
  try wp_auto
  wp_apply wp_exactMatch_found wp_Count _ (muxRoot m) S HS.1 (p, pp, h) he $$ [$Hrep] as Hrep
  try wp_auto
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hv HA Hrep] as Hrw
  · iunfold mux22P; iexists S, Rt; iframe; ipureintro; exact HS
  try wp_auto
  iapply HΦ
  iexists pp
  iframe; iframe #
  ipureintro; exact hn

/-- `pp.String()` of a registered pattern: its string. -/
theorem wp_pattern_String (pp : Loc) (p : List w8) :
    {{ patRep (GF := GF) (hG := hG) pp p }}
      (App (Val (pp @!! go.GoType.PointerType net.http.pattern.ty @!! go!"String")) (Val #()))
    {{ RET #p; True }} := by
  unfold patRep
  wp_start as ⟨%sl, %loc, Hpp, #Hsl⟩
  iStructNamedPrefix Hpp "P"
  wp_auto
  iapply HΦ
  ipureintro; trivial

/-- The URL of a `CONNECT` request for the path `p` (net/http's parse of `CONNECT p HTTP/1.x`). -/
abbrev connURL (p : GoString) : net.url.URL := { (_root_.Perennial.zero_val net.url.URL) with Path' := p }

/-- `mux.findHandler(r)` of a `CONNECT` request for a registered literal path, by a reader of the Go
1.22 matcher: `p`'s handler, pattern and `*pattern`, no matches. -/
theorem wp_findHandler22_connect (wp_PathUnescape : net.url.PathUnescape.spec (GF := GF) (hG := hG))
    (wp_IndexByte : strings.IndexByte.spec (GF := GF) (hG := hG))
    (wp_Count : strings.Count.spec (GF := GF) (hG := hG))
    (wp_EscapedPath : net.url.URL.EscapedPath.spec (GF := GF) (hG := hG))
    (m : Loc) (γ : Mux22Names) (r u : Loc) (dq : DFrac) (q : Qp) (p : GoString) (h : GoInterface)
    (hp : litPat p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isPkgInit (PROP := IProp GF) pkg_id.net.url ∗
        isPkgInit (PROP := IProp GF) pkg_id.strings ∗
        sync.ownRWMutex (muxMu m) (mux22P (GF := GF) (hG := hG) γ m) ∗ p ↪[γ.r]□ h ∗
        structFieldRef net.http.Request go!"Method" r ↦□ go!"CONNECT" ∗
        structFieldRef net.http.Request go!"URL" r ↦{dq} u ∗
        structFieldRef net.http.Request go!"Host" r ↦{dq} ([] : List w8) ∗ u ↦{DFrac.own q} connURL p }}
      (App (Val (m @!! go.GoType.PointerType net.http.ServeMux.ty @!! go!"findHandler")) (Val #r))
    {{ (pp : Loc), RET (PairV (PairV (PairV #h #p) #pp) #slice.nil);
        sync.ownRWMutex (muxMu m) (mux22P γ m) ∗
        structFieldRef net.http.Request go!"URL" r ↦{dq} u ∗
        structFieldRef net.http.Request go!"Host" r ↦{dq} ([] : List w8) ∗
        u ↦{DFrac.own q.half} connURL p }} := by
  wp_start as ⟨Hrw, #Hel, #Hmeth, Hurl, Hhost, Hu⟩
  icases (typedPointsto_half_split u (connURL p) q).1 $$ Hu with ⟨Hu, Hu1⟩
  iStructNamedPrefix Hu1 "U"
  try wp_auto
  wp_apply wp_EscapedPath u _ (connURL p) $$ [$Hu] as Hu
  rw [escapedPathF_lit p hp]
  try wp_auto
  wp_apply wp_matchOrRedirect_found wp_PathUnescape wp_IndexByte wp_Count m γ p h go!"CONNECT" u
    (by decide) (by decide) $$ [$Hrw $Hel] as %n ⟨%pp, Hrw, #Hfix, #Hpr, %hn⟩
  · iframe #
  try wp_auto
  wp_apply wp_matchOrRedirect_found wp_PathUnescape wp_IndexByte wp_Count m γ p h go!"CONNECT" null
    (by decide) (by decide) $$ [$Hrw $Hel] as %n2 ⟨%pp2, Hrw, #Hfix2, #Hpr2, %hn2⟩
  · iframe #
  try wp_auto
  rw [decide_eq_false hn2]
  iunfold nodeFix at Hfix2
  icases Hfix2 with ⟨#Hfp, #Hfh⟩
  try wp_auto
  wp_apply wp_pattern_String pp2 p $$ [$Hpr2]
  try wp_auto
  iapply HΦ
  iframe

/-- `mux.ServeHTTP(w, r)` of a `CONNECT` request for a registered literal path `p` (the fields
net/http's request parser leaves, `RequestURI` the path, `Host` empty), over either matcher: a
reader slot borrowed from the matcher's pool for the lookup, then `p`'s handler `h` serves the
request with the thread token. -/
theorem wp_ServeMux_ServeHTTP_connect
    (wp_PathUnescape : net.url.PathUnescape.spec (GF := GF) (hG := hG))
    (wp_IndexByte : strings.IndexByte.spec (GF := GF) (hG := hG))
    (wp_Count : strings.Count.spec (GF := GF) (hG := hG))
    (wp_EscapedPath : net.url.URL.EscapedPath.spec (GF := GF) (hG := hG))
    (m : Loc) (p : GoString) (h : GoInterface) (e : GoInterfaceOk) (hhe : h = interface.ok e)
    (hp : litPat p) (w : GoInterface) (r u : Loc) (pat0 : GoString) (pp0 : Loc) (ms0 : GoSlice)
    (Φ : val → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isPkgInit (PROP := IProp GF) pkg_id.net.url ∗
      isPkgInit (PROP := IProp GF) pkg_id.strings ∗ muxRouteS (GF := GF) (hG := hG) m p h ∗ threadTok ∗
      structFieldRef net.http.Request go!"Method" r ↦□ go!"CONNECT" ∗
      structFieldRef net.http.Request go!"RequestURI" r ↦ p ∗
      structFieldRef net.http.Request go!"URL" r ↦ u ∗
      structFieldRef net.http.Request go!"Host" r ↦ ([] : List w8) ∗
      structFieldRef net.http.Request go!"Pattern" r ↦ pat0 ∗
      structFieldRef net.http.Request go!"pat" r ↦ pp0 ∗
      structFieldRef net.http.Request go!"matches" r ↦ ms0 ∗ u ↦ connURL p ∗
      (threadTok -∗ WP (App (App (Val #(methods e.ty go!"ServeHTTP" e.v)) (Val #w)) (Val #r))
        {{ v, ⌜v = #()⌝ ∗ Φ #() }}) ⊢
    WP (App (App (Val (m @!! go.GoType.PointerType net.http.ServeMux.ty @!! go!"ServeHTTP")) (Val #w))
      (Val #r)) {{ Φ }} := by
  iintro ⟨#Hsync, #Hurl0, #Hstr, #Hrt, Htok, #Hmeth, Hruri, Hurl, Hhost, Hpat, Hpp, Hms, Hu, Hk⟩
  iunfold muxRouteS at Hrt
  icases Hrt with ⟨%b, %γ, #Hsh, #Hel⟩
  iunfold muxSh at Hsh
  icases Hsh with ⟨#Hu121, #Hshb⟩
  subst hhe
  have hpstar : p ≠ go!"*" := by
    intro h0; have := hp.1; rw [h0] at this; simp at this
  cases b
  · irevert Hshb Hel
    simp only [Bool.false_eq_true, ↓reduceIte]
    iintro ⟨#Hg, #Hpool⟩ #Hel
    iapply fupd_wp
    imod threadPool.borrow (muxPoolN m) γ.p22
      (sync.ownRWMutex (muxMu m) (mux22P (GF := GF) (hG := hG) γ.n22 m)) ⊤ (fun _ _ => CoPset.mem_full)
      $$ [Hpool Htok] with ⟨Hrw, Hloan⟩
    · iframe #; iframe
    imodintro
    rw [method_unfold (t := go.GoType.PointerType net.http.ServeMux.ty)]
    wp_call
    try wp_auto
    rw [decide_eq_false hpstar]
    try wp_auto
    wp_apply wp_findHandler22_connect wp_PathUnescape wp_IndexByte wp_Count wp_EscapedPath m γ.n22 r u
      (DFrac.own 1) 1 p (interface.ok e) hp $$ [$Hrw $Hel $Hmeth $Hurl $Hhost $Hu]
      as %pp ⟨Hrw, Hurl, Hhost, Hu⟩
    · iframe #
    iapply fupd_wp
    imod threadPool.giveBack (muxPoolN m) γ.p22
      (sync.ownRWMutex (muxMu m) (mux22P (GF := GF) (hG := hG) γ.n22 m)) ⊤ (fun _ _ => CoPset.mem_full)
      $$ [Hpool Hloan Hrw] with Htok
    · iframe #; iframe
    imodintro
    try wp_auto
    wp_bind (App (App (Val #(methods e.ty go!"ServeHTTP" e.v)) (Val #w)) (Val #r))
    iapply wp_wand $$ (Hk $$ Htok)
    iintro %v ⟨%hv, HΦ⟩
    subst hv
    wp_auto
    iexact HΦ
  · irevert Hshb Hel
    simp only [↓reduceIte]
    iintro ⟨#Hg, #Hpool⟩ #Hel
    iapply fupd_wp
    imod threadPool.borrow (muxPoolN m) γ.p121
      (sync.ownRWMutex (mux121Mu m) (mux121P (GF := GF) (hG := hG) γ.n121 (mux121Loc m))) ⊤
      (fun _ _ => CoPset.mem_full) $$ [Hpool Htok] with ⟨Hrw, Hloan⟩
    · iframe #; iframe
    imodintro
    rw [method_unfold (t := go.GoType.PointerType net.http.ServeMux.ty)]
    wp_call
    try wp_auto
    rw [decide_eq_false hpstar]
    try wp_auto
    iStructNamedPrefix Hu "U"
    imod (typedPointsto_dfractional (GF := GF) _ u).dfractional_persist (DFrac.own 1) $$ Hurl with #Hurl
    imod (typedPointsto_dfractional (GF := GF) _ ([] : List w8)).dfractional_persist (DFrac.own 1) $$ Hhost
      with #Hhost
    imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist (DFrac.own 1) $$ UHost with #UHost
    imod (typedPointsto_dfractional (GF := GF) _ p).dfractional_persist (DFrac.own 1) $$ UPath with #UPath
    wp_apply wp_mux121_findHandler_connect (mux121Loc m) γ.n121 DFrac.discard r u p [] [] (interface.ok e)
      $$ [$Hrw $Hel] as ⟨Hrw, -⟩
    · iunfold connReqFields; iframe #
    iapply fupd_wp
    imod threadPool.giveBack (muxPoolN m) γ.p121
      (sync.ownRWMutex (mux121Mu m) (mux121P (GF := GF) (hG := hG) γ.n121 (mux121Loc m))) ⊤
      (fun _ _ => CoPset.mem_full) $$ [Hpool Hloan Hrw] with Htok
    · iframe #; iframe
    imodintro
    try wp_auto
    wp_bind (App (App (Val #(methods e.ty go!"ServeHTTP" e.v)) (Val #w)) (Val #r))
    iapply wp_wand $$ (Hk $$ Htok)
    iintro %v ⟨%hv, HΦ⟩
    subst hv
    wp_auto
    iexact HΦ

end dispatch

end net.http
end Perennial
