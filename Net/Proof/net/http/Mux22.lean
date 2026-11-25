/-
net/http's Go 1.22 matcher (the `ServeMux`'s `tree` and `index`, used unless `GODEBUG` sets
`httpmuxgo121=1`) on literal path patterns: the state its `RWMutex` guards, and registration.

* `TreeSt` is countable (for a ghost variable); `nodeRep`, `mapRep` and `treeRep` split by
  fractions (`treeRep_split`).
* `mux22P γ mux q`: what the mux's `RWMutex` guards (fractional, `mux22P_fractional`): the tree's
  state (a ghost variable, the owner holding the other half), the routes (a ghost map, a pattern to
  its handler; `p ↪[γ.r]□ h` once registered) and `treeRep`, with `TreeSt.ok`. The index is the
  registering owner's alone (`idxRep`, `MuxIndex.lean`): only `registerErr` touches it.
-/
module

public import Net.Proof.net.http.MuxIndex
public import Net.Proof.net.http.MuxParse
public import Perennial.Spec.runtime.Caller
public import Proof.fmt.SprintfPure
public import Perennial.Proof.sync.Results
public import Perennial.Proof.sync.RWMutexThreads

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http

section st
variable [GooseExts]

instance Seg.countable : Pos.Countable Seg :=
  .ofInjective (fun x => Pos.Countable.encode (match x with | .lit s => some s | .multi => none))
    (by intro a b h; have h := Pos.encode_inj h; cases a <;> cases b <;> simp_all)

instance entry.countable : Pos.Countable (net.http.entry GoString Loc) :=
  .ofInjective (fun e => Pos.Countable.encode (e.key', e.value'))
    (by rintro ⟨a, b⟩ ⟨c, d⟩ h; have h := Pos.encode_inj h; simp_all)

instance MapSt.countable : Pos.Countable MapSt :=
  .ofInjective (fun st => Pos.Countable.encode (st.s, st.m, st.es, st.M))
    (by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h; have h := Pos.encode_inj h; simp_all)

instance NodeSt.countable : Pos.Countable NodeSt :=
  .ofInjective (fun d => Pos.Countable.encode (d.l, d.pat, d.h, d.ms, d.kids, d.multi, d.empty))
    (by rintro ⟨a, b, c, d, e, f, g⟩ ⟨a', b', c', d', e', f', g'⟩ h
        have h := Pos.encode_inj h; simp_all)

instance TreeSt.countable : Pos.Countable TreeSt :=
  .ofInjective (fun S => Pos.Countable.encode (S.nodes, S.pats))
    (by rintro ⟨a, b⟩ ⟨a', b'⟩ h; have h := Pos.encode_inj h; simp_all)

/-- The routes of the tree's patterns: a pattern to its handler. -/
def routesOk (Rt : GMap GoString GoInterface) (S : TreeSt) : Prop :=
  ∀ k, Rt !! k = (S.pats.find? (fun e => decide (e.1 = k))).map (fun e => e.2.2)

/-- The tree's root: the mux's `tree` field. -/
abbrev muxRoot [GoGlobalContext] [GoSemanticsFunctions] (mux : Loc) : Loc := structFieldRef net.http.ServeMux go!"tree" mux

theorem routesOk_none (Rt : GMap GoString GoInterface) (S : TreeSt) (p : List w8)
    (h : routesOk Rt S) (hnew : p ∉ S.pats.map Prod.fst) : Rt !! p = none := by
  rw [h p]
  cases hf : S.pats.find? (fun e => decide (e.1 = p)) with
  | none => rfl
  | some e =>
    exfalso
    have h1 := List.mem_of_find?_eq_some hf
    have h2 := List.find?_some hf
    simp only [decide_eq_true_eq] at h2
    exact hnew (List.mem_map.mpr ⟨e, h1, h2⟩)

theorem routesOk_insert (Rt : GMap GoString GoInterface) (S S' : TreeSt) (p : List w8) (pp : Loc)
    (hd : GoInterface) (h : routesOk Rt S) (hS' : S'.pats = (p, pp, hd) :: S.pats) :
    routesOk (GMap.insert p hd Rt) S' := by
  intro k
  rw [GMap.lookup_insert_eq_iff, hS']
  by_cases hk : p = k
  · subst hk; simp
  · simp only [hk, ↓reduceIte, h k, List.find?_cons, decide_eq_true_eq]
    simp [hk]

end st

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]

theorem pts_split {V : Type} [TypedPointsto (GF := GF) V] (q1 q2 : Qp) (l : Loc) (v : V) :
    (l ↦{DFrac.own (q1 + q2)} v : IProp GF) ⊣⊢ l ↦{DFrac.own q1} v ∗ l ↦{DFrac.own q2} v :=
  (typedPointsto_dfractional (GF := GF) l v).dfractional (DFrac.own q1) (DFrac.own q2)

theorem mapRep_split (q1 q2 : Qp) (h : Loc) (st : MapSt) (kids : List (GoString × Loc)) :
    mapRep (GF := GF) (hG := hG) (DFrac.own (q1 + q2)) h st kids ⊣⊢
      mapRep (DFrac.own q1) h st kids ∗ mapRep (DFrac.own q2) h st kids := by
  have hcap : (ownSliceCap (GF := GF) (net.http.entry GoString Loc) st.s (DFrac.own (q1 + q2))) ⊣⊢
      ownSliceCap (net.http.entry GoString Loc) st.s (DFrac.own q1) ∗
        ownSliceCap (net.http.entry GoString Loc) st.s (DFrac.own q2) :=
    (ownSliceCap_dfractional (GF := GF) (V := net.http.entry GoString Loc) st.s).dfractional
      (DFrac.own q1) (DFrac.own q2)
  have hmap := (ownMap_fractional (GF := GF) st.m st.M).fractional q1 q2
  unfold mapRep
  by_cases hm : st.m = map.nil
  · simp only [hm, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · iintro ⟨Hh, %Hnd, #Hes, Hcap, %Hk⟩
      icases (pts_split q1 q2 _ _).1 $$ Hh with ⟨Hh1, Hh2⟩
      icases hcap.1 $$ Hcap with ⟨Hc1, Hc2⟩
      isplitl [Hh1 Hc1]
      · iframe; iframe #; ipureintro; exact ⟨Hnd, Hk⟩
      · iframe; iframe #; ipureintro; exact ⟨Hnd, Hk⟩
    · iintro ⟨⟨Hh1, %Hnd, #Hes, Hc1, %Hk⟩, ⟨Hh2, -, -, Hc2, -⟩⟩
      isplitl [Hh1 Hh2]
      · iapply (pts_split q1 q2 _ _).2; iframe
      isplitr
      · ipureintro; exact Hnd
      iframe #
      isplitl [Hc1 Hc2]
      · iapply hcap.2; iframe
      ipureintro; exact Hk
  · simp only [hm, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · iintro ⟨Hh, %Hnd, HM, %Hk⟩
      icases (pts_split q1 q2 _ _).1 $$ Hh with ⟨Hh1, Hh2⟩
      icases hmap.1 $$ HM with ⟨HM1, HM2⟩
      isplitl [Hh1 HM1]
      · iframe; ipureintro; exact ⟨Hnd, Hk⟩
      · iframe; ipureintro; exact ⟨Hnd, Hk⟩
    · iintro ⟨⟨Hh1, %Hnd, HM1, %Hk⟩, ⟨Hh2, -, HM2, -⟩⟩
      isplitl [Hh1 Hh2]
      · iapply (pts_split q1 q2 _ _).2; iframe
      isplitr
      · ipureintro; exact Hnd
      isplitl [HM1 HM2]
      · iapply hmap.2; iframe
      ipureintro; exact Hk

theorem nodeRep_split (q1 q2 : Qp) (d : NodeSt) :
    nodeRep (GF := GF) (hG := hG) (DFrac.own (q1 + q2)) d ⊣⊢
      nodeRep (DFrac.own q1) d ∗ nodeRep (DFrac.own q2) d := by
  unfold nodeRep
  refine ⟨?_, ?_⟩
  · iintro ⟨Hp, Hh, Hm, Hmc, Hec⟩
    icases (pts_split q1 q2 _ _).1 $$ Hp with ⟨Hp1, Hp2⟩
    icases (pts_split q1 q2 _ _).1 $$ Hh with ⟨Hh1, Hh2⟩
    icases (mapRep_split q1 q2 _ _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    icases (pts_split q1 q2 _ _).1 $$ Hmc with ⟨Hmc1, Hmc2⟩
    icases (pts_split q1 q2 _ _).1 $$ Hec with ⟨Hec1, Hec2⟩
    isplitl [Hp1 Hh1 Hm1 Hmc1 Hec1]
    · iframe
    · iframe
  · iintro ⟨⟨Hp1, Hh1, Hm1, Hmc1, Hec1⟩, ⟨Hp2, Hh2, Hm2, Hmc2, Hec2⟩⟩
    isplitl [Hp1 Hp2]
    · iapply (pts_split q1 q2 _ _).2; iframe
    isplitl [Hh1 Hh2]
    · iapply (pts_split q1 q2 _ _).2; iframe
    isplitl [Hm1 Hm2]
    · iapply (mapRep_split q1 q2 _ _ _).2; iframe
    isplitl [Hmc1 Hmc2]
    · iapply (pts_split q1 q2 _ _).2; iframe
    iapply (pts_split q1 q2 _ _).2; iframe

theorem treeRep_split (q1 q2 : Qp) (S : TreeSt) :
    treeRep (GF := GF) (hG := hG) (DFrac.own (q1 + q2)) S ⊣⊢
      treeRep (DFrac.own q1) S ∗ treeRep (DFrac.own q2) S := by
  unfold treeRep
  have hm : ([∗map] _k ↦ d ∈ S.nodes, nodeRep (GF := GF) (hG := hG) (DFrac.own (q1 + q2)) d) ⊣⊢
      ([∗map] _k ↦ d ∈ S.nodes, nodeRep (DFrac.own q1) d) ∗
        ([∗map] _k ↦ d ∈ S.nodes, nodeRep (DFrac.own q2) d) :=
    ⟨(BigSepM.bigSepM_mono_of_forall (fun {_ _} => (nodeRep_split q1 q2 _).1)).trans
        (BiEntails.of_eq BigSepM.bigSepM_sep_eq).1,
      (BiEntails.of_eq BigSepM.bigSepM_sep_eq).2.trans
        (BigSepM.bigSepM_mono_of_forall (fun {_ _} => (nodeRep_split q1 q2 _).2))⟩
  refine ⟨?_, ?_⟩
  · iintro ⟨HN, #Hp⟩
    icases hm.1 $$ HN with ⟨HN1, HN2⟩
    isplitl [HN1]
    · iframe; iframe #
    · iframe; iframe #
  · iintro ⟨⟨HN1, #Hp⟩, ⟨HN2, -⟩⟩
    isplitl [HN1 HN2]
    · iapply hm.2; iframe
    iframe #

/-- The ghost names of the Go 1.22 matcher: its tree's state (a ghost variable, half with the
owner) and its routes (a ghost map, a pattern to its handler). -/
structure Mux22Names where
  st : GName
  r : GName

/-- The mux's lock guards `P q` (a reader `q = rfrac`, the writer `1`). -/
def mux22P (γ : Mux22Names) (mux : Loc) (q : Qp) : IProp GF :=
  iprop(∃ (S : TreeSt) (Rt : GMap GoString GoInterface),
    ghostVar γ.st q.half S ∗ ghostMapAuth γ.r q Rt ∗ treeRep (DFrac.own q) S ∗
    ⌜S.ok (muxRoot mux) ∧ routesOk Rt S ∧ ∀ e ∈ S.pats, e.2.2 ≠ interface.nil⌝)

theorem routesOk_unique (R1 R2 : GMap GoString GoInterface) (S : TreeSt)
    (h1 : routesOk R1 S) (h2 : routesOk R2 S) : R1 = R2 :=
  GMap.ext (fun k => by rw [h1 k, h2 k])

instance mux22P_fractional (γ : Mux22Names) (mux : Loc) :
    Fractional (mux22P (GF := GF) (hG := hG) γ mux) where
  fractional q1 q2 := by
    have hg := fun (x : TreeSt) => (ghostVar_half_fractional (GF := GF) γ.st x).fractional q1 q2
    have ha := fun (R : GMap GoString GoInterface) =>
      (ghostMapAuth_fractional (GF := GF) γ.r R).fractional q1 q2
    unfold mux22P
    refine ⟨?_, ?_⟩
    · iintro ⟨%S, %R, Hg, HA, Hrep, %HS⟩
      icases (hg S).1 $$ Hg with ⟨Hg1, Hg2⟩
      icases (ha R).1 $$ HA with ⟨HA1, HA2⟩
      icases (treeRep_split q1 q2 S).1 $$ Hrep with ⟨Hr1, Hr2⟩
      isplitl [Hg1 HA1 Hr1]
      · iexists S, R; iframe; ipureintro; exact HS
      · iexists S, R; iframe; ipureintro; exact HS
    · iintro ⟨⟨%S1, %R1, Hg1, HA1, Hr1, %HS1⟩, ⟨%S2, %R2, Hg2, HA2, Hr2, %HS2⟩⟩
      ihave %Hst := ghostVar_agree γ.st _ _ _ _ $$ Hg1 Hg2
      subst Hst
      have HR := routesOk_unique R1 R2 S1 HS1.2.1 HS2.2.1
      subst HR
      iexists S1, R1
      isplitl [Hg1 Hg2]
      · iapply (hg S1).2; iframe
      isplitl [HA1 HA2]
      · iapply (ha R1).2; iframe
      isplitl [Hr1 Hr2]
      · iapply (treeRep_split q1 q2 S1).2; iframe
      ipureintro; exact HS1

end defs

section wp
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]

set_option hygiene false in
/-- `wp_registerErr_lit`'s end: the lock given back with the new tree, `nil` returned. -/
local macro "reg_close" : tactic => `(tactic| (
  have hRp := routesOk_none Rt S p HS.2.1 hnew
  imod ghostVar_update_halves S' γ.st S S $$ Hv Hv0 with ⟨Hv, Hv0⟩
  imod ghost_map_insert_persist p (GoInterface.ok e) hRp $$ HA with ⟨HA, #Hel⟩
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [Hlocked Hv0 HA Hrep]
  · iframe Hlocked
    iframe #
    iunfold mux22P
    iexists S', GMap.insert p (GoInterface.ok e) Rt
    iframe
    ipureintro
    refine ⟨HS'.1, routesOk_insert Rt S S' p pp _ HS.2.1 HS'.2, fun x hx => ?_⟩
    rw [HS'.2] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hh
    · exact HS.2.2 x hx
  try wp_auto
  iapply HΦ
  iexists S', pp
  rw [HS'.2]
  iframe
  iframe #
  ipureintro; rfl))

set_option hygiene false in
/-- `wp_registerErr_lit` from the lock on (the pattern's `loc` set). -/
local macro "reg_lock" : tactic => `(tactic| (
  try wp_auto
  wp_apply sync.RWMutex.wp_Lock_guard $$ [] as ⟨Hlocked, HP⟩
  · iframe #
  iunfold mux22P at HP
  icases HP with ⟨%S0, %Rt, Hv0, HA, Hrep, %HS⟩
  ihave %Heq := ghostVar_agree γ.st _ _ _ _ $$ Hv Hv0
  subst Heq
  try wp_auto
  ipersist Hpp
  imod ownSlice_persist sl _ _ $$ Hsl with #Hsl
  ipersist pat
  ihave #Hpr : patRep (GF := GF) (hG := hG) pp p $$ []
  · iunfold patRep; iexists sl, _; iframe #
  rw [show ∀ x b, (RecV BAnon x b : val) = #(func.mk BAnon x b) from
    fun x b => by rw [go.intoVal_unfold GoFunc]]
  wp_apply (wp_possiblyConflictingPatterns_lit (structFieldRef net.http.ServeMux go!"index" mux) pp _
    (S.pats.map Prod.fst) p hp) $$ [Hidx] as Hidx
  · iframe; iframe #
    iunfold noConflictFn
    imodintro
    iintro %pp2
    imodintro
    iintro %Φ' Hpi HΦ'
    iunfold pidx at Hpi
    icases Hpi with ⟨%q2, #Hq2, %hq2⟩
    simp only [go.intoVal_unfold GoFunc]
    wp_call
    try wp_auto
    wp_apply (wp_conflictsWith_lit pp pp2 p q2 hp hq2.1 (fun he => hnew (he ▸ hq2.2))) $$ []
    · iframe #
    try wp_auto
    iapply HΦ'
    ipureintro; trivial
  try wp_auto
  wp_apply (wp_tree_addPattern (muxRoot mux) S p pp (GoInterface.ok e) ms HS.1 hp hnew) $$ [Hrep]
    as ⟨%S', Hrep, %HS'⟩
  · iframe; iframe #
  try wp_auto
  wp_apply (wp_index_addPattern _ pp _ p hp) $$ [Hidx] as Hidx
  · iframe; iframe #
  try wp_auto
  reg_close))

set_option hygiene false in
/-- `wp_registerErr_lit` from `parsePattern` on. -/
local macro "reg_main" : tactic => `(tactic| (
  wp_apply wp_parsePattern_lit wp_IndexAny wp_IndexByte wp_PathUnescape p hp $$ []
    as %pp %sl ⟨Hpp, Hsl, Hcap⟩
  · iframe #
  try wp_auto
  wp_apply wp_Caller as %pc %file %line %ok -
  try wp_auto
  cases ok
  · try wp_auto
    reg_lock
  · try wp_auto
    wp_apply (wp_slice_literal (l := [_, _]))
    isplitr
    · ipureintro; rfl
    iintro %sla ⟨Hsla, -⟩
    try wp_auto
    wp_apply EtcdGrove.fmt.wp_Sprintf_pure wp_Sprintf go!"%s:%d"
      [.dir none _root_.Perennial.fmt.verb_s, .lit go!":", .dir none _root_.Perennial.fmt.verb_d] _ _
      [.str file, .int (sint.Z line)] _ (by fmt_encode) (by fmt_fits)
      (.str _ _ _ (.int _ _ _ _ (by constructor) .nil)) $$ [Hsla] as %r -
    · iframe
    reg_lock))

set_option maxRecDepth 20000 in
/-- `mux.registerErr(p, h)` by the owner (the other half of the tree's state, the index) of a
literal pattern not yet registered and a non-nil handler: `nil`, `p` registered for `h`. -/
theorem wp_registerErr_lit (wp_IndexAny : strings.IndexAny.spec (GF := GF) (hG := hG))
    (wp_IndexByte : strings.IndexByte.spec (GF := GF) (hG := hG))
    (wp_PathUnescape : net.url.PathUnescape.spec (GF := GF) (hG := hG))
    (wp_Caller : runtime.Caller.spec (GF := GF) (hG := hG))
    (wp_Sprintf : fmt.Sprintf.spec (GF := GF) (hG := hG))
    (mux : Loc) (γ : Mux22Names) (S : TreeSt) (ms : w64) (p : List w8) (h : GoInterface)
    (hp : litPat p) (hnew : p ∉ S.pats.map Prod.fst) (hh : h ≠ interface.nil)
    (hfn : ∀ v, h = interface.mkOk net.http.HandlerFunc.ty v → ∃ fv : GoFunc, v = #fv ∧ fv ≠ func.nil) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isPkgInit (PROP := IProp GF) pkg_id.strings ∗
        isPkgInit (PROP := IProp GF) pkg_id.net.url ∗ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗
        sync.isRWMutexGuard (structFieldRef net.http.ServeMux go!"mu" mux) (mux22P γ mux) ∗
        ghostVar γ.st (1 : Qp).half S ∗
        idxRep (structFieldRef net.http.ServeMux go!"index" mux) (S.pats.map Prod.fst) ∗
        globalAddr net.http.maxSlice ↦□ ms }}
      (App (App (Val (mux @!! go.GoType.PointerType net.http.ServeMux.ty @!! go!"registerErr"))
        (Val #p)) (Val #h))
    {{ RET #(interface.nil : GoInterface); ∃ (S' : TreeSt) (pp : Loc), ghostVar γ.st (1 : Qp).half S' ∗
        idxRep (structFieldRef net.http.ServeMux go!"index" mux) (S'.pats.map Prod.fst) ∗
        p ↪[γ.r]□ h ∗ ⌜S'.pats = (p, pp, h) :: S.pats⌝ }} := by
  wp_start as ⟨#Hguard, Hv, Hidx, #Hms⟩
  try wp_auto
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  have hpne : p ≠ [] := by intro h0; rw [h0] at hp; simp [litPat] at hp
  rw [decide_eq_false hpne]
  obtain ⟨e, rfl⟩ : ∃ e, h = GoInterface.ok e := by
    cases h with
    | nil => exact absurd rfl hh
    | ok e => exact ⟨e, rfl⟩
  try wp_auto
  by_cases het : e.ty = net.http.HandlerFunc.ty
  · obtain ⟨fv, hfv, hfn0⟩ := hfn e.v (by cases e; simp_all [interface.mkOk])
    simp only [het, hfv]
    try wp_auto
    rw [decide_eq_false hfn0]
    try wp_auto
    reg_main
  · simp only [het]
    try wp_auto
    reg_main

end wp

end net.http
end Perennial

