/-
net/http's Go 1.21 matcher (`servemux121.go`, the `ServeMux`'s `mux121`, used when `GODEBUG`
sets `httpmuxgo121=1`): its state, registration and the dispatch of a registered path.

* `Mux121St`: the physical state (the map `m`, the sorted slice `es` of the patterns ending in
  `/`, its entries, the registered patterns). Countable, for a ghost variable.
* `rep121 dq mux st M`: the matcher at `mux` is in state `st` with map contents `M`, at fraction
  `dq`: every pattern begins with `/` (so `hosts` stays `false`), an entry's pattern is its key,
  `es` sorted (`sortedDesc`).
* `wp_mux121_match_found`, `wp_mux121_shouldRedirect_found` (the lock held at `dq`, a registered
  path: its own entry, no redirect), `wp_appendSorted` (over `sort.Search`'s spec: the entry
  inserted where the order puts it).
* `mux121P γ mux q`: what the matcher's `RWMutex` guards (fractional, `mux121P_fractional`): the
  state (a ghost variable, the owner holding the other half), the routes (a ghost map, a pattern
  to its handler; `p ↪[γ.r]□ h` once registered) and `rep121`. `mux121_init` makes it from the
  zero value (the guard, the reader slots in a thread pool).
* `wp_mux121_handle` (the owner, under the guard), `wp_mux121_handler`,
  `wp_mux121_redirectToPathSlash`, `wp_mux121_findHandler_connect` (a reader slot, a registered
  path; for a `CONNECT`, the request's fields `connReqFields`): registration, and dispatch of a
  registered path to its handler.
-/
module

public import Net.GeneratedProof.net.http
public import Perennial.Spec.sort.Search
public import Perennial.Proof.sync.Results
public import Perennial.Proof.sync.RWMutexThreads
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.perennial.goose.model.strings (wp_string_len)

namespace net.http

section st
variable [GooseExts]

/-- The physical state of a `serveMux121` (see the file header). -/
structure Mux121St where
  m : GoMap
  es : GoSlice
  ents : List net.http.muxEntry
  pats : List GoString

instance muxEntry.countable : Pos.Countable net.http.muxEntry :=
  .ofInjective (fun e => Pos.Countable.encode (e.h', e.pattern'))
    (by rintro ⟨a, b⟩ ⟨c, d⟩ h; have h := Pos.encode_inj h; simp_all)

instance Mux121St.countable : Pos.Countable Mux121St :=
  .ofInjective (fun st => Pos.Countable.encode (st.m, st.es, st.ents, st.pats))
    (by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h; have h := Pos.encode_inj h; simp_all)

/-- What the matcher's state says of its patterns (see the file header). -/
def Mux121St.ok (st : Mux121St) (M : GMap GoString net.http.muxEntry) : Prop :=
  (st.m = map.nil → M = ∅) ∧
  ∀ k e, M !! k = some e → e.pattern' = k ∧ k.head? = some (W8 47)

/-- `appendSorted`'s list: `append`, `copy` one place down, the new entry at `i`. -/
theorem appendSorted_list {α : Type} (ents : List α) (z e : α) (i : Nat) (hi : i < ents.length) :
    ((ents ++ [z]).take (i + 1) ++ (((subslice i (ents.length + 1) (ents ++ [z])).take
        (ents.length + 1 - (i + 1)) ++ (subslice (i + 1) (ents.length + 1) (ents ++ [z])).drop
        (ents.length + 1 - i)) ++ (ents ++ [z]).drop (ents.length + 1))).set i e =
      ents.take i ++ e :: ents.drop i := by
  have h1 : (ents ++ [z]).take (i + 1) = ents.take (i + 1) := by
    rw [List.take_append_of_le_length (by omega)]
  have h2 : (subslice i (ents.length + 1) (ents ++ [z])).take (ents.length + 1 - (i + 1)) =
      ents.drop i := by
    have ha : (ents ++ [z]).take (ents.length + 1) = ents ++ [z] :=
      List.take_of_length_le (by simp)
    have hb : (ents ++ [z]).drop i = ents.drop i ++ [z] :=
      List.drop_append_of_le_length (by omega)
    have hc : ents.length + 1 - (i + 1) = (ents.drop i).length := by simp
    simp only [subslice]
    rw [ha, hb, hc, List.take_left]
  have h3 : (subslice (i + 1) (ents.length + 1) (ents ++ [z])).drop (ents.length + 1 - i) = [] := by
    simp only [subslice]; apply List.drop_eq_nil_of_le; simp; omega
  have h4 : (ents ++ [z]).drop (ents.length + 1) = [] := by
    apply List.drop_eq_nil_of_le; simp
  rw [h1, h2, h3, h4, List.append_nil, List.append_nil]
  rw [List.set_append_left _ _ (by simp; omega)]
  have h5 : ents.take (i + 1) = ents.take i ++ [ents[i]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl
  rw [h5, List.set_append_right _ _ (by simp; omega)]
  have h6 : i - (ents.take i).length = 0 := by simp; omega
  rw [h6]
  simp

/-- A pattern's length as `appendSorted` compares it (`len`, a signed `int`). -/
def plen (x : net.http.muxEntry) : Int := sint.Z (W64 (x.pattern'.length : Int))

/-- `es` sorted from the longest pattern to the shortest (`appendSorted`'s order). -/
def sortedDesc (ents : List net.http.muxEntry) : Prop :=
  ents.Pairwise (fun a b => plen b ≤ plen a)

/-- `appendSorted`'s search predicate: the `k`-th entry is shorter than `e`. -/
def sortF (ents : List net.http.muxEntry) (e : net.http.muxEntry) (k : Int) : Bool :=
  match ents[k.toNat]? with
  | some x => decide (plen x < plen e)
  | none => false

theorem sortedDesc_insert (ents : List net.http.muxEntry) (e : net.http.muxEntry) (i : Nat)
    (hs : sortedDesc ents) (hlo : ∀ x ∈ ents.take i, plen e ≤ plen x)
    (hhi : ∀ x ∈ ents.drop i, plen x ≤ plen e) :
    sortedDesc (ents.take i ++ e :: ents.drop i) := by
  unfold sortedDesc at *
  rw [← List.take_append_drop i ents] at hs
  rw [List.pairwise_append] at hs ⊢
  obtain ⟨h1, h2, h3⟩ := hs
  refine ⟨h1, List.pairwise_cons.mpr ⟨hhi, h2⟩, ?_⟩
  intro a ha b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact hlo a ha
  · exact h3 a ha b hb

theorem sortF_lo (ents : List net.http.muxEntry) (e : net.http.muxEntry) (m : Nat)
    (h : ∀ k : Int, 0 ≤ k ∧ k < m → sortF ents e k = false) :
    ∀ x ∈ ents.take m, plen e ≤ plen x := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  rw [List.length_take] at hj
  have hf := h (j : Int) ⟨by omega, by omega⟩
  simp only [sortF, Int.toNat_natCast, List.getElem?_eq_getElem (show j < ents.length by omega),
    decide_eq_false_iff_not] at hf
  rw [List.getElem_take]; omega

theorem sortF_hi (ents : List net.http.muxEntry) (e : net.http.muxEntry) (m : Nat)
    (hs : sortedDesc ents) (hm : m < ents.length) (hf : sortF ents e m = true) :
    ∀ x ∈ ents.drop m, plen x ≤ plen e := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  rw [List.length_drop] at hj
  simp only [sortF, Int.toNat_natCast, List.getElem?_eq_getElem hm, decide_eq_true_eq] at hf
  rw [List.getElem_drop]
  by_cases hj0 : j = 0
  · subst hj0; simp only [Nat.add_zero]; omega
  · have := List.pairwise_iff_getElem.mp hs m (m + j) hm (by omega) (by omega)
    omega

end st

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]

/-- The matcher at `mux` in state `st`, at `dq` (see the file header). -/
def rep121 (dq : DFrac) (mux : Loc) (st : Mux121St) (M : GMap GoString net.http.muxEntry) :
    IProp GF :=
  iprop(structFieldRef net.http.serveMux121 go!"m" mux ↦{dq} st.m ∗
    structFieldRef net.http.serveMux121 go!"es" mux ↦{dq} st.es ∗
    structFieldRef net.http.serveMux121 go!"hosts" mux ↦{dq} false ∗
    st.es ↦*{dq} st.ents ∗ ownSliceCap net.http.muxEntry st.es dq ∗
    ⌜st.ok M ∧ sortedDesc st.ents⌝ ∗
    (if st.m = map.nil then True else st.m ↦${dq} M))

/-- `mux.match(path)` of a registered path: its entry. -/
theorem wp_mux121_match_found (mux : Loc) (dq : DFrac) (st : Mux121St) (M : GMap GoString net.http.muxEntry)
    (path : GoString) (e : net.http.muxEntry) (he : M !! path = some e) :
    {{ rep121 (GF := GF) (hG := hG) dq mux st M }}
      (App (Val (mux @!! go.GoType.PointerType net.http.serveMux121.ty @!! go!"match")) (Val #path))
    {{ RET (PairV #e.h' #path); rep121 dq mux st M }} := by
  by_cases hm : st.m = map.nil
  · simp only [rep121]
    wp_start as ⟨Hm, Hes, Hh, Hents, Hcap, %Hok, HM⟩
    have hf : False := by rw [Hok.1.1 hm] at he; simp at he
    exact hf.elim
  simp only [rep121, hm, ↓reduceIte]
  wp_start as ⟨Hm, Hes, Hh, Hents, Hcap, %Hok, HM⟩
  wp_auto
  wp_apply wp_map_lookup2 go.string net.http.muxEntry.ty st.m M path dq $$ HM with HM
  rw [he]
  simp only [Option.getD_some, Option.isSome_some, decide_true]
  wp_auto
  rw [(Hok.1.2 path e he).1]
  iapply HΦ
  iframe
  ipureintro; exact Hok

/-- `mux.shouldRedirectRLocked(host, path)` of a registered path: no redirect. -/
theorem wp_mux121_shouldRedirect_found (mux : Loc) (dq : DFrac) (st : Mux121St)
    (M : GMap GoString net.http.muxEntry) (host path : GoString) (e : net.http.muxEntry)
    (he : M !! path = some e) :
    {{ rep121 (GF := GF) (hG := hG) dq mux st M }}
      (App (App (Val (mux @!! go.GoType.PointerType net.http.serveMux121.ty @!!
        go!"shouldRedirectRLocked")) (Val #host)) (Val #path))
    {{ RET #false; rep121 dq mux st M }} := by
  by_cases hm : st.m = map.nil
  · simp only [rep121]
    wp_start as ⟨Hm, Hes, Hh, Hents, Hcap, %Hok, HM⟩
    have hf : False := by rw [Hok.1.1 hm] at he; simp at he
    exact hf.elim
  simp only [rep121, hm, ↓reduceIte]
  wp_start as ⟨Hm, Hes, Hh, Hents, Hcap, %Hok, HM⟩
  wp_auto
  wp_apply wp_slice_literal (V := GoString) [path, host ++ path]
  isplitr
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_auto
  ihave HI : (∃ cv : GoString, "i" ∷ i_ptr ↦ W64 0 ∗ "c" ∷ c_ptr ↦ cv : IProp GF) $$ [i c]
  · iexists _; iframe
  wp_for HI
  try wp_auto
  have hsz : go.arrayLiteralSize [KeyedElement none (ElementExpression go.string #path),
      KeyedElement none (ElementExpression go.string #(host ++ path))] = 2 := rfl
  rw [ite_eq_left (show decide (sint.Z (W64 0) < sint.Z (W64 (go.arrayLiteralSize _))) = true by rw [hsz]; decide)]
  wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 0)) [path, host ++ path] _ path (by decide) $$ [Hlit] with Hlit
  · iframe; ipureintro; rfl
  try wp_auto
  wp_apply wp_map_lookup2 go.string net.http.muxEntry.ty st.m M path dq $$ HM with HM
  rw [he]
  simp only [Option.isSome_some, decide_true]
  wp_auto
  wp_for_post
  try wp_auto
  iapply HΦ
  iframe
  ipureintro; exact Hok

/-- `appendSorted(es, e)`: `e` inserted where the order puts it. -/
theorem wp_appendSorted (wp_Search : sort.Search.spec (GF := GF) (hG := hG)) (es : GoSlice)
    (ents : List net.http.muxEntry) (e : net.http.muxEntry) (hs : sortedDesc ents) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ es ↦* ents ∗
        ownSliceCap net.http.muxEntry es (DFrac.own 1) }}
      (App (App (Val (@! net.http.appendSorted)) (Val #es)) (Val #e))
    {{ (s' : GoSlice), RET #s'; ∃ i, ⌜i ≤ ents.length ∧ sortedDesc (ents.take i ++ e :: ents.drop i)⌝ ∗
        s' ↦* (ents.take i ++ e :: ents.drop i) ∗ ownSliceCap net.http.muxEntry s' (DFrac.own 1) }} := by
  wp_start as ⟨Hes, Hcap⟩
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hes
  rw [show ∀ x b, (RecV BAnon x b : val) = #(func.mk BAnon x b) from
    fun x b => by rw [go.intoVal_unfold GoFunc]]
  wp_apply wp_Search _ _ (sortF ents e) iprop(es_ptr ↦ es ∗ e_ptr ↦ e ∗ es ↦* ents) $$ [es e Hes]
  · iframe
    isplitl []
    · ipureintro; word
    isplitl []
    · unfold sort.predImplements
      iintro %i
      wp_start as ⟨⟨Hesp, Hep, Hes⟩, %Hbound⟩
      wp_auto
      simp only [Hbound.1, Hbound.2, and_self, ↓reduceIte]
      list_elem ents (sint.nat i) as x
      icases ownSlice_elem_acc (sint.Z i) x es _ ents Hbound.1 Hx_lookup $$ Hes with ⟨Hx, Hclose⟩
      ihave %hxn := typedPointsto_not_null _ _ _ $$ Hx
      ihave %hen := typedPointsto_not_null _ _ _ $$ Hep
      iStructNamedPrefix Hx "X"
      iStructNamedPrefix Hep "E"
      wp_auto
      wp_apply wp_string_len as %Hl1
      wp_apply wp_string_len as %Hl2
      try wp_auto
      ihave Hx := typedPointsto_combine (sliceIndexRef net.http.muxEntry (sint.Z i) es) x
        (DFrac.own 1) hxn $$ [Xh Xpattern]
      · simp only [TypedPointsto.typedPointstoDef]; iframe
      ihave Hes := Hclose $$ Hx
      rw [show (sint.Z i).toNat = sint.nat i from rfl, list_set_lookup_self ents (sint.nat i) x Hx_lookup]
      ihave Hep := typedPointsto_combine e_ptr e (DFrac.own 1) hen $$ [Eh Epattern]
      · simp only [TypedPointsto.typedPointstoDef]; iframe
      iapply HΦ
      iframe
      ipureintro
      simp only [sortF, plen, show (sint.Z i).toNat = sint.nat i from rfl, Hx_lookup]
      try rfl
    · ipureintro
      intro a b hab hfa
      have hn : (ents.length : Int) = sint.Z es.len := by rw [Hlen.1]; word
      have ha : a.toNat < ents.length := by omega
      have hb : b.toNat < ents.length := by omega
      simp only [sortF, List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb,
        decide_eq_true_eq] at hfa ⊢
      have := List.pairwise_iff_getElem.mp hs a.toNat b.toNat ha hb (by omega)
      omega
  iintro %i ⟨⟨Hesp, Hep, Hes⟩, %Hi0, %Hfound, %Hoob, %Hlow⟩
  wp_auto
  have hn : (ents.length : Int) = sint.Z es.len := by rw [Hlen.1]; word
  have hle : sint.Z i ≤ sint.Z es.len := by
    apply Classical.byContradiction; intro hgt
    by_cases hall : ∀ k, 0 ≤ k ∧ k < sint.Z es.len → sortF ents e k = false
    · have := Hoob hall; omega
    · obtain ⟨k, hk⟩ := Classical.not_forall.mp hall
      have hk1 : 0 ≤ k ∧ k < sint.Z es.len :=
        Classical.byContradiction (fun h => hk (fun h' => absurd h' h))
      have hk2 : sortF ents e k ≠ false := fun h => hk (fun _ => h)
      exact hk2 (Hlow k ⟨hk1.1, by omega⟩)
  wp_if_destruct
  · wp_apply wp_slice_literal (V := net.http.muxEntry) [e]
    isplitr
    · ipureintro; rfl
    iintro %lit ⟨Hlit, -⟩
    wp_apply wp_slice_append (V := net.http.muxEntry) _ _ _ _ _ $$ [$Hes $Hcap $Hlit] as %sl' ⟨Hsl', Hcap', -⟩
    try wp_auto
    iapply HΦ
    iexists ents.length
    rw [List.take_of_length_le (Nat.le_refl _), List.drop_of_length_le (Nat.le_refl _)]
    iframe
    ipureintro
    refine ⟨Nat.le_refl _, ?_⟩
    have h := sortedDesc_insert ents e ents.length hs
      (sortF_lo ents e ents.length (fun k hk => Hlow k ⟨hk.1, by omega⟩))
      (by simp)
    rwa [List.take_of_length_le (Nat.le_refl _), List.drop_of_length_le (Nat.le_refl _)] at h
  · have hlt : sint.Z i < sint.Z es.len := by
      have : sint.Z i ≠ sint.Z es.len := fun h => Hif (by word)
      omega
    try wp_auto
    wp_apply wp_slice_literal (V := net.http.muxEntry) [zero_val net.http.muxEntry]
    isplitr
    · ipureintro; rfl
    iintro %lit ⟨Hlit, -⟩
    wp_apply wp_slice_append (V := net.http.muxEntry) _ _ _ _ _ $$ [$Hes $Hcap $Hlit] as %sl' ⟨Hsl', Hcap', -⟩
    ihave %Hlen' := ownSlice_len _ _ _ $$ Hsl'
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hsl'
    have hl' : sint.Z sl'.len = sint.Z es.len + 1 := by
      have := Hlen'.1; simp only [List.length_append, List.length_singleton] at this; word
    have hi1 : sint.Z (i + W64 1) = sint.Z i + 1 := by word
    try wp_auto
    rw [ite_eq_left ⟨by omega, by omega, Hwf.2⟩]
    try wp_auto
    rw [ite_eq_left ⟨by omega, by omega, Hwf.2⟩]
    try wp_auto
    wp_apply wp_slice_copy_within (V := net.http.muxEntry) sl' (ents ++ [zero_val net.http.muxEntry])
      (i + W64 1) sl'.len i sl'.len
      ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩ $$ [$Hsl'] as %ncp ⟨-, Hsl'⟩
    try wp_auto
    ihave %HlenC := ownSlice_len _ _ _ $$ Hsl'
    try rw [ite_eq_left ⟨by omega, by omega⟩]
    wp_apply wp_store_slice_index sl' (sint.Z i) ((ents ++ [zero_val net.http.muxEntry]).take
        (sint.nat (i + W64 1)) ++ ((subslice (sint.nat i) (sint.nat sl'.len)
          (ents ++ [zero_val net.http.muxEntry])).take (sint.nat sl'.len - sint.nat (i + W64 1)) ++
        (subslice (sint.nat (i + W64 1)) (sint.nat sl'.len) (ents ++ [zero_val net.http.muxEntry])).drop
          (sint.nat sl'.len - sint.nat i)) ++ (ents ++ [zero_val net.http.muxEntry]).drop (sint.nat sl'.len))
      e $$ [Hsl'] as Hsl'
    · iframe; ipureintro; refine ⟨by omega, ?_⟩; rw [HlenC.1]; word
    try wp_auto
    have hfin : ((ents ++ [zero_val net.http.muxEntry]).take
        (sint.nat (i + W64 1)) ++ ((subslice (sint.nat i) (sint.nat sl'.len)
          (ents ++ [zero_val net.http.muxEntry])).take (sint.nat sl'.len - sint.nat (i + W64 1)) ++
        (subslice (sint.nat (i + W64 1)) (sint.nat sl'.len) (ents ++ [zero_val net.http.muxEntry])).drop
          (sint.nat sl'.len - sint.nat i)) ++ (ents ++ [zero_val net.http.muxEntry]).drop (sint.nat sl'.len)).set (sint.Z i).toNat e =
        ents.take (sint.nat i) ++ e :: ents.drop (sint.nat i) := by
      have ha : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      have hb : sint.nat sl'.len = ents.length + 1 := by word
      rw [show (sint.Z i).toNat = sint.nat i from rfl, ha, hb]
      simpa only [List.append_assoc] using
        appendSorted_list ents (zero_val net.http.muxEntry) e (sint.nat i) (by word)
    iapply HΦ
    iexists sint.nat i
    isplitr
    · ipureintro
      refine ⟨by word, sortedDesc_insert ents e (sint.nat i) hs
        (sortF_lo ents e (sint.nat i) (fun k hk => Hlow k ⟨hk.1, by word⟩))
        (sortF_hi ents e (sint.nat i) hs (by word) ?_)⟩
      have := Hfound hlt
      rwa [show sint.Z i = ((sint.nat i : Nat) : Int) by word] at this
    rw [← hfin]
    iframe

/-- The ghost names of a `serveMux121`: its state (a ghost variable, half with the owner) and its
routes (a ghost map, a pattern to its handler). -/
structure Mux121Names where
  st : GName
  r : GName

/-- The map's contents `M` are the routes `R`, each entry its pattern and handler. -/
def mapOfRoutes (M : GMap GoString net.http.muxEntry) (R : GMap GoString GoInterface) : Prop :=
  ∀ k, M !! k = (R !! k).map (fun h => ⟨h, k⟩)

/-- The matcher's lock guards `P q` (a reader `q = rfrac`, the writer `1`). -/
def mux121P (γ : Mux121Names) (mux : Loc) (q : Qp) : IProp GF :=
  iprop(∃ (st : Mux121St) (R : GMap GoString GoInterface) (M : GMap GoString net.http.muxEntry),
    ghostVar γ.st q.half st ∗ ghostMapAuth γ.r q R ∗ rep121 (DFrac.own q) mux st M ∗
    ⌜mapOfRoutes M R ∧ (∀ k, k ∈ st.pats ↔ (R !! k).isSome) ∧
      ∀ k v, R !! k = some v → v ≠ interface.nil⌝)

/-- After `handle` inserts `p`: the state's facts for the new map, routes and patterns. -/
theorem mux121_insert_ok (st : Mux121St) (M : GMap GoString net.http.muxEntry)
    (R : GMap GoString GoInterface) (p : GoString) (h : GoInterface) (m' : GoMap) (es' : GoSlice)
    (ents' : List net.http.muxEntry) (hp : p.head? = some (W8 47)) (hm' : m' ≠ map.nil)
    (Hok : st.ok M) (HMR : mapOfRoutes M R ∧ ∀ k, k ∈ st.pats ↔ (R !! k).isSome) :
    Mux121St.ok { m := m', es := es', ents := ents', pats := p :: st.pats }
        (GMap.insert p { h' := h, pattern' := p } M) ∧
      mapOfRoutes (GMap.insert p { h' := h, pattern' := p } M) (GMap.insert p h R) ∧
      ∀ k, k ∈ p :: st.pats ↔ ((GMap.insert p h R) !! k).isSome := by
  refine ⟨⟨fun h0 => absurd h0 hm', ?_⟩, ?_, ?_⟩
  · intro k e he
    rw [GMap.lookup_insert_eq_iff] at he
    by_cases hk : p = k
    · subst hk; simp only [↓reduceIte, Option.some.injEq] at he; subst he; exact ⟨rfl, hp⟩
    · simp only [hk, ↓reduceIte] at he; exact Hok.2 k e he
  · intro k
    rw [GMap.lookup_insert_eq_iff, GMap.lookup_insert_eq_iff]
    by_cases hk : p = k
    · subst hk; simp
    · simp only [hk, ↓reduceIte]; exact HMR.1 k
  · intro k
    rw [GMap.lookup_insert_eq_iff, List.mem_cons]
    by_cases hk : p = k
    · subst hk; simp
    · simp only [hk, ↓reduceIte, HMR.2 k]
      constructor
      · rintro (h0 | h0)
        · exact absurd h0.symm hk
        · exact h0
      · intro h0; exact Or.inr h0

set_option hygiene false in
/-- The end of `wp_mux121_handle`, once the lock is given back with the new state. -/
local macro "mux121_close " mt:term:max et:term:max nt:term:max hs:term:max : tactic => `(tactic| (
  ihave %hm'n := ownMap_not_nil _ _ _ $$ HM
  have Hfacts := mux121_insert_ok st M R p (GoInterface.ok hi) $mt $et $nt hp hm'n Hok.1 ⟨HMR.1, HMR.2.1⟩
  imod ghostVar_update_halves { m := $mt, es := $et, ents := $nt, pats := p :: st.pats }
    γ.st st st $$ Hv Hv0 with ⟨Hv, Hv0⟩
  imod ghost_map_insert_persist p (GoInterface.ok hi) hRp $$ HA with ⟨HA, #Hel⟩
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [Hlocked Hv0 HA Hm Hes Hh Hents Hcap HM]
  · iframe Hlocked
    iunfold mux121P
    iexists { m := $mt, es := $et, ents := $nt, pats := p :: st.pats },
      GMap.insert p (GoInterface.ok hi) R, GMap.insert p { h' := GoInterface.ok hi, pattern' := p } M
    iframe
    iunfold rep121
    simp only [hm'n, ↓reduceIte]
    iframe
    ipureintro
    refine ⟨⟨Hfacts.1, $hs⟩, Hfacts.2.1, Hfacts.2.2, fun k v hv => ?_⟩
    rw [GMap.lookup_insert_eq_iff] at hv
    by_cases hk : p = k
    · simp only [hk, ↓reduceIte, Option.some.injEq] at hv; subst hv; exact hh
    · simp only [hk, ↓reduceIte] at hv; exact HMR.2.2 k v hv
  try wp_auto
  iapply HΦ
  iexists { m := $mt, es := $et, ents := $nt, pats := p :: st.pats }
  iframe Hv
  iframe #
  ipureintro; rfl))

set_option hygiene false in
/-- `wp_mux121_handle` from the map's insertion on (the map at `mt`). -/
local macro "mux121_rest " mt:term:max : tactic => `(tactic| (
  wp_apply (wp_mapInsert (K := GoString) (V := net.http.muxEntry) go.string $mt _ p
    { h' := GoInterface.ok hi, pattern' := p }) $$ HM as HM
  try wp_auto
  wp_apply wp_string_len as %Hpl
  try wp_auto
  have hlen1 : 1 ≤ p.length := by cases p with | nil => exact absurd rfl hpne | cons _ _ => simp
  have hl0 : 0 ≤ sint.Z (W64 (p.length : Int) - W64 1) := by word
  have hidx : sint.nat (W64 (p.length : Int) - W64 1) = p.length - 1 := by word
  obtain ⟨c, hc⟩ : ∃ c, p[p.length - 1]? = some c := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hc0 : p[0]? = some (W8 47) := by
    cases p with | nil => exact absurd rfl hpne | cons a l => simp at hp ⊢; exact hp
  simp only [hl0, ↓reduceIte, hidx, hc]
  try wp_auto
  wp_if_destruct
  · try wp_auto
    wp_apply wp_appendSorted wp_Search st.es st.ents { h' := GoInterface.ok hi, pattern' := p } Hok.2
      $$ [Hents Hcap] as %es' ⟨%i, %Hi, Hents, Hcap⟩
    · iframe
    try wp_auto
    simp only [hc0]
    try wp_auto
    mux121_close $mt es' (st.ents.take i ++ { h' := GoInterface.ok hi, pattern' := p } :: st.ents.drop i) Hi.2
  · try wp_auto
    simp only [hc0]
    try wp_auto
    mux121_close $mt st.es st.ents Hok.2))

/-- `rep121` splits and combines by fractions (its state fixed). -/
theorem rep121_split (q1 q2 : Qp) (mux : Loc) (st : Mux121St) (M : GMap GoString net.http.muxEntry) :
    rep121 (GF := GF) (hG := hG) (DFrac.own (q1 + q2)) mux st M ⊣⊢
      rep121 (DFrac.own q1) mux st M ∗ rep121 (DFrac.own q2) mux st M := by
  have hpt : ∀ {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V),
      (l ↦{DFrac.own (q1 + q2)} v : IProp GF) ⊣⊢ l ↦{DFrac.own q1} v ∗ l ↦{DFrac.own q2} v :=
    fun l v => (typedPointsto_dfractional (GF := GF) l v).dfractional (DFrac.own q1) (DFrac.own q2)
  have hsl : (st.es ↦*{DFrac.own (q1 + q2)} st.ents : IProp GF) ⊣⊢
      st.es ↦*{DFrac.own q1} st.ents ∗ st.es ↦*{DFrac.own q2} st.ents :=
    (ownSlice_dfractional (GF := GF) st.es st.ents).dfractional (DFrac.own q1) (DFrac.own q2)
  have hcap : (ownSliceCap (GF := GF) net.http.muxEntry st.es (DFrac.own (q1 + q2))) ⊣⊢
      ownSliceCap net.http.muxEntry st.es (DFrac.own q1) ∗
        ownSliceCap net.http.muxEntry st.es (DFrac.own q2) :=
    (ownSliceCap_dfractional (GF := GF) (V := net.http.muxEntry) st.es).dfractional
      (DFrac.own q1) (DFrac.own q2)
  have hmap := (ownMap_fractional (GF := GF) st.m M).fractional q1 q2
  unfold rep121
  by_cases hm : st.m = map.nil
  · simp only [hm, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · iintro ⟨Hm, Hes, Hh, Hents, Hcap, %Hok, -⟩
      icases (hpt _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
      icases (hpt _ _).1 $$ Hes with ⟨Hes1, Hes2⟩
      icases (hpt _ _).1 $$ Hh with ⟨Hh1, Hh2⟩
      icases hsl.1 $$ Hents with ⟨Hents1, Hents2⟩
      icases hcap.1 $$ Hcap with ⟨Hcap1, Hcap2⟩
      isplitl [Hm1 Hes1 Hh1 Hents1 Hcap1]
      · iframe; ipureintro; exact ⟨Hok, trivial⟩
      · iframe; ipureintro; exact ⟨Hok, trivial⟩
    · iintro ⟨⟨Hm1, Hes1, Hh1, Hents1, Hcap1, %Hok, -⟩, ⟨Hm2, Hes2, Hh2, Hents2, Hcap2, -, -⟩⟩
      isplitl [Hm1 Hm2]
      · iapply (hpt _ _).2; iframe
      isplitl [Hes1 Hes2]
      · iapply (hpt _ _).2; iframe
      isplitl [Hh1 Hh2]
      · iapply (hpt _ _).2; iframe
      isplitl [Hents1 Hents2]
      · iapply hsl.2; iframe
      isplitl [Hcap1 Hcap2]
      · iapply hcap.2; iframe
      ipureintro; exact ⟨Hok, trivial⟩
  · simp only [hm, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · iintro ⟨Hm, Hes, Hh, Hents, Hcap, %Hok, HM⟩
      icases (hpt _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
      icases (hpt _ _).1 $$ Hes with ⟨Hes1, Hes2⟩
      icases (hpt _ _).1 $$ Hh with ⟨Hh1, Hh2⟩
      icases hsl.1 $$ Hents with ⟨Hents1, Hents2⟩
      icases hcap.1 $$ Hcap with ⟨Hcap1, Hcap2⟩
      icases hmap.1 $$ HM with ⟨HM1, HM2⟩
      isplitl [Hm1 Hes1 Hh1 Hents1 Hcap1 HM1]
      · iframe; ipureintro; exact Hok
      · iframe; ipureintro; exact Hok
    · iintro ⟨⟨Hm1, Hes1, Hh1, Hents1, Hcap1, %Hok, HM1⟩, ⟨Hm2, Hes2, Hh2, Hents2, Hcap2, -, HM2⟩⟩
      isplitl [Hm1 Hm2]
      · iapply (hpt _ _).2; iframe
      isplitl [Hes1 Hes2]
      · iapply (hpt _ _).2; iframe
      isplitl [Hh1 Hh2]
      · iapply (hpt _ _).2; iframe
      isplitl [Hents1 Hents2]
      · iapply hsl.2; iframe
      isplitl [Hcap1 Hcap2]
      · iapply hcap.2; iframe
      isplitr
      · ipureintro; exact Hok
      iapply hmap.2; iframe

theorem mapOfRoutes_unique (M1 M2 : GMap GoString net.http.muxEntry) (R : GMap GoString GoInterface)
    (h1 : mapOfRoutes M1 R) (h2 : mapOfRoutes M2 R) : M1 = M2 :=
  GMap.ext (fun k => by rw [h1 k, h2 k])

instance mux121P_fractional (γ : Mux121Names) (mux : Loc) :
    Fractional (mux121P (GF := GF) (hG := hG) γ mux) where
  fractional q1 q2 := by
    have hg := fun (x : Mux121St) => (ghostVar_half_fractional (GF := GF) γ.st x).fractional q1 q2
    have ha := fun (R : GMap GoString GoInterface) =>
      (ghostMapAuth_fractional (GF := GF) γ.r R).fractional q1 q2
    unfold mux121P
    refine ⟨?_, ?_⟩
    · iintro ⟨%st, %R, %M, Hg, HA, Hrep, %HMR⟩
      icases (hg st).1 $$ Hg with ⟨Hg1, Hg2⟩
      icases (ha R).1 $$ HA with ⟨HA1, HA2⟩
      icases (rep121_split q1 q2 mux st M).1 $$ Hrep with ⟨Hr1, Hr2⟩
      isplitl [Hg1 HA1 Hr1]
      · iexists st, R, M; iframe; ipureintro; exact HMR
      · iexists st, R, M; iframe; ipureintro; exact HMR
    · iintro ⟨⟨%st1, %R1, %M1, Hg1, HA1, Hr1, %HMR1⟩, ⟨%st2, %R2, %M2, Hg2, HA2, Hr2, %HMR2⟩⟩
      ihave %Hst := ghostVar_agree γ.st _ _ _ _ $$ Hg1 Hg2
      subst Hst
      ihave %HR := ghostMapAuth_agree γ.r _ _ _ _ $$ HA1 HA2
      subst HR
      have HM := mapOfRoutes_unique M1 M2 R1 HMR1.1 HMR2.1
      subst HM
      iexists st1, R1, M1
      isplitl [Hg1 Hg2]
      · iapply (hg st1).2; iframe
      isplitl [HA1 HA2]
      · iapply (ha R1).2; iframe
      isplitl [Hr1 Hr2]
      · iapply (rep121_split q1 q2 mux st1 M1).2; iframe
      ipureintro; exact HMR1

/-- `mux.handle(p, h)` by the owner (the other half of the state): `p` registered for `h`. -/
theorem wp_mux121_handle (wp_Search : sort.Search.spec (GF := GF) (hG := hG)) (mux : Loc)
    (γ : Mux121Names) (st : Mux121St) (p : GoString) (h : GoInterface)
    (hp : p.head? = some (W8 47)) (hh : h ≠ interface.nil) (hnew : p ∉ st.pats) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        sync.isRWMutexGuard (structFieldRef net.http.serveMux121 go!"mu" mux) (mux121P γ mux) ∗
        ghostVar γ.st (1 : Qp).half st }}
      (App (App (Val (mux @!! go.GoType.PointerType net.http.serveMux121.ty @!! go!"handle"))
        (Val #p)) (Val #h))
    {{ RET #(); ∃ st' : Mux121St, ghostVar γ.st (1 : Qp).half st' ∗ p ↪[γ.r]□ h ∗
        ⌜st'.pats = p :: st.pats⌝ }} := by
  wp_start as ⟨#Hguard, Hv⟩
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hlocked, HP⟩
  iunfold mux121P at HP
  icases HP with ⟨%st0, %R, %M, Hv0, HA, Hrep, %HMR⟩
  ihave %Heq := ghostVar_agree γ.st st (1 : Qp).half st0 (1 : Qp).half $$ Hv Hv0
  subst Heq
  iunfold rep121 at Hrep
  icases Hrep with ⟨Hm, Hes, Hh, Hents, Hcap, %Hok, HM⟩
  try wp_auto
  have hpne : p ≠ [] := by intro h0; simp [h0] at hp
  rw [decide_eq_false hpne]
  try wp_auto
  obtain ⟨hi, rfl⟩ : ∃ i, h = GoInterface.ok i := by
    cases h with
    | nil => exact absurd rfl hh
    | ok i => exact ⟨i, rfl⟩
  try wp_auto
  have hRp : R !! p = none := by
    have h1 : ¬ (R !! p).isSome = true := fun h0 => hnew ((HMR.2.1 p).mpr h0)
    cases hr : R !! p with
    | none => rfl
    | some _ => simp [hr] at h1
  have hMp : M !! p = none := by rw [HMR.1 p, hRp]; rfl
  by_cases hmn : st.m = map.nil
  · irevert HM; simp only [hmn, ↓reduceIte]; iintro -
    have hM0 : M = ∅ := Hok.1.1 hmn
    try wp_auto
    wp_apply (wp_map_make1 (K := GoString) (V := net.http.muxEntry) _ _) as %m' HM
    irevert HM; rw [← hM0]; iintro HM
    try wp_auto
    mux121_rest m'
  · irevert HM; simp only [hmn, ↓reduceIte]; iintro HM
    wp_apply wp_map_lookup2 go.string net.http.muxEntry.ty st.m M p (DFrac.own 1) $$ HM with HM
    rw [hMp]
    try wp_auto
    rw [decide_eq_false hmn]
    try wp_auto
    mux121_rest st.m

/-- A reader's view of the matcher (`P rfrac`), for a registered path: its state, and the path's
entry in the map. -/
theorem mux121P_found (γ : Mux121Names) (mux : Loc) (q : Qp) (path : GoString) (h : GoInterface) :
    mux121P (GF := GF) (hG := hG) γ mux q -∗ path ↪[γ.r]□ h -∗
      ∃ (st : Mux121St) (R : GMap GoString GoInterface) (M : GMap GoString net.http.muxEntry),
        ghostVar γ.st q.half st ∗ ghostMapAuth γ.r q R ∗ rep121 (DFrac.own q) mux st M ∗
        ⌜(mapOfRoutes M R ∧ (∀ k, k ∈ st.pats ↔ (R !! k).isSome) ∧
          ∀ k v, R !! k = some v → v ≠ interface.nil) ∧ R !! path = some h ∧
          M !! path = some ⟨h, path⟩⌝ := by
  iintro HP #Hel
  iunfold mux121P at HP
  icases HP with ⟨%st, %R, %M, Hv, HA, Hrep, %HMR⟩
  ihave %HRp := ghost_map_lookup $$ HA Hel
  iexists st, R, M
  iframe
  ipureintro
  refine ⟨HMR, HRp, ?_⟩
  rw [HMR.1 path, HRp]; rfl

/-- `mux.handler(host, path)` of a registered path, by a reader (a reader slot of the matcher's
lock): the path's handler and the path. -/
theorem wp_mux121_handler (mux : Loc) (γ : Mux121Names) (host path : GoString) (h : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗
        sync.ownRWMutex (structFieldRef net.http.serveMux121 go!"mu" mux) (mux121P γ mux) ∗
        path ↪[γ.r]□ h }}
      (App (App (Val (mux @!! go.GoType.PointerType net.http.serveMux121.ty @!! go!"handler"))
        (Val #host)) (Val #path))
    {{ RET (PairV #h #path); sync.ownRWMutex (structFieldRef net.http.serveMux121 go!"mu" mux)
        (mux121P γ mux) }} := by
  wp_start as ⟨Hrw, #Hel⟩
  try wp_auto
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrw] as ⟨Hrl, HP⟩
  icases mux121P_found γ mux _ path h $$ HP Hel with ⟨%st, %R, %M, Hv, HA, Hrep, %HMR, %HRp, %HMp⟩
  iunfold rep121 at Hrep
  icases Hrep with ⟨Hm, Hes, Hh, Hents, Hcap, %Hok, HM⟩
  try wp_auto
  ihave Hrep : rep121 (DFrac.own sync.rfrac) mux st M $$ [Hm Hes Hh Hents Hcap HM]
  · iunfold rep121; iframe; ipureintro; exact Hok
  wp_apply wp_mux121_match_found mux (DFrac.own sync.rfrac) st M path ⟨h, path⟩ HMp $$ Hrep as Hrep
  try wp_auto
  obtain ⟨hi, rfl⟩ : ∃ i, h = GoInterface.ok i := by
    cases h with
    | nil => exact absurd rfl (HMR.2.2 path _ HRp)
    | ok i => exact ⟨i, rfl⟩
  try wp_auto
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hv HA Hrep] as Hrw
  · iunfold mux121P; iexists st, R, M; iframe; ipureintro; exact HMR
  try wp_auto
  iapply HΦ
  iframe

/-- `mux.redirectToPathSlash(host, path, u)` of a registered path, by a reader: no redirect. -/
theorem wp_mux121_redirectToPathSlash (mux : Loc) (γ : Mux121Names) (host path : GoString)
    (u : Loc) (h : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗
        sync.ownRWMutex (structFieldRef net.http.serveMux121 go!"mu" mux) (mux121P γ mux) ∗
        path ↪[γ.r]□ h }}
      (App (App (App (Val (mux @!! go.GoType.PointerType net.http.serveMux121.ty @!!
        go!"redirectToPathSlash")) (Val #host)) (Val #path)) (Val #u))
    {{ RET (PairV #u #false); sync.ownRWMutex (structFieldRef net.http.serveMux121 go!"mu" mux)
        (mux121P γ mux) }} := by
  wp_start as ⟨Hrw, #Hel⟩
  try wp_auto
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrw] as ⟨Hrl, HP⟩
  icases mux121P_found γ mux _ path h $$ HP Hel with ⟨%st, %R, %M, Hv, HA, Hrep, %HMR, %HRp, %HMp⟩
  try wp_auto
  wp_apply wp_mux121_shouldRedirect_found mux (DFrac.own sync.rfrac) st M host path ⟨h, path⟩ HMp
    $$ Hrep as Hrep
  try wp_auto
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hv HA Hrep] as Hrw
  · iunfold mux121P; iexists st, R, M; iframe; ipureintro; exact HMR
  try wp_auto
  iapply HΦ
  iframe

/-- The fields of a request `r` that the matcher reads for a `CONNECT` (at `dq`). -/
def connReqFields (dq : DFrac) (r u : Loc) (path rh uh : GoString) : IProp GF :=
  iprop(structFieldRef net.http.Request go!"Method" r ↦{dq} go!"CONNECT" ∗
    structFieldRef net.http.Request go!"URL" r ↦{dq} u ∗
    structFieldRef net.http.Request go!"Host" r ↦{dq} rh ∗
    structFieldRef _root_.Perennial.net.url.URL go!"Host" u ↦{dq} uh ∗
    structFieldRef _root_.Perennial.net.url.URL go!"Path" u ↦{dq} path)

/-- `mux.findHandler(r)` for a `CONNECT` to a registered path, by a reader: the path's handler. -/
theorem wp_mux121_findHandler_connect (mux : Loc) (γ : Mux121Names) (dq : DFrac) (r u : Loc)
    (path rh uh : GoString) (h : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗
        sync.ownRWMutex (structFieldRef net.http.serveMux121 go!"mu" mux) (mux121P γ mux) ∗
        path ↪[γ.r]□ h ∗ connReqFields dq r u path rh uh }}
      (App (Val (mux @!! go.GoType.PointerType net.http.serveMux121.ty @!! go!"findHandler")) (Val #r))
    {{ RET (PairV #h #path); sync.ownRWMutex (structFieldRef net.http.serveMux121 go!"mu" mux)
        (mux121P γ mux) ∗ connReqFields dq r u path rh uh }} := by
  wp_start as ⟨Hrw, #Hel, Hr⟩
  iunfold connReqFields at Hr
  icases Hr with ⟨Hmeth, Hurl, Hrh, Huh, Hpath⟩
  try wp_auto
  wp_apply wp_mux121_redirectToPathSlash mux γ uh path u h $$ [$Hrw $Hel] as Hrw
  try wp_auto
  wp_apply wp_mux121_handler mux γ rh path h $$ [$Hrw $Hel] as Hrw
  try wp_auto
  iapply HΦ
  iframe
  iunfold connReqFields
  iframe

/-- The state of a fresh matcher: no map, no sorted entries, no patterns. -/
def mux121St0 : Mux121St := { m := map.nil, es := slice.nil, ents := [], pats := [] }

/-- **A fresh matcher** (its zero value, owned): its lock's guard, its reader slots in a thread
pool of namespace `Np`, and the owner's half of its state, with no pattern. -/
theorem mux121_init {E : CoPset} (Np : Namespace) (mux : Loc) (Hb : threadBound GF ≤ 2 ^ 30) :
    ⊢ mux ↦ (zero_val net.http.serveMux121) ={E}=∗
      ∃ (γ : Mux121Names) (γp : GName),
        sync.isRWMutexGuard (structFieldRef net.http.serveMux121 go!"mu" mux) (mux121P (GF := GF) (hG := hG) γ mux) ∗
        threadPool.isThreadPool Np γp
          (sync.ownRWMutex (structFieldRef net.http.serveMux121 go!"mu" mux) (mux121P γ mux)) ∗
        ghostVar γ.st (1 : Qp).half mux121St0 := by
  iintro Hmux
  iStructNamed Hmux
  imod ghostVar_alloc (GF := GF) mux121St0 with ⟨%γs, Hv⟩
  icases (ghostVar_split_half γs 1 mux121St0).1 $$ Hv with ⟨Hv1, Hv2⟩
  imod ghost_map_alloc_empty (GF := GF) (K := GoString) (V := GoInterface) with ⟨%γr, HA⟩
  ihave HP : mux121P (GF := GF) (hG := hG) ⟨γs, γr⟩ mux 1 $$ [Hv1 HA m es hosts]
  · iunfold mux121P
    iexists mux121St0, ∅, ∅
    iframe
    iunfold rep121
    simp only [mux121St0, ↓reduceIte]
    iframe
    isplitl []
    · isplitl []
      · iapply ownSlice_nil
      isplitl []
      · iapply ownSliceCap_nil
      ipureintro
      refine ⟨⟨?_, List.Pairwise.nil⟩, trivial⟩
      unfold Mux121St.ok
      exact ⟨fun _ => rfl, fun k e he => by simp at he⟩
    ipureintro
    exact ⟨fun k => by simp, fun k => by simp, fun k v hv => by simp at hv⟩
  imod sync.init_RWMutex_threadPool (mux121P (GF := GF) (hG := hG) ⟨γs, γr⟩ mux) (E := E) Np _ Hb
    $$ HP mu with ⟨%γp, #Hguard, #Hpool⟩
  imodintro
  iexists ⟨γs, γr⟩, γp
  iframe #
  iexact Hv2

end defs

end net.http
end Perennial
