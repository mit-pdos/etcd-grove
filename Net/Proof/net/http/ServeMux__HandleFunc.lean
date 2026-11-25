/-
`(*ServeMux).HandleFunc`'s spec (`Net/Spec/net/http/ServeMux__HandleFunc.lean`), proved over the real
`ServeMux` (`MuxServe.lean`'s state, as `Handle.wp_proof`): on Go 1.22's matcher (`use121` false)
`mux.register(p, HandlerFunc(f))` (`wp_register_lit`); on Go 1.21's, `mux121.handleFunc(p, f)`: its
nil check (`f ≠ func.nil`), then `mux121.handle(p, HandlerFunc(f))` (`wp_mux121_handle`). Until
2026-11-25 an interim trust-boundary axiom. Lean-first.
-/
module

public import Net.Spec.net.http.ServeMux__HandleFunc
public import Perennial.Spec.sort.Search
public import Perennial.Spec.runtime.Caller

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProofMode Net

namespace net.http

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

/-- `(*ServeMux).HandleFunc` meets its spec, over `register` (Go 1.22's matcher) and
`serveMux121.handleFunc` (Go 1.21's); see the file header. -/
theorem ServeMux.HandleFunc.wp_proof (wp_Search : sort.Search.spec (GF := GF) (hG := hG))
    (wp_IndexAny : strings.IndexAny.spec (GF := GF) (hG := hG))
    (wp_IndexByte : strings.IndexByte.spec (GF := GF) (hG := hG))
    (wp_PathUnescape : net.url.PathUnescape.spec (GF := GF) (hG := hG))
    (wp_Caller : runtime.Caller.spec (GF := GF) (hG := hG))
    (wp_Sprintf : fmt.Sprintf.spec (GF := GF) (hG := hG)) :
    ServeMux.HandleFunc.spec (GF := GF) (hG := hG) := by
  intro m Ps p f hp hnew hf
  have hh : interface.mkOk net.http.HandlerFunc.ty #f ≠ interface.nil := by
    intro h0; cases h0
  have hfn : ∀ v, interface.mkOk net.http.HandlerFunc.ty #f = interface.mkOk net.http.HandlerFunc.ty v →
      ∃ fv : GoFunc, v = #fv ∧ fv ≠ func.nil := by
    intro v hv; cases hv; exact ⟨f, rfl, hf⟩
  wp_start as Hown
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hsort : isPkgInit (PROP := IProp GF) pkg_id.sort $$ []
  · iPkgInit
  ihave #Hstr : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  ihave #Hurl : isPkgInit (PROP := IProp GF) pkg_id.net.url $$ []
  · iPkgInit
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  iunfold muxOwn at Hown
  icases Hown with ⟨Hown, #Hse⟩
  iunfold muxOwnS at Hown
  icases Hown with ⟨%b, %γ, %ms, Hsh, #Hms, Hst⟩
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
      p (interface.mkOk net.http.HandlerFunc.ty #f) hp hnew hh hfn) $$ [Hv Hidx]
      as ⟨%S', %pp, Hv, Hidx, #Hel, %HS'⟩
    · iframe; iframe #
    iapply HΦ
    iunfold muxOwn; iunfold muxRoute
    isplitl [Hv Hidx]
    · isplitl [Hv Hidx]
      · iunfold muxOwnS
        iexists false, γ, ms
        iunfold muxSh
        simp only [Bool.false_eq_true, ↓reduceIte]
        iframe; iframe #
        ipureintro; rw [HS']; rfl
      · iexact Hse
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
    rw [method_unfold (t := go.GoType.PointerType net.http.serveMux121.ty)]
    wp_auto
    rw [decide_eq_false hf]
    wp_auto
    wp_apply (wp_mux121_handle wp_Search (mux121Loc m) γ.n121 st p
      (interface.mkOk net.http.HandlerFunc.ty #f) hp.1 hh hnew) $$ [Hv]
      as ⟨%st', Hv, #Hel, %Hst'⟩
    · iframe; iframe #
    iapply HΦ
    iunfold muxOwn; iunfold muxRoute
    isplitl [Hv]
    · isplitl [Hv]
      · iunfold muxOwnS
        iexists true, γ, ms
        iunfold muxSh
        simp only [↓reduceIte]
        iframe; iframe #
        ipureintro; exact Hst'
      · iexact Hse
    · iunfold muxRouteS
      iexists true, γ
      iunfold muxSh
      simp only [↓reduceIte]
      iframe #

end proof

end net.http
end Perennial
