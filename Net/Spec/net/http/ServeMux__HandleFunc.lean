/-
`(*ServeMux).HandleFunc(pattern, f)`: register `HandlerFunc(f)` for `pattern` on the mux `m`. On
the right to register there (`muxOwn m Ps`, `MuxDefs.lean`), for a literal path pattern not yet
registered (`litPattern p`, `p ∉ Ps`: Go 1.22's conflict rule is then equality, so `register` does
not panic) and a non-nil function (`HandleFunc` panics on a nil one: "http: nil handler"), it
registers it: the right now covers `p :: Ps`, and the mux routes `p` to `HandlerFunc(f)`
(`muxRoute`, persistent). Over both of the model's muxes (`use121`). `Handle.spec`'s shape, for a
mux of the program's own (`NewServeMux`) and a function; httpdriver (2026-11-24), phase 7's S5
item 4. Lean-first.
-/
module

public import Net.Proof.net.http.MuxDefs
public import Net.Proof.net.http.PkgInit

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.http

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

/-- See the file header. -/
abbrev ServeMux.HandleFunc.spec : Prop :=
  ∀ (m : Loc) (Ps : List GoString) (p : GoString) (f : GoFunc),
    litPattern p → p ∉ Ps → f ≠ func.nil →
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ muxOwn (GF := GF) (hG := hG) m Ps }}
    (App (App (Val #(methods (go.GoType.PointerType net.http.ServeMux.ty) go!"HandleFunc" #m))
      (Val #p)) (Val #f))
  {{ RET #(); muxOwn (GF := GF) (hG := hG) m (p :: Ps) ∗
      muxRoute (GF := GF) (hG := hG) m p (interface.mkOk net.http.HandlerFunc.ty #f) }}

end spec
end net.http
end Perennial
