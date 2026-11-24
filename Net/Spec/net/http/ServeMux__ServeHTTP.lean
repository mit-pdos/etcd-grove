/-
`(*ServeMux).ServeHTTP(w, r)` on a frozen mux (`muxAt m (L.map Prod.fst)`, `MuxDefs.lean`: its
patterns are exactly `L`'s, each routed to its handler, `muxRoute`), each handler serving the
requests under its pattern with the protocol `P` (`handlerOk h P p`, `ProtoDefs.lean`): it is a
handler run (`servePre` to `serveDone`, `ProtoDefs.lean`). A request whose path is clean and under a
pattern goes to the handler of the longest such pattern (whose `servePre` holds: the path is under
it); the mux answers the others itself: a `301` to a path it redirects (not clean, or unrouted with
`path + "/"` a pattern), a `404` with `NotFound`'s body to the rest, which the protocol must allow for
the requests clients send (`muxNoRoute P L`). The patterns are literal paths (`litPattern`, as
`HandleFunc` registers). The machine's thread bound (`threadBound GF ≤ 2 ^ 30`): the mux's `RWMutex`
reader slots. httpdriver (2026-11-24); S5's `mux_handlerOk`, as the function's spec. Lean-first.
-/
module

public import Net.Proof.net.http.ProtoDefs
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
abbrev ServeMux.ServeHTTP.spec : Prop :=
  ∀ (m : Loc) (L : List (GoString × GoInterface)) (P : HProto GF) (pfx : GoString)
    (w : GoInterface) (r : Loc) (R : HReq) (τ : GName) (rd : GoInterface)
    (I : RespSt → IProp GF) (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF),
    (∀ ph ∈ L, litPattern ph.1) → muxNoRoute P L → (∀ x, S x ⊢ iprop(⌜x.length < 2 ^ 60⌝)) →
  iprop(⌜threadBound GF ≤ 2 ^ 30⌝ ∗ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗
      muxAt (GF := GF) (hG := hG) m (L.map Prod.fst) ∗
      ([∗list] ph ∈ L, muxRoute (GF := GF) (hG := hG) m ph.1 ph.2 ∗ handlerOk ph.2 P ph.1) ∗
      servePre P pfx w r R τ rd I S E) ⊢
    WP (App (App (Val #(methods (go.GoType.PointerType net.http.ServeMux.ty) go!"ServeHTTP" #m))
      (Val #w)) (Val #r)) {{ v, serveDone P R τ I S v }}

end spec
end net.http
end Perennial
