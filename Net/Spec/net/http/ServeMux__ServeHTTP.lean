/-
`(*ServeMux).ServeHTTP(w, r)` on a frozen mux (`muxAt m (L.map Prod.fst)`, `MuxDefs.lean`: its
patterns are exactly `L`'s, each routed to its handler, `muxRoute`), each handler serving the requests
under its pattern with the protocol `P` (`handlerOk h P p`, `ProtoDefs.lean`), on Go 1.22's matcher
(`use121 ↦□ false`: net/http's `init` under the environment premise `GodebugHttpmuxgo121Not1`, #18's
option (a)): it is a handler run (`servePre` to `serveDone`, `ProtoDefs.lean`). In `findHandler`'s
order: a request it redirects (`muxRedirect`: the path not clean, or not a pattern, not ending in `/`,
with `path + "/"` a pattern) gets a `307` (`StatusTemporaryRedirect`); otherwise the handler of the
longest pattern the path is under (`pathUnder`) serves it (that handler's `servePre` holds: the path
is under its pattern); otherwise a `404` with `NotFound`'s body. The protocol must allow the mux's own
answers to the requests clients send (`muxNoRoute P L`). The request's fields the mux reads
(`RequestURI`, `Host`, `URL`, the protocol, the method: `srvReq`) and writes (`Pattern`, `pat`,
`matches`: `reqMuxFields`) are in `servePre`. The patterns are literal paths (`litPattern`, as
`HandleFunc` registers) and clean (`pathClean`: no empty segment but the last, so no `//`; Go's
routing tree keys an empty segment like a single wildcard, `routing_tree.go`, so `//` routes like
`/{x}/`; zeldovich-proving-2's re-review, N1). The machine's thread bound (`threadBound GF ≤ 2 ^ 30`): the mux's `RWMutex`
reader slots. httpdriver (2026-11-25); S5's `mux_handlerOk`, as the function's spec. Lean-first.
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
    (∀ ph ∈ L, litPattern ph.1 ∧ pathClean ph.1) → muxNoRoute P L → (∀ x, S x ⊢ iprop(⌜x.length < 2 ^ 60⌝)) →
  iprop(⌜threadBound GF ≤ 2 ^ 30⌝ ∗ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗
      globalAddr net.http.use121 ↦□ false ∗
      muxAt (GF := GF) (hG := hG) m (L.map Prod.fst) ∗
      ([∗list] ph ∈ L, muxRoute (GF := GF) (hG := hG) m ph.1 ph.2 ∗ handlerOk ph.2 P ph.1) ∗
      servePre P pfx w r R τ rd I S E) ⊢
    WP (App (App (Val #(methods (go.GoType.PointerType net.http.ServeMux.ty) go!"ServeHTTP" #m))
      (Val #w)) (Val #r)) {{ v, serveDone P R τ I S v }}

end spec
end net.http
end Perennial
