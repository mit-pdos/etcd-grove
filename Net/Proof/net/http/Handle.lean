/-
`http.Handle`'s spec (`Net/Spec/net/http/Handle.lean`), proved over the real `ServeMux`
(`MuxServe.lean`'s `wp_Handle_lit`: `register` on Go 1.22's matcher, `mux121.handle` on Go 1.21's,
chosen by `use121`). Until 2026-11-25 an interim trust-boundary axiom. Lean-first.
-/
module

public import Net.Spec.net.http.Handle
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

theorem Handle.wp_proof (wp_Search : sort.Search.spec (GF := GF) (hG := hG))
    (wp_IndexAny : strings.IndexAny.spec (GF := GF) (hG := hG))
    (wp_IndexByte : strings.IndexByte.spec (GF := GF) (hG := hG))
    (wp_PathUnescape : net.url.PathUnescape.spec (GF := GF) (hG := hG))
    (wp_Caller : runtime.Caller.spec (GF := GF) (hG := hG))
    (wp_Sprintf : fmt.Sprintf.spec (GF := GF) (hG := hG)) :
    Handle.spec (GF := GF) (hG := hG) := by
  intro Ps p h hp hnew hh hfn
  iintro %Φ ⟨#Hpkg, Hown⟩ HΦ
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
  iapply (wp_Handle_lit wp_Search wp_IndexAny wp_IndexByte wp_PathUnescape wp_Caller wp_Sprintf
    (globalAddr net.http.defaultServeMux) Ps p h hp hnew hh hfn) $$ [Hown]
  · iframe #; iexact Hown
  inext
  iintro ⟨Hown, #Hr⟩
  iapply HΦ
  iunfold muxOwn; iunfold muxRoute
  iframe; iframe #

end proof

end net.http
end Perennial
