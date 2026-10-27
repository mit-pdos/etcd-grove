/-
`(*RealFIFO).Bookmark(rv)` (`the_real_fifo.go:620`): a bookmark delta queued (the informers emit them). Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the informers' FIFO).
-/
module

public import Proof.k8s_io.client_go.tools.cache.FIFODefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`f.Bookmark(rv)`**, logically atomic: a bookmark delta queued. -/
abbrev RealFIFO.Bookmark.spec : Prop :=
  ∀ (f : Loc) (γ : FifoNames) (OK : GoInterface → IProp GF)
    (rv : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isFIFO f γ OK }}
  <<{ ∀∀ q, fifoSt γ q }>>
    (App (Val (f @!! go.GoType.PointerType RealFIFO.ty @!! go!"Bookmark")) (Val #rv))
    @@ ∅
  <<{ fifoSt γ { q with items := q.items ++ [.bookmark rv] } }>>
  {{ RET #interface.nil; True }}

end spec

end cache
end EtcdGrove
end Perennial
