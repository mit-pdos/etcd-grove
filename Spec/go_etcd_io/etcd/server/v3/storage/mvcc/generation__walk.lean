/-
`generation.walk` (`key_index.go`). Lean-first (no Rocq counterpart); see `Model.lean`, `Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `g.walk(f)`, with `f` deciding `p` (`walkFnSpec`): the position of the last revision
failing `p`, or `-1` (`genWalk`). A read, at any fraction. -/
abbrev mvcc.generation.walk.spec : Prop :=
  ∀ (g : Loc) (gv : generation) (gm : mvcc.Gen) (dq : DFrac) (f : GoFunc) (p : mvcc.Rev → Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      g ↦{dq} gv ∗ mvcc.ownGen gv gm dq ∗ mvcc.walkFnSpec f p }}
    (App (Val (g @!! go.GoType.PointerType generation.ty @!! go!"walk")) (Val #f))
  {{ RET #(W64 (mvcc.genWalk gm.revs p)); g ↦{dq} gv ∗ mvcc.ownGen gv gm dq }}

end spec

end EtcdGrove
end Perennial
