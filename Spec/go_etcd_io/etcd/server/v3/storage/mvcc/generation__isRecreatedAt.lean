/-
`generation.isRecreatedAt` (`key_index.go`; the fork's fix of etcd-io/etcd#22377, M2, 2026-10-28).
Lean-first (no Rocq counterpart); see `Compact.lean` (`genRecreatedAt`), `Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Defs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Compact

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `g.isRecreatedAt(rev)`: whether `g` has a revision and its first one's main is `rev`
(`genRecreatedAt`; a read, at any fraction). -/
abbrev mvcc.generation.isRecreatedAt.spec : Prop :=
  ∀ (g : Loc) (gv : generation) (gm : mvcc.Gen) (dq : DFrac) (rev : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        ⌜g ≠ null⌝ ∗ g ↦{dq} gv ∗ mvcc.ownGen gv gm dq }}
      (App (Val (g @!! go.GoType.PointerType generation.ty @!! go!"isRecreatedAt")) (Val #rev))
    {{ RET #(mvcc.genRecreatedAt rev gm); g ↦{dq} gv ∗ mvcc.ownGen gv gm dq }}

end spec

end EtcdGrove
end Perennial
