/-
`generation.isRecreatedAt` (`key_index.go`, added by etcd-io/etcd#22377): `doCompact`'s test of the
generation after one whose tombstone is at the compaction revision (`Compact.lean`, `RecreatedAt`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Compact

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

/-- `g.isRecreatedAt(rev)` of a non-nil `g`: whether the generation has a revision and its first
one has main `rev` (`RecreatedAt`: the key was put, creating the generation, in revision `rev`).
A read, at any fraction. -/
abbrev mvcc.generation.isRecreatedAt.spec : Prop :=
  ∀ (g : Loc) (gv : generation) (gm : mvcc.Gen) (dq : DFrac) (rev : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        ⌜g ≠ null⌝ ∗ g ↦{dq} gv ∗ mvcc.ownGen gv gm dq }}
      (App (Val (g @!! go.GoType.PointerType generation.ty @!! go!"isRecreatedAt")) (Val #rev))
    {{ RET #(decide (mvcc.RecreatedAt rev gm)); g ↦{dq} gv ∗ mvcc.ownGen gv gm dq }}

end spec

end EtcdGrove
end Perennial
