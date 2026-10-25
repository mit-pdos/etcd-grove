/-
`WriteTo` (the backend's `defragmentedSnapshot`, `backend.go`: the method its embedded `snapshot`
promotes; `etcd#21776`). `s.WriteTo(w)`: the defragmented snapshot's temporary database written to
`w` (bbolt's `Tx.WriteTo`). Lean-first (no Rocq counterpart); the vocabulary is `InvSnapshot.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvSnapshot

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `s.WriteTo(w)` of an open defragmented snapshot: bytes appended to the writer, after at least
one `Write` returned, an image of the snapshot's data `D` unless the error is non-nil. -/
abbrev backend.defragmentedSnapshot.WriteTo.spec : Prop :=
  ∀ (ds : Loc) (D : Data) (γ : GName × GName) (q : Qp) (w : GoInterfaceOk)
    (Wr : Bool → List w8 → IProp GF) (c : Bool) (bs₀ : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      defragSnapOpenQ ds D γ q ∗ writerOk w Wr ∗ Wr c bs₀ }}
    (App (Val (ds @!! go.GoType.PointerType defragmentedSnapshot.ty @!! go!"WriteTo"))
      (Val #(GoInterface.ok w)))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ bs : List w8, defragSnapOpenQ ds D γ q ∗ Wr true (bs₀ ++ bs) ∗
        ⌜err = GoInterface.nil → boltImage bs D⌝ }}

end spec

end EtcdGrove
end Perennial
