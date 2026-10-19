/-
`WriteTo` (the backend's `snapshot`, `backend.go`: the method its embedded `*bolt.Tx` promotes;
names only). `s.WriteTo(w)`: the snapshot's database written to `w` (bbolt's `Tx.WriteTo`: two
meta pages, then the data pages read from the database file). The trust boundary (D22 S-f,
2026-10-19; an axiom in `Proof/go_etcd_io/etcd/server/v3/storage/backend/snapshot__WriteTo.lean`).
Lean-first (no Rocq counterpart); the vocabulary is `InvSnapshot.lean`.

The pre: the snapshot open over `D` (`snapOpen`, given back) and the writer's contract
(`writerOk w Wr`) at the bytes `bs₀` written so far. The post: some bytes `bs` appended (`WriteTo`
calls only `w.Write`), and, if the error is nil, `bs` a bbolt image of `D` (`boltImage`). The
count it returns is not specified (the sender only logs it).
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

/-- `s.WriteTo(w)`: bytes appended to the writer, an image of the snapshot's data unless the
error is non-nil. -/
abbrev backend.snapshot.WriteTo.spec : Prop :=
  ∀ (sp : Loc) (D : Data) (w : GoInterfaceOk) (Wr : List w8 → IProp GF) (bs₀ : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      snapOpen sp D ∗ writerOk w Wr ∗ Wr bs₀ }}
    (App (Val (sp @!! go.GoType.PointerType snapshot.ty @!! go!"WriteTo")) (Val #(GoInterface.ok w)))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ bs : List w8, snapOpen sp D ∗ Wr (bs₀ ++ bs) ∗ ⌜err = GoInterface.nil → boltImage bs D⌝ }}

end spec

end EtcdGrove
end Perennial
