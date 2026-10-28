/-
`WriteTo` (the backend's `snapshot`, `backend.go`: the method its embedded `*bolt.Tx` promotes;
names only). `s.WriteTo(w)`: the snapshot's database written to `w` (bbolt's `Tx.WriteTo`: two
meta pages, then the data pages read from the database file). The trust boundary (D22 S-f,
2026-10-19; an axiom in `Proof/go_etcd_io/etcd/server/v3/storage/backend/snapshot__WriteTo.lean`).
Lean-first (no Rocq counterpart); the vocabulary is `InvSnapshot.lean`.

The pre: a share of the snapshot open over `D` (`snapOpenQ`, given back: it only reads the
transaction) and the writer's contract (`writerOk w Wr`) at the bytes `bs₀` written so far. The
post: some bytes `bs` appended (`WriteTo` calls only `w.Write`), at least one `Write` call having
returned (D22 S-h, 2026-10-20: its first action is the first meta page's `Write`, the transaction's
`WriteFlag` being `0`, which etcd never sets), and, if the error is nil, `bs` a bbolt image of `D`
(`boltImage`). The count it returns is not specified (the sender only logs it).
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `s.WriteTo(w)`: bytes appended to the writer, after at least one `Write` returned, an image of
the snapshot's data unless the error is non-nil. -/
abbrev backend.snapshot.WriteTo.spec : Prop :=
  ∀ (sp : Loc) (D : Data) (γ : GName) (q : Qp) (w : GoInterfaceOk)
    (Wr : Bool → List w8 → IProp GF) (c : Bool) (bs₀ : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      snapOpenQ sp D γ q ∗ writerOk w Wr ∗ Wr c bs₀ }}
    (App (Val (sp @!! go.GoType.PointerType snapshot.ty @!! go!"WriteTo")) (Val #(GoInterface.ok w)))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ bs : List w8, snapOpenQ sp D γ q ∗ Wr true (bs₀ ++ bs) ∗
        ⌜err = GoInterface.nil → boltImage bs D⌝ }}

end spec

end EtcdGrove
end Perennial
