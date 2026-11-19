/-
`Tx.WriteTo` (bbolt), for a read transaction (session S4, D-I6 of
`notes/bbolt-integration-plan.md`): the transaction's whole database written to an `io.Writer`
(two meta pages, then the file's pages below the high-water mark, read through the database's
`*os.File`). The writer's contract is `io.writerOk` (`Proof/io/SectionReader.lean`), with no
`ReadFrom` method (`io.writerPlain`: `io.CopyN` would hand it the reader). On success the bytes
written are an image of the transaction's data (`boltImage`) with their txid's receipt
(`boltImageRcpt`, what `fileHolds_of_image` takes). Proof: `Proof/go_etcd_io/bbolt/Tx__WriteTo.lean`.
-/
module

public import Spec.go_etcd_io.bbolt.Api
public import Proof.io.SectionReader

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- See the file header. -/
abbrev Tx.WriteTo.spec : Prop :=
  ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (tx : Loc) (γ : BoltName) (q : Qp) (D : Data)
    (w : GoInterfaceOk) (Wr : Bool → List w8 → IProp GF) (c : Bool) (bs₀ : List w8),
  io.writerPlain w →
  {{ boltTx (GF := GF) tx γ q (TxView.ro D) ∗ io.writerOk w Wr ∗ Wr c bs₀ }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"WriteTo")) (Val #(GoInterface.ok w)))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ bs : List w8, boltTx tx γ q (TxView.ro D) ∗ Wr true (bs₀ ++ bs) ∗
        ((⌜err = GoInterface.nil ∧ boltImage bs D⌝ ∗ boltImageRcpt bs) ∨
          ⌜err ≠ GoInterface.nil⌝) }}

end spec

end bbolt
end EtcdGrove
end Perennial
