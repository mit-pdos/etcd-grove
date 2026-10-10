module
public import Proof.os.FileModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `f.ReadAt(b, off)`: the first `k` bytes of `b` become the file's from `off` on, where `k`
is `len(b)` unless the file ends first (or the read fails: then `err` is not nil). -/
abbrev os.File.ReadAt.spec : Prop :=
  ∀ (f : Loc) (fd : w64) (bs : List w8) (b : GoSlice) (ds : List w8) (off : w64),
  0 ≤ sint.Z off →
  {{ osFile (GF := GF) f fd ∗ fileBytes fd bs ∗ b ↦* ds }}
    (App (App (Val (f @!! go.GoType.PointerType _root_.Perennial.os.File.ty @!! go!"ReadAt")) (Val #b)) (Val #off))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ (k : Nat), ⌜k ≤ ((bs.drop (sint.nat off)).take ds.length).length ∧ n = W64 k ∧
        (err = interface.nil → k = ds.length)⌝ ∗
      fileBytes fd bs ∗ b ↦* (((bs.drop (sint.nat off)).take k) ++ ds.drop k) }}

end spec

end bbolt
end EtcdGrove
end Perennial
