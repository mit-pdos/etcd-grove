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

/-- `f.WriteAt(b, off)`: the file gets `b`'s bytes at `off` (zeros in a gap after its end),
or, if it fails (`err` not nil), the first `k` of them. The mapped cells of the bytes it
changes are passed in (the caller's half) and come back with the new bytes. -/
abbrev os.File.WriteAt.spec : Prop :=
  ∀ (f : Loc) (fd : w64) (bs : List w8) (m : Option (Loc × Nat)) (b : GoSlice) (ds : List w8)
    (q : DFrac) (off : w64),
  0 ≤ sint.Z off →
  {{ osFile (GF := GF) f fd ∗ fileBytes fd bs ∗ fileMap fd m ∗ b ↦*{q} ds ∗
      mapRange m bs (min (sint.nat off) bs.length) (sint.nat off + ds.length) }}
    (App (App (Val (f @!! go.GoType.PointerType _root_.Perennial.os.File.ty @!! go!"WriteAt")) (Val #b)) (Val #off))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ (k : Nat), ⌜k ≤ ds.length ∧ n = W64 k ∧ (err = interface.nil → k = ds.length)⌝ ∗
      fileBytes fd (writeBytes bs (sint.nat off) (ds.take k)) ∗ fileMap fd m ∗ b ↦*{q} ds ∗
      mapRange m (writeBytes bs (sint.nat off) (ds.take k)) (min (sint.nat off) bs.length)
        (sint.nat off + ds.length) }}

end spec

end bbolt
end EtcdGrove
end Perennial
