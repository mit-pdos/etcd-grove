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

/-- `f.Truncate(size)`: the file is cut or extended with zeros to `size` bytes (unless it
fails). The mapped cells of the bytes that go or come are passed in and come back. -/
abbrev os.File.Truncate.spec : Prop :=
  ∀ (f : Loc) (fd : w64) (bs : List w8) (m : Option (Loc × Nat)) (size : w64),
  0 ≤ sint.Z size →
  {{ osFile (GF := GF) f fd ∗ fileBytes fd bs ∗ fileMap fd m ∗
      mapRange m bs (min (sint.nat size) bs.length) (max (sint.nat size) bs.length) }}
    (App (Val (f @!! go.GoType.PointerType _root_.Perennial.os.File.ty @!! go!"Truncate")) (Val #size))
  {{ (err : GoInterface), RET #err;
      ∃ (bs' : List w8), ⌜bs' = truncBytes bs (sint.nat size) ∨ (err ≠ interface.nil ∧ bs' = bs)⌝ ∗
      fileBytes fd bs' ∗ fileMap fd m ∗
      mapRange m bs' (min (sint.nat size) bs.length) (max (sint.nat size) bs.length) }}

end spec

end bbolt
end EtcdGrove
end Perennial
