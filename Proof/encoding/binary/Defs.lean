/-
`encoding/binary`'s byte order as the code passes it (2026-10-22, rafthttp stage 3): the vocabulary
of `Write`'s and `Read`'s specs (`Spec/encoding/binary/{WriteUint64,WriteUint8,ReadUint64}.lean`);
the big-endian bytes are `InvCindex.lean`'s `u64Be`/`beToU64`. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvCindex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

section defs
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- **`binary.BigEndian` as a `binary.ByteOrder`**: the global loaded (a struct without fields:
its zero value, `encoding.binary.wp_load_struct_nofields`) and converted to the interface. -/
abbrev bigEndianOrder : GoInterface :=
  interface.mkOk encoding.binary.bigEndian.ty #(zero_val encoding.binary.bigEndian)

end defs

open Iris Iris.BI

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.binary.Assumptions]

open Iris.ProofMode in
/-- **`binary.BigEndian` is not nil**, from the package's initialization (whose state holds its
points-to): what loading the global needs (`encoding.binary.wp_load_struct_nofields`). -/
theorem bigEndian_ne_null :
    isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ⊢
      ⌜globalAddr encoding.binary.BigEndian ≠ null⌝ := by
  iintro #Hpkg
  ihave #Hinit := encoding.binary.isInit_access $$ Hpkg
  icases Hinit with ⟨-, #Hbe⟩
  iapply typedPointsto_not_null _ _ _ $$ Hbe

end lemmas

end EtcdGrove
end Perennial
