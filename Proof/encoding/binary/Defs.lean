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
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext]

/-- **`binary.BigEndian` as a `binary.ByteOrder`**: the global loaded (a struct without fields:
its zero value, `encoding.binary.wp_load_struct_nofields`) and converted to the interface. -/
abbrev bigEndianOrder : GoInterface :=
  interface.mkOk encoding.binary.bigEndian.ty #(zero_val encoding.binary.bigEndian)

end defs

end EtcdGrove
end Perennial
