/- Lean-first (no Rocq counterpart).

`encode(replica, seq, kind, val)` (register.go:24): the operation's encoding, a new slice with
its capacity.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

/-- See the file header. -/
abbrev encode.spec : Prop :=
  ∀ (replica seq : w64) (kind : w8) (val : List w8),
  (val.length : Int) < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.register.encode))
      (Val #replica)) (Val #seq)) (Val #kind)) (Val #val))
  {{ (b : GoSlice), RET #b; b ↦* encodeOp replica seq kind val ∗ ownSliceCap w8 b (DFrac.own 1) }}

end spec

end register
end EtcdGrove
end Perennial
