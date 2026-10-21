/- Lean-first (no Rocq counterpart).

`encode(replica, seq, kind, key, val)` (kv.go): the operation's encoding (`encodeOp`: the
25-byte header with the key's length, the key, the value), a new slice with its capacity.
-/
module

public import RaftWitness.Proof.github_com.mit_pdos.etcd_grove.examples.kvwitness.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI go_etcd_io.raft.v3
open github_com.anishathalye.porcupine

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]

/-- See the file header. -/
abbrev encode.spec : Prop :=
  ∀ (replica seq : w64) (kind : w8) (key val : List w8),
  (key.length : Int) < 2 ^ 61 → (val.length : Int) < 2 ^ 61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvwitness }}
    (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvwitness.encode))
      (Val #replica)) (Val #seq)) (Val #kind)) (Val #key)) (Val #val))
  {{ (b : GoSlice), RET #b; b ↦* encodeOp replica seq kind key val ∗ ownSliceCap w8 b (DFrac.own 1) }}

end spec

end kvwitness
end EtcdGrove
end Perennial
