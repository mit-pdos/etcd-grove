/- Lean-first (no Rocq counterpart).

`readCtx(replica, seq, key)` (kv.go): a read's context (`readCtxB`: the replica, little-endian,
then the read's encoding, of kind `opRead`), a new slice.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]

/-- See the file header. -/
abbrev readCtx.spec : Prop :=
  ∀ (replica seq : w64) (key : List w8),
  (key.length : Int) < 2 ^ 61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvreconf }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvreconf.readCtx))
      (Val #replica)) (Val #seq)) (Val #key))
  {{ (b : GoSlice), RET #b; b ↦* readCtxB replica seq key ∗ ownSliceCap w8 b (DFrac.own 1) }}

end spec

end kvreconf
end EtcdGrove
end Perennial
