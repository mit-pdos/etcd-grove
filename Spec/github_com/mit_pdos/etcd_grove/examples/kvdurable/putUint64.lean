/- Lean-first (no Rocq counterpart).

`putUint64(buf, x)` (storage.go): `buf` with `x` appended, 8 bytes, little-endian.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Codec

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]

/-- See the file header. -/
abbrev putUint64.spec : Prop :=
  ∀ (buf : GoSlice) (B : List w8) (x : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable ∗ buf ↦* B ∗ ownSliceCap w8 buf (DFrac.own 1) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvdurable.putUint64)) (Val #buf)) (Val #x))
  {{ (s : GoSlice), RET #s; s ↦* (B ++ u64Le x) ∗ ownSliceCap w8 s (DFrac.own 1) }}

end spec

end kvdurable
end EtcdGrove
end Perennial
