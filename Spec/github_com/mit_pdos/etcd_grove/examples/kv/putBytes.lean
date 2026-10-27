/- Lean-first (no Rocq counterpart).

`putBytes(buf, b)` (kv.go, D22 S-r): `buf` with `b` appended, prefixed by its length (`putB`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]

/-- See the file header. -/
abbrev putBytes.spec : Prop :=
  ∀ (buf b : GoSlice) (B bs : List w8) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗
      buf ↦* B ∗ ownSliceCap w8 buf (DFrac.own 1) ∗ b ↦*{dq} bs }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kv.putBytes)) (Val #buf)) (Val #b))
  {{ (s : GoSlice), RET #s; s ↦* (B ++ putB bs) ∗ ownSliceCap w8 s (DFrac.own 1) ∗
      b ↦*{dq} bs }}

end spec

end kv
end EtcdGrove
end Perennial
