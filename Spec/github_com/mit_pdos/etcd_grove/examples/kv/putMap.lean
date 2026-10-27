/- Lean-first (no Rocq counterpart).

`putMap(buf, m)` (kv.go, 2026-10-22, the snapshot-liveness fix): `buf` with the map `K` appended
(`encMap`), of some list of its bindings (`KVsOf`; in Go, in increasing order of the keys, see
`less.spec`).
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
abbrev putMap.spec : Prop :=
  ∀ (buf : GoSlice) (B : List w8) (mK : Loc) (K : GMap GoString GoString) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗
      buf ↦* B ∗ ownSliceCap w8 buf (DFrac.own 1) ∗ mK ↦${dq} K }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kv.putMap)) (Val #buf)) (Val #mK))
  {{ (s : GoSlice), RET #s; mK ↦${dq} K ∗ ownSliceCap w8 s (DFrac.own 1) ∗
      ∃ kvs : List (GoString × GoString), s ↦* (B ++ encMap kvs) ∗ ⌜KVsOf K kvs⌝ }}

end spec

end kv
end EtcdGrove
end Perennial
