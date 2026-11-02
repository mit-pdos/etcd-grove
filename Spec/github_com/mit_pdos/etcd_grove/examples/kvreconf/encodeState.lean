/- Lean-first (no Rocq counterpart).

`encodeState(kv, applied)` (kv.go, D22 S-r): the store's map and applied table as a snapshot's
data (`encState`), of some list of the map's bindings and some list of the table's (in Go, each
in increasing order of the keys; see `less.spec`). (2026-10-22, the snapshot-liveness fix: the
table maps each operation applied to its answer, and both are written by `putMap`.)
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
abbrev encodeState.spec : Prop :=
  ∀ (mK mA : Loc) (K A : GMap GoString GoString) (dq1 dq2 : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvreconf ∗
      mK ↦${dq1} K ∗ mA ↦${dq2} A }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvreconf.encodeState)) (Val #mK)) (Val #mA))
  {{ (s : GoSlice), RET #s; mK ↦${dq1} K ∗ mA ↦${dq2} A ∗
      ∃ (kvs ops : List (GoString × GoString)),
        s ↦* encState kvs ops ∗ ⌜KVsOf K kvs ∧ KVsOf A ops⌝ }}

end spec

end kvreconf
end EtcdGrove
end Perennial
