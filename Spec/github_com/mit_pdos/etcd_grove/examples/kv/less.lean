/- Lean-first (no Rocq counterpart).

`less(a, b)` (kv.go, D22 S-r): the byte-wise order of strings. Its result is not stated: the
proof needs of the order only that `sortStrings` permutes (`sortStrings.spec`), and `StateEnc`
admits any order of the keys.
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
abbrev less.spec : Prop :=
  ∀ (a b : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kv.less)) (Val #a)) (Val #b))
  {{ (r : Bool), RET #r; True }}

end spec

end kv
end EtcdGrove
end Perennial
