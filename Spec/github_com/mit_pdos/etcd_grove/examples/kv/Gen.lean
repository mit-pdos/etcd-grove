/- Lean-first (no Rocq counterpart).

`Gen(id)` (check.go): the test's random traffic: a boxed `Input` (`kvInOk`), whatever
`primitive.RandomUint64` returns.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.ModelDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI go_etcd_io.raft.v3
open github_com.anishathalye.porcupine

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]

/-- See the file header. -/
abbrev Gen.spec : Prop :=
  ∀ (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kv.Gen)) (Val #id))
  {{ (i : GoInterface), RET #i; □ kvInOk (GF := GF) i }}

end spec

end kv
end EtcdGrove
end Perennial
