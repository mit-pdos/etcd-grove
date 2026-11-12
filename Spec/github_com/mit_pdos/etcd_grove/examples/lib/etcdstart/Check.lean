/- Lean-first (no Rocq counterpart).

`Check(name, put, evs, tried, oks)` (`examples/lib/etcdstart/watch.go`; watchkv's until 2026-10-22, D33): returns, without panicking, when the events are puts at
revisions `2, 3, ...`, each of a key and value tried, and each successful Put is the event at its
revision with its key and value (`CheckOk`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Attempted

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.lib.etcdstart

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]

/-- See the file header. -/
abbrev Check.spec : Prop :=
  ∀ (name put : GoString) (esl tsl osl : GoSlice) (evs : List wev) (tried : List wkv)
    (oks : List wrec),
  CheckOk evs tried oks →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
      esl ↦*□ evs ∗ tsl ↦*□ tried ∗ osl ↦*□ oks }}
    (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Check))
      (Val #name)) (Val #put)) (Val #esl)) (Val #tsl)) (Val #osl))
  {{ RET #(); True }}

end spec

end etcdstart
end EtcdGrove
end Perennial
