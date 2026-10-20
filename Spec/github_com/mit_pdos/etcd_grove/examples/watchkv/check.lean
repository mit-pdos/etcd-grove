/- Lean-first (no Rocq counterpart).

`check(evs, tried, oks)` (watchkv.go): returns, without panicking, when the events are puts at
revisions `2, 3, ...`, each of a key and value tried, and each successful Put is the event at its
revision with its key and value (`CheckOk`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.watchkv.attempted

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace watchkv

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.watchkv

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.watchkv.Assumptions]

/-- See the file header. -/
abbrev check.spec : Prop :=
  ∀ (esl tsl osl : GoSlice) (evs : List wev) (tried : List wkv) (oks : List wrec),
  CheckOk evs tried oks →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.watchkv ∗
      esl ↦*□ evs ∗ tsl ↦*□ tried ∗ osl ↦*□ oks }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.watchkv.check)) (Val #esl))
      (Val #tsl)) (Val #osl))
  {{ RET #(); True }}

end spec

end watchkv
end EtcdGrove
end Perennial
