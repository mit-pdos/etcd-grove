/- Lean-first (no Rocq counterpart).

`checkWatch(evs, tried, oks)` (linkv3p.go): returns, without panicking, when the events are puts at
revisions `2, 3, ...`, each of a key and value tried, and each successful Put is the event at its
revision with its key and value (`CheckOk`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3p.attempted

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.linkv3p

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]

/-- See the file header. -/
abbrev checkWatch.spec : Prop :=
  ∀ (esl tsl osl : GoSlice) (evs : List wev) (tried : List wkv) (oks : List wrec),
  CheckOk evs tried oks →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv3p ∗
      esl ↦*□ evs ∗ tsl ↦*□ tried ∗ osl ↦*□ oks }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv3p.checkWatch)) (Val #esl))
      (Val #tsl)) (Val #osl))
  {{ RET #(); True }}

end spec

end linkv3p
end EtcdGrove
end Perennial
