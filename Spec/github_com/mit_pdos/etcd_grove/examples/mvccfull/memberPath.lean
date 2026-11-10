/- Lean-first (no Rocq counterpart).

`memberPath(prefix, id)` (`examples/mvccfull/mvccfull.go`): a member's file,
`prefix + "-" + itoa(id) + ".db"` (`memberPathM`), for `id ≥ 0`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.itoa

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull

/-- A member's file. -/
def memberPathM (pfx : GoString) (id : Nat) : GoString := pfx ++ go!"-" ++ itoaM id ++ go!".db"

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

/-- See the file header. -/
abbrev memberPath.spec : Prop :=
  ∀ (pfx : GoString) (id : w64), 0 ≤ sint.Z id →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccfull.memberPath)) (Val #pfx)) (Val #id))
  {{ RET #(memberPathM pfx (sint.nat id)); True }}

end spec

end mvccfull
end EtcdGrove
end Perennial
