/-
`membership.newMember(name, peerURLs, memberID, isLearner)` (`member.go:76-86`; claim #34, stage 2,
2026-11-25: translated with its body). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Build

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`newMember(name, us, id, isLearner)`** of plain peer URLs `us` (read-only): a fresh member,
owned, of the id, the URLs' strings, the learner flag, the name, no client URLs. -/
abbrev membership.newMember.spec : Prop :=
  ∀ (name : GoString) (sl : GoSlice) (us : List _root_.Perennial.net.url.URL) (id : w64) (il : Bool),
  (∀ u ∈ us, http.urlRootPlain u) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ sl ↦*□ us }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.membership.newMember)) (Val #name)) (Val #sl)) (Val #id)) (Val #il))
  {{ (m : Loc), RET #m;
      membership.memberAt m 1 ⟨id, us.map membership.urlStrOf, il, name, []⟩ }}

end spec

end EtcdGrove
end Perennial
