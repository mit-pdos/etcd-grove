/-
`Members(prefix, k, peerBase, clientBase)` (`examples/lib/etcdstart/members.go`; the clusterN Scope,
`notes/clusterN-scope.md`, 2026-11-15): the `k` members of a new cluster named `prefix`. Lean-first
(no Rocq counterpart).

**The triple:** for a count `k` below `2 ^ 63` (`make`'s length, an `int`), `Members` returns a new
slice of the members `membersOf prefix k peerBase clientBase`: member `i` named `prefix-i`, with
peer address `127.0.0.1:(peerBase+i)` and client address `127.0.0.1:(clientBase+i)`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.MembersDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]

/-- See the file header. -/
abbrev Members.spec : Prop :=
  ∀ (pfx : GoString) (k pb cb : w64), uint.Z k < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Members))
      (Val #pfx)) (Val #k)) (Val #pb)) (Val #cb))
  {{ (sl : GoSlice), RET #sl; sl ↦* membersOf pfx (uint.nat k) pb cb }}

end spec

end etcdstart
end EtcdGrove
end Perennial
