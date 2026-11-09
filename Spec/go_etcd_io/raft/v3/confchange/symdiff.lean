/-
## `symdiff(l, r)` (internal)

**Users.** `Simple` (the tracker's incoming voters against the copy's). Mirrors the code: two
`range`s counting into an `int` (wrapping, as the model's `symdiffTooBig` reads it).
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ConfChange

open Iris Iris.BI
open Classical Tracker

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.confchange.Assumptions]

/-- (internal) The size of the symmetric difference, as an `int`. -/
def symdiff.spec : Prop :=
  ∀ (l r : GoMap) (dql dqr : DFrac) (sl sr : GSet w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ Quorum.majorityOwn l dql sl ∗ Quorum.majorityOwn r dqr sr }}
    (App (App (Val #(functions go_etcd_io.raft.v3.confchange.symdiff [])) (Val #l)) (Val #r))
  {{ RET #(W64 (GMap.size (sl \ sr) + GMap.size (sr \ sl))); Quorum.majorityOwn l dql sl ∗
      Quorum.majorityOwn r dqr sr }}

end spec
end ConfChange
end EtcdGrove
end Perennial
