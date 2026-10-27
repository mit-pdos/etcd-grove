/-
`(*EtcdServer).setAppliedIndex(v)` (server.go). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ServerOn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.cindex go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.setAppliedIndex(v')`, by the apply thread (the only writer), right after applying the entry
at index `v'`, with mvcc's certificate of the KV log `L` it left (the request path's unit 4b): it
stores `v'` into the atomic `s.appliedIndex` and, at that point, raises the ghost applied index to
`v'` and makes `L` the current applied log. Since 2026-10-14 (unit C2a) the log `L` is deposited
ahead as the log applied through `v' = v + 1` (`srvAppliedPre γr v v' L`, `applied_predeposit`:
before the entry's result goes to its proposer), and the store publishes it. -/
abbrev EtcdServer.setAppliedIndex.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (v v' : w64) (L : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvAppliedInv s E γr ∗ srvAppliedPre γr v v' L ∗ mvcc.idxCert E.γ.idx L }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"setAppliedIndex")) (Val #v'))
  {{ RET #(); srvAppliedOwn γr v' ∗ appliedAtLeast γr v' ∗ appliedLogAt γr v' L }}


/-- **`spec` in the auth mode `on`** (the auth plan's E3p, 2026-10-27): the applied index's
invariant over the mode's KV model (`srvAppliedInvM on`), and (E3u) in the mode `on` the auth state
at the log through `v'` published (`appliedPubM`, which the invariant keeps of the current applied
index; `True` at `false`, so `spec` is `specM false` up to it). -/
abbrev EtcdServer.setAppliedIndex.specM (on : Bool) : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (v v' : w64) (L : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvAppliedInvM on s E γr ∗ srvAppliedPre γr v v' L ∗ mvcc.idxCert E.γ.idx L ∗
      appliedPubM on E γr v' }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"setAppliedIndex")) (Val #v'))
  {{ RET #(); srvAppliedOwn γr v' ∗ appliedAtLeast γr v' ∗ appliedLogAt γr v' L }}

end spec

end EtcdGrove
end Perennial
