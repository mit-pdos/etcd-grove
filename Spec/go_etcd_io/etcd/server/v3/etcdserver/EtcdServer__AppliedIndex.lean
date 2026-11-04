/-
`s.AppliedIndex()` (`server.go`). Lean-first (no Rocq counterpart); the request path's unit 4b
(2026-10-13): a method of the read loop's `server` interface (`read/Inv.lean`, `isReadServer`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ServerOn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`spec` in the auth mode `on`** (the auth plan's E3r, 2026-10-27; `srvAppliedInvM on`, `specOff` at
`on = false` by definition). -/
abbrev EtcdServer.AppliedIndex.specM (on : Bool) : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γr : ReadNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvAppliedInvM on s E γr }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"AppliedIndex")) (Val #()))
  {{ (v : w64), RET #v; appliedAtLeast γr v }}

/-- **`s.AppliedIndex()`** (the auth component's stage 2, 2026-11-04: one statement in both auth
modes): `s.getAppliedIndex()`, an index the applied index has reached, from the applied index's
invariant in the mode `on` (a model row, `srvAppliedInvM`). Until stage 2, `spec` was this at
`on = false` (now `specOff`, `ModeSpecs.lean`). -/
abbrev EtcdServer.AppliedIndex.spec : Prop :=
  ∀ on : Bool, EtcdServer.AppliedIndex.specM (GF := GF) (hG := hG) on

end spec

end EtcdGrove
end Perennial
