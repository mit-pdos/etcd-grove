/-
`(*EtcdServer).setTerm(v)` (server.go). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AppliedOn

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

/-- `s.setTerm(v)` stores `v` into the atomic `s.term` (the server's atomics in the environment's
auth mode, `srvAtomicsM`; only the term's invariant is used). -/
abbrev EtcdServer.setTerm.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (v : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvAtomicsM E.authOn s E γr }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"setTerm")) (Val #v))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
