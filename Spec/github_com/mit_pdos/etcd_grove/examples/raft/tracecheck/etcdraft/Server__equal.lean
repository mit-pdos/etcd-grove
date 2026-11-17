/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `v.equal(w, srv)`: `Server.eq` (`matchIndex` compared on `srv`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Own

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

/-- `v.equal(w, srv)`: the servers' variables equal, `matchIndex` compared on the servers `srv`. -/
abbrev Server.equal.spec : Prop :=
  ∀ (p : Loc) (v : Server) (q : Loc) (w : Server) (sl : GoSlice) (srv : SetIds),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      serverRO p v ∗ serverRO q w ∗ setRO sl srv }}
    (App (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Server.ty
      @!! go!"equal")) (Val #q)) (Val #sl))
  {{ RET #(v.eq w srv); True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
