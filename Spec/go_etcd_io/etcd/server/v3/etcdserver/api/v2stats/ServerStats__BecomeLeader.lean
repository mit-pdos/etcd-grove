/-
`(*v2stats.ServerStats).BecomeLeader()` (`server.go`; the server's ready handler calls it when it
becomes the leader). Lean-first (the request path's unit 4c); translated with its body since
prove-ps2-v2stats (2026-11-21, the trust boundary until then).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.Defs

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

/-- `st.BecomeLeader()` on a non-nil `*ServerStats` made by `NewServerStats`
(`v2stats.isServerStats`) returns. (Until prove-ps2-v2stats, 2026-11-21, an axiom with `st ≠ null`
only, which no proof could discharge without the stats' mutex: the approved rule of adding a
persistent ownership premise every caller discharges, `notes/specs-only/ledger.md`.) -/
abbrev v2stats.ServerStats.BecomeLeader.spec : Prop :=
  ∀ (st : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats ∗ ⌜st ≠ null⌝ ∗
      v2stats.isServerStats st }}
    (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.ServerStats.ty @!! go!"BecomeLeader")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
