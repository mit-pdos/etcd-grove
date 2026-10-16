/-
`lease.NewLessor(lg, b, cluster, cfg)` (`lessor.go`): names-only (it starts the lessor's loop). Lean-first (no Rocq counterpart); the server-construction unit, stage N0 (2026-10-16, D13:
`notes/decisions.md`), for `NewServer`.
Pending (`?` in `etc/link-lean-first-server.txt`): a hypothesis of `NewServer`'s linked result
until unit N1 settles it (then an axiom at the trust boundary).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`NewLessor(lg, b, cl, cfg)`** over a backend `b` whose batch lock's invariant is `P` with the
post-lock hook `f` (`lease.leaseBackend`): a lessor (`lessorOk`: `Promote`, `Demote`,
`ExpiredLeasesC`; `SetCheckpointer` returns), with names `γl` (mvcc's `isLessor`, a reader slot of
its lock for the store, the live set empty), whose apply-side methods meet the apply contract at
any store over those names (`isApplyLessor`). -/
abbrev lease.NewLessor.spec : Prop :=
  ∀ (lg : Loc) (b cl : GoInterface) (cfg : go_etcd_io.etcd.server.v3.lease.LessorConfig)
    (P : IProp GF) (f : val),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ ⌜lg ≠ null⌝ ∗
      lease.leaseBackend b P f }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.lease.NewLessor)) (Val #lg)) (Val #b))
      (Val #cl)) (Val #cfg))
  {{ (l : GoInterface), RET #l; lessorOk l ∗ lessorCkptOk l ∗
      ∃ γl : GName, mvcc.isLessor l γl ∗ lease.lessorRdOf γl ∗ lease.leaseOwn γl [] ∗
        □ (∀ γ : mvcc.StoreNames, ⌜γ.leases = γl⌝ -∗ apply.isApplyLessor l γ P f) }}

end spec

end EtcdGrove
end Perennial
