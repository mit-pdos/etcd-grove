/-
`put(s, i)` (`examples/etcd/restart1/restart1.go`; restart S7.5, step c, 2026-11-14): `s.Put` of
`key(i) ↦ value(i)` through the server's own API, in a context with the request timeout, cancelled
after the call. Lean-first (no Rocq counterpart).

**The triple:** at a started member's request view (`isServerReq`, auth off) and the revocation's
built part (`srvRevokeBuilt`, from which the call borrows its `leadTimeMu` slot and `E.RD` at level 2
of the thread token, and gives them back), under `restart1`'s KV invariant (`r1Inv`), with the
driver's half of the put counter at `i < NPuts`: the thread token back, and `nil` with the counter's
half at `i + 1` (the put fired: the range holds the first `i + 1` pairs), or an error.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.KV
public import Perennial.ProgramLogic.Bounds

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restart1

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Assumptions]

/-- See the file header. -/
abbrev put.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γc : GName) (i : Nat)
    [ReceiptBoundLe GF (2 ^ 48)],
  i < r1NPuts → E.authOn = false → srvLevels (GF := GF) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restart1 ∗
      isServerReq s E ρ ∗ srvRevokeBuilt s E ∗ threadTok ∗
      r1Inv ρ.kv γc ∗ monoNatAuthOwn γc (1 : Qp).half i }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.restart1.put))
      (Val #s)) (Val #(W64 (i : Int))))
  {{ (err : GoInterface), RET #err; threadTok ∗
      ((⌜err = GoInterface.nil⌝ ∗ monoNatAuthOwn γc (1 : Qp).half (i + 1)) ∨
        ⌜err ≠ GoInterface.nil⌝) }}

end spec

end etcd_restart1
end EtcdGrove
end Perennial
