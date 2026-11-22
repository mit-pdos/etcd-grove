/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/NewLessor.lean`: `NewLessor` converts `newLessor`'s
`*lessor` to the `Lessor` interface (`lessor.go:208-210`). Lean-first (no Rocq counterpart). An axiom
from unit N4 (2026-10-17, D14d/D14e) to prove-ps2-newlessor5 (2026-11-21), which proved `newLessor`
over the real code (`newLessor.lean`); the expiry loop's payload is `Lease.expired`'s trust boundary
(`Lease__expired.lean`), which replaced it.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.NewLessor
public import Spec.go_etcd_io.etcd.server.v3.lease.newLessor

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem lease.NewLessor.wp_proof (hNL : lease.newLessor.spec (GF := GF) (hG := hG)) :
    lease.NewLessor.spec (GF := GF) (hG := hG) := by
  intro lg cl cfg d W Pk qo GA S r mono recs reqOf Lr hS hlp hrecs hrq hLr
  wp_start as ⟨Hlg, %Hrate, #Hcl, #HB, Ho, Htoks, Hrb, #HGA, %Htb⟩
  (try wp_auto)
  wp_apply (hNL lg cl cfg d W Pk qo GA S r mono recs reqOf Lr hS hlp hrecs hrq hLr)
    $$ [$Hpkg $Hlg $Hcl $HB $Ho $Htoks $Hrb $HGA]
    as %lp ⟨Ho, Hrb, %γl, Hpost⟩
  · ipureintro; exact ⟨Hrate, Htb⟩
  (try wp_auto)
  iapply HΦ
  iframe Ho Hrb
  iexists lp, γl
  iframe Hpost
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial
