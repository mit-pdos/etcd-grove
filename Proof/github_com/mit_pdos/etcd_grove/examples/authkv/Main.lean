/-
`Main()` (`examples/authkv/authkv.go`; the auth plan's E2b): **not proved** (a `sorry`). Lean-first
(no Rocq counterpart).

What the proof needs, and the state of each callee's statement: `notes/authkv-main-plan.md`
(the skeleton of frozen statements; "Main's callees, draft"). Its hypotheses are the callees
drafted so far; the rest (the watches, G2; `Serve.specOn`, `startServer`, `NewClient`, the
contexts) join at the freeze.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.SetUp
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.newUserClient
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.Work
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.Principals
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.CheckHistory
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.LastIn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

theorem Main.wp_proof
    (wp_SetUp : SetUp.spec (GF := GF) (hG := hG))
    (wp_newUserClient : newUserClient.spec (GF := GF) (hG := hG))
    (wp_Work : Work.spec (GF := GF) (hG := hG))
    (wp_Principals : Principals.spec (GF := GF) (hG := hG))
    (wp_CheckHistory : CheckHistory.spec (GF := GF) (hG := hG))
    (wp_LastIn : LastIn.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end authkv
end EtcdGrove
end Perennial
