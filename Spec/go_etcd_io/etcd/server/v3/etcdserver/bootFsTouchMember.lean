/-
**`TouchDirAll(lg, cfg.MemberDir())` on the start (`bootFs.touchMember.law`, `BootParts.lean`), as a spec the server's link can name** (claim #34 step 4, 2026-11-25): a law
`bootstrap.wp_proof` takes, a hypothesis of the results that reach it (`?` in the server's link). Not a
Go function. Why it is open in the server Link: not proved yet (`TouchDirAll.spec` making the absent `member` directory). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BootParts

@[expose] public section

set_option linter.unusedSectionVars false

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

/-- **bootFs.touchMember.law**, named for the server's link (see the file header). -/
abbrev bootFsTouchMember.spec : Prop := bootFs.touchMember.law (GF := GF) (hG := hG)

end spec

end EtcdGrove
end Perennial
