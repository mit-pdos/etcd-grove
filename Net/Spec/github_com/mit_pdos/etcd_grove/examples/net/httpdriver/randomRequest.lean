/- Lean-first (no Rocq counterpart).

`randomRequest()`: one of the driver's requests (`DReq`, `qOf`).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net
open net.http (HReq HProto Resp RespSlot ReqSlot HdrLine HttpProtoGS RespSt)

namespace github_com.mit_pdos.etcd_grove.examples.net.httpdriver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [π : NetProtoGS] [hπ : HttpProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- See the file header. -/
abbrev randomRequest.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.httpdriver }}
    (App (Val (@! randomRequest)) (Val #()))
  {{ (q : request), RET #q; ⌜∃ d : DReq, d.ok ∧ qOf q d⌝ }}

end spec
end github_com.mit_pdos.etcd_grove.examples.net.httpdriver
end Perennial
