/- Lean-first (no Rocq counterpart).

`randomWord()`: a word (`isWord`: at most `32` lowercase letters).
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
abbrev randomWord.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.httpdriver }}
    (App (Val (@! randomWord)) (Val #()))
  {{ (s : GoString), RET #s; ⌜isWord s⌝ }}

end spec
end github_com.mit_pdos.etcd_grove.examples.net.httpdriver
end Perennial
