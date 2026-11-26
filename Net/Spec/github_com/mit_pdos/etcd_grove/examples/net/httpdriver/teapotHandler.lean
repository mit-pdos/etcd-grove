/- Lean-first (no Rocq counterpart).

`teapotHandler(w, r)`: a run of a handler of the requests under `/status` with the protocol `drvP` (`servePre`
to `serveDone`), returning `()` or a panic.
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
abbrev teapotHandler.spec : Prop :=
  ∀ (w : GoInterface) (r : Loc) (R : HReq) (τ : GName) (rd : GoInterface)
    (I : RespSt → IProp GF) (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF),
    (∀ x, S x ⊢ iprop(⌜x.length < 2 ^ 60⌝)) →
  iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.httpdriver ∗
      net.http.servePre drvP go!"/status" w r R τ rd I S E) ⊢
    WP (App (App (Val (@! teapotHandler)) (Val #w)) (Val #r))
      {{ v, ⌜v = #() ∨ v.isPanic = true⌝ ∗ net.http.serveDone drvP R τ I S v }}

end spec
end github_com.mit_pdos.etcd_grove.examples.net.httpdriver
end Perennial
