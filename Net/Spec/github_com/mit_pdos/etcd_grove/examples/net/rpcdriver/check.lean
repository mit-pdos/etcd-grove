/- Lean-first (no Rocq counterpart).

`check(a, r, err)`: never panics on a call's outcome as net/rpc's client gives it
(`Client.Call.spec`, over the method's spec `echoSpec`): a success with the method's reply to this
request (its id, its payload, `Runs` 1); a `ServerError` whose message is the request's own `fail`
or one of net/rpc's own error answers (`srvErrMsg`, none of which is one of the method's messages:
`srvErrMsg_not_fail`); or another error.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Defs
public import Net.Proof.net.rpc.Codec

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The outcomes `check` takes (see the file header). -/
def callOutcome (pr : Loc) (id : w64) (data : List w8) (fail : GoString) (err : GoInterface) :
    IProp GF :=
  iprop((⌜err = interface.nil ∧ fail = []⌝ ∗
      ∃ dsl' : GoSlice, pr ↦ service.Reply.mk id dsl' (W64 1) ∗ dsl' ↦* data) ∨
    (∃ msg : GoString, ⌜err = net.rpc.serverErr msg ∧ (msg = fail ∨ net.rpc.srvErrMsg msg)⌝) ∨
    ⌜err ≠ interface.nil ∧ net.rpc.notServerErr err⌝)

/-- See the file header. -/
abbrev check.spec : Prop :=
  ∀ (pa pr : Loc) (id : w64) (dsl : GoSlice) (data : List w8) (fail : GoString)
    (err : GoInterface),
  {{ drvFacts ∗ pa ↦ service.Args.mk id dsl fail ∗ dsl ↦* data ∗
      ⌜fail = [] ∨ fail ∈ failList⌝ ∗ callOutcome pr id data fail err }}
    (App (App (App (Val (@! check)) (Val #pa)) (Val #pr)) (Val #err))
  {{ RET #(); True }}

end spec
end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
end Perennial
