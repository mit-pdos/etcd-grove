/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/examples/snapstore/Store__Create.lean (241f27e).
-/
/-
`snapstore.Store.Create`'s spec (stage 3, package-internal).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.snapstore.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open github_com.hashicorp.raft github_com.hashicorp.raft.examples.snapstore

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.snapstore.Assumptions]

/-- `st.Create(ver, idx, term, cfg, cfgIdx, trans)`: a fresh sink, open and empty, with some id. -/
abbrev github_com.hashicorp.raft.examples.snapstore.Store.Create.spec : Prop :=
  ∀ (st : Loc) (γ : GName) (eof : GoInterface) (ver idx term cfgIdx : w64) (cfg : Configuration)
    (trans : GoInterface),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.snapstore ∗ isStore st γ eof }}
      (App (App (App (App (App (App (Val (st @!! go.GoType.PointerType Store.ty @!! go!"Create"))
        (Val #ver)) (Val #idx)) (Val #term)) (Val #cfg)) (Val #cfgIdx)) (Val #trans))
    {{ (k : Loc) (id : GoString),
        RET (PairV #(interface.mkOk (go.GoType.PointerType Sink.ty) #k) #interface.nil);
        sinkCore k st γ eof id ver idx term cfgIdx cfg ∗ sinkSt k (some []) }}

end spec

end Perennial
