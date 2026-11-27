/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/examples/snapstore/Sink__Close.lean (241f27e).
-/
/-
`snapstore.Sink.Close`'s spec (stage 3, package-internal).
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

/-- `k.Close()`: on an open sink with `bs`, runs the commit (`sinkCommit`: the latest becomes
`newerSnap old (sinkMeta … id bs) bs`) under the store's lock and returns its result `R`; on a
closed sink, nothing. -/
abbrev github_com.hashicorp.raft.examples.snapstore.Sink.Close.spec : Prop :=
  ∀ (k st : Loc) (γ : GName) (eof : GoInterface) (id : GoString) (ver idx term cfgIdx : w64)
    (cfg : Configuration) (o : Option (List w8)) (R : IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.snapstore ∗ sinkCore k st γ eof id ver idx term cfgIdx cfg ∗
        sinkSt k o ∗
        (match o with
          | some bs => sinkCommit γ (sinkMeta ver idx term cfgIdx cfg id bs) bs R
          | none => iprop(True)) }}
      (App (Val (k @!! go.GoType.PointerType Sink.ty @!! go!"Close")) (Val #()))
    {{ RET #interface.nil; sinkSt k none ∗ (match o with | some _ => R | none => iprop(True)) }}

end spec

end Perennial
