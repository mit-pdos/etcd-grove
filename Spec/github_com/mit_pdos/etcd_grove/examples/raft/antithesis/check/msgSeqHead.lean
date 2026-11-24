/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `msgSeqHead(c)`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Rep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- `C[1]`, where `C` is not empty (`<<>>[1]`: an `EvalError`). -/
abbrev msgSeqHead.spec : Prop :=
  ∀ (sl : GoSlice) (ms : List Msg) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      msgsRO sl ms ∗ ⌜AntCheck.msgSeqHead ms = .ok m⌝ }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.msgSeqHead)) (Val #sl))
  {{ (u : G.Msg), RET #u; msgRO u m }}

end spec

end AntCheck
end EtcdGrove
end Perennial
