/-
Lean-first (no Rocq counterpart). #33 S3b (2026-11-23): `TermAt(l, k)`: `termAt`.
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

/-- `TermAt(l, k)` (R 131): `termAt l k`. -/
abbrev TermAt.spec : Prop :=
  ∀ (sl : GoSlice) (l : List Entry) (k : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      logRO sl l }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermAt)) (Val #sl)) (Val #k))
  {{ (r : w64), RET #r; ⌜sint.Z r = termAt l (sint.Z k)⌝ }}

end spec

end AntCheck
end EtcdGrove
end Perennial
