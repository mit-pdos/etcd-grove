/- Lean-first (no Rocq counterpart).

`genFrom(n)` (linkvtxn.go): an input `Apply` may take (`GenIn`), for any `n`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.GenLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.linkvtxn


section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

/-- See the file header. -/
abbrev genFrom.spec : Prop :=
  ∀ (n : w64),
  {{ (True : IProp GF) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkvtxn.genFrom)) (Val #n))
  {{ (x : Input), RET #x; ⌜GenIn x⌝ }}

end spec

end linkvtxn
end EtcdGrove
end Perennial
