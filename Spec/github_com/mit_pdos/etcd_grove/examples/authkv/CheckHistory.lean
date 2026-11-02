/-
`CheckHistory(evs, endKey)` (`examples/authkv/authkv.go`; the auth plan's E2f).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Checks

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

/-- `CheckHistory(evs, endKey)` returns (does not panic) when every event but of the key `endKey`
and the set-up's puts (`setupWriteK`) is a write its key's principal was permitted (`histOk`). -/
abbrev CheckHistory.spec : Prop :=
  ∀ (esl : GoSlice) (evs : List wev) (dq : DFrac) (endKey : GoString),
  histOk evs endKey →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.authkv ∗
      esl ↦*{dq} evs }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.authkv.CheckHistory))
      (Val #esl)) (Val #endKey))
  {{ RET #(); esl ↦*{dq} evs }}

end spec

end authkv
end EtcdGrove
end Perennial
