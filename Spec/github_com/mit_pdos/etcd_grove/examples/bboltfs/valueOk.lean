/- Lean-first (no Rocq counterpart). `valueOk(txid, v, has)` (`examples/bboltfs/programs.go`): what the programs allow transaction `txid` to hold (`valueOkP`, their `DBNames.vp`): no value for init's transactions (`txid ≤ 1`), and `txid` itself for the others. It returns whether `(has, v)` is that. -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

/-- What the programs allow transaction `t` to hold: nothing for `t ≤ 1` (init's), `t` after. -/
def valueOkP (t : Nat) (vo : Option w64) : Prop :=
  if t ≤ 1 then vo = none else vo = some (W64 (t : Int))

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

/-- See the file header. -/
abbrev valueOk.spec : Prop :=
  ∀ (txid v : w64) (has : Bool),
  {{ (True : IProp GF) }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.bboltfs.valueOk)) (Val #txid))
      (Val #v)) (Val #has))
  {{ (b : Bool), RET #b;
      ⌜b = true ↔ valueOkP txid.toNat (if has then some v else none)⌝ }}

end spec

end bboltfs
end EtcdGrove
end Perennial
