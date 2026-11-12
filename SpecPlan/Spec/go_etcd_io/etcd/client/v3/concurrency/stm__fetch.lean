/-
`(*concurrency.stm).fetch` (`client/v3/concurrency/stm.go`), internal: the STM's method.

Users: the user's closure through `STM` (`stmAt_methods`), `runSTM`, `stmSerializable`'s methods.

Proof sketch: the read set's lookups; else `OpGet.spec` per key (the gets' options `gs`), the KV
contract's `Txn(...).Then(gets...).Commit()` (a read-only transaction: its persistent update
from the read permission, `etcdPeek`); its reply's nested ranges (W0's model: one per key, each
with its view's revision as header) persisted, `readSet.add.spec` (each read `readOf` the
reply's state); an error: `panic(stmError{err})` (`stmRet`'s abort).

Changes: from `specs-ref`'s `stm__fetch.lean`: restated over `stmCoreAt` and the `Attempt` model.

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.concurrency.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Concurrency

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- `s.fetch(keys...)`: `nil` for no key; the response of the first key already read, else one read transaction of all the keys (at the gets' options) and the first's response; or the abort. -/
def stm.fetch.spec : Prop :=
  ∀ (p : Loc) (γ : Cluster) (dflt who : Principal) (iso : w64) (a : Attempt) (gs : List (OpM → OpM)) (sl : GoSlice) (ks : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ stmCoreAt p γ who iso a gs ∗ sl ↦*□ ks }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.stm.ty @!! go!"fetch")) (Val #sl))
  {{ (r : val), RET r; stmRet r (fun resp : Loc => iprop(∃ a',
      stmCoreAt p γ who iso a' gs ∗
      ⌜a'.writes = a.writes ∧ (∀ k e, a.reads k = some e → a'.reads k = some e) ∧
            (∀ k, a'.reads k ≠ none → a.reads k ≠ none ∨ k ∈ ks)⌝ ∗
          ((⌜ks = [] ∧ resp = null ∧ a' = a⌝) ∨
           (∃ (k : GoString) (e : ReadM),
              ⌜(ks.find? (fun k => decide (a.reads k ≠ none)) = some k ∨
                (ks.find? (fun k => decide (a.reads k ≠ none)) = none ∧ ks.head? = some k)) ∧
                a'.reads k = some e⌝ ∗ readRespAt resp e)))) iprop(True) }}

end spec

end Concurrency
end EtcdGrove
end Perennial
