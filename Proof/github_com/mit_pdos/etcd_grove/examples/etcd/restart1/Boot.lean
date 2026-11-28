/- Lean-first (no Rocq counterpart).

# restart1's named premises from the bootstrap axioms (premises to axioms, 2026-11-27)

`Run`'s named premises (`premises`, `Defs.lean`) were the closed theorem's Iris premise `HpremR`: the member's
first-start contract (`etcdstart.premises`) and its restart contract (`etcdstart.bootPremiseR`). Both now come
from interim axioms at Go's values: the first start from `bootstrap.wp_proofOne` (`bootstrap.specOne`, through
`etcdstart.premises_of_specOne`), the restart from `bootstrap.wp_proofRestart` (`bootstrap.specRestart`, through
`etcdstart.bootPremiseR_one`), given the one-member pure facts `BootGo` (putget's `etcdstart.BootGo1` at
restart1's name and addresses) and the `fips140` GODEBUG setting off.

A defs module: it takes the axioms' statements as hypotheses and imports no proof.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.BootRestart

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restart1

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **`bootstrap`'s values for restart1's member are Go's** (pure; `etcdstart.BootGo1` at the member's name,
peer and client addresses; `TestMemberID` in `restart1_test.go` prints the id). -/
abbrev BootGo (id : w64) (ctxs : List (List w8)) (boot : List LogEntry) : Prop :=
  etcdstart.BootGo1 name peerAddr clientAddr id ctxs boot

/-- The member's name is plain JSON string bytes. -/
theorem name_plain : ∀ c ∈ name, JsonScan.plainEnc c := by decide

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`Run`'s named premises from `bootstrap.specOne` and `bootstrap.specRestart`** (see the file header). -/
theorem premises_of_specs [ThreadBoundLe GF (2 ^ 29)] [ReceiptBoundLe GF (2 ^ 60)]
    (hb1 : ∀ [MemStorReg GF], _root_.Perennial.EtcdGrove.bootstrap.specOne (GF := GF) (hG := hG))
    (hbR : ∀ [MemStorReg GF], _root_.Perennial.EtcdGrove.bootstrap.specRestart (GF := GF) (hG := hG))
    (N : Nat) (id : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (hfips : crypto.fips140.GodebugFips140Off) (hf : BootGo id ctxs boot) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ⊢
      premises (GF := GF) N id ctxs boot := by
  iintro #Hpkg
  iunfold premises
  isplitl []
  · iapply (etcdstart.premises_of_specOne hb1 name peerAddr clientAddr N id ctxs boot name_plain hfips hf)
    iexact Hpkg
  · iapply (etcdstart.bootPremiseR_one hbR name peerAddr clientAddr N id ctxs boot name_plain hfips hf)
    iexact Hpkg

end defs

end etcd_restart1
end EtcdGrove
end Perennial

end
