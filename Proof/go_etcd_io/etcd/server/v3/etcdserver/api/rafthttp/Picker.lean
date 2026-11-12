/-
**A peer's URL picker** (`urlpick.go`; rafthttp stage 4): the mutex `mu` guards the peer's URLs,
read-only, non-empty, each satisfying `P` (the peer's: its hosts are its member's), and the index
`picked` among them. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Stream

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- What the picker's mutex guards. -/
def pickerInv (pk : Loc) (P : net.url.URL → Prop) : IProp GF :=
  iprop(∃ (sl : GoSlice) (us : List net.url.URL) (i : w64),
    pk.[rafthttp.urlPicker, go!"urls"] ↦ sl ∗ sl ↦*□ us ∗ pk.[rafthttp.urlPicker, go!"picked"] ↦ i ∗
    ⌜0 ≤ sint.Z i ∧ sint.Z i < us.length ∧ ∀ u ∈ us, P u⌝)

/-- **A URL picker of URLs satisfying `P`** (persistent). -/
def pickerOk (pk : Loc) (P : net.url.URL → Prop) : IProp GF :=
  sync.isMutex (pk.[rafthttp.urlPicker, go!"mu"]) (pickerInv pk P)

instance pickerOk_persistent (pk : Loc) (P : net.url.URL → Prop) :
    Persistent (pickerOk (GF := GF) pk P) := by
  unfold pickerOk; infer_instance

end defs

end EtcdGrove
end Perennial
