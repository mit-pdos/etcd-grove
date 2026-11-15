/-
restart3 A0 probes P2/P3 (unlinked scratch, never landed).

P2 (variant A-g, the fork's window guard): at the merge point of `applyAll` the apply thread reads
`s.consistIndex.ConsistentIndex()` (`wp_ci_get`: `ciEff γ st''.k`); when the guard
`ep.appliedi < ConsistentIndex()` is false the batch is past the window, which is what
`winNoMergedSendR`'s left disjunct gave the proof (`hW`, `EtcdServer__applyAll.lean:471`). When the
batch is inside the window the guard is true (the merge is deferred), so the fork's guard defers
exactly the in-window merges.

P3 (R2s-A as recorded): the generalized certificate `srvImageGe` (an image at a consistent index
`j` at or above the snapshot's index `i`) is a valid `NetPayload.img` (persistent), and the old one
implies it at `j = i`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RestReplay

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- P2: the guard false, the window is over (`hW`). `hk`: `applyResR`/`kvBatchR`'s
`ai₀ + |A₀| ≤ ciEff γ st.k`; `hmono`: the consistent index only rises across the batch
(`applyAll`'s `hci'`, then `Hst''.2`); `hai`: Go's index after the batch. -/
theorem probe_P2_guard (ai0 ai' ciB ciG : w64) (A₀ L : List EntryModel)
    (hk : uint.Z ai0 + A₀.length ≤ uint.Z ciB) (hmono : uint.Z ciB ≤ uint.Z ciG)
    (hai : uint.Z ai' = uint.Z ai0 + L.length) (hguard : ¬ uint.Z ai' < uint.Z ciG) :
    A₀.length ≤ L.length := by
  omega

/-- P2, converse: inside the window (`|L| < |A₀|`) the guard holds, so the fork defers the merge. -/
theorem probe_P2_guard_in (ai0 ai' ciB ciG : w64) (A₀ L : List EntryModel)
    (hk : uint.Z ai0 + A₀.length ≤ uint.Z ciB) (hmono : uint.Z ciB ≤ uint.Z ciG)
    (hai : uint.Z ai' = uint.Z ai0 + L.length) (hin : L.length < A₀.length) :
    uint.Z ai' < uint.Z ciG := by
  omega

/-- P2, the ghost rows: past the window the existing branch's `ghostOf_past` applies. -/
theorem probe_P2_ghost (rp : RestartPt) (L : List EntryModel) (ai0 ai' ciB ciG : w64)
    (hk : uint.Z ai0 + rp.A₀.length ≤ uint.Z ciB) (hmono : uint.Z ciB ≤ uint.Z ciG)
    (hai : uint.Z ai' = uint.Z ai0 + L.length) (hguard : ¬ uint.Z ai' < uint.Z ciG) :
    ghostOf rp L = L :=
  ghostOf_past rp L (probe_P2_guard ai0 ai' ciB ciG rp.A₀ L hk hmono hai hguard)

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- P3: R2s-A's certificate: an image at a consistent index `j ≥ i`. -/
def srvImageGe (on : Bool) (γ : SrvRaft) (i : w64) (D : backend.Data) : IProp GF :=
  iprop(∃ j : w64, ⌜uint.Z i ≤ uint.Z j⌝ ∗ srvImageM on γ j D)

instance srvImageGe_persistent (on : Bool) (γ : SrvRaft) (i : w64) (D : backend.Data) :
    Persistent (srvImageGe (GF := GF) on γ i D) := by
  unfold srvImageGe; cases on <;> simp only [srvImageM] <;> infer_instance

/-- P3: R2s-A's `srvNet`, with only `img` changed. -/
def srvNetGe (γ : SrvRaft) : NetPayload GF :=
  { srvNet (GF := GF) γ with
    img := fun i D => srvImageGe γ.authOn γ i D
    img_pers := fun i D => by infer_instance }

/-- P3: today's certificate gives R2s-A's at `j = i` (the senders outside a window). -/
theorem probe_P3_ofEq (on : Bool) (γ : SrvRaft) (i : w64) (D : backend.Data) :
    srvImageM (GF := GF) on γ i D ⊢ srvImageGe on γ i D := by
  iintro #H
  iunfold srvImageGe
  iexists i
  iframe H
  ipureintro; exact Int.le_refl _

end defs

end EtcdGrove
end Perennial
