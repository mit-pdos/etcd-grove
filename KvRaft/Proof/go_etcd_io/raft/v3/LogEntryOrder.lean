-- The copy for the part `KvRaft/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/LogEntryOrder.lean` (etc/copy-part.py; rerun it, do not edit).
/- Order of the physical entries in any well-formed, recorded Raft log. -/
module
public import KvRaft.Proof.go_etcd_io.raft.v3.Protocol.Ghost

@[expose] public section
noncomputable section
namespace Perennial
namespace EtcdGrove
open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

variable [GooseExts] {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF]

theorem logRecs_entryOrder (γ : RaftNames) (F : List EntryM) (hw : PlogWf base0 F) :
    logRecs (GF := GF) γ base0 F ⊢ ⌜F.Pairwise (fun a b =>
      uint.nat a.Term' ≤ uint.nat b.Term' ∧ uint.nat a.Index' < uint.nat b.Index')⌝ := by
  iintro #Hlog
  ihave %hm := recs_mono γ F hw $$ Hlog
  ipureintro
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hei := List.getElem?_eq_getElem hi
  have hej := List.getElem?_eq_getElem hj
  have hidxi := hw _ _ hei
  have hidxj := hw _ _ hej
  have hti := plogTermAt_lookup base0 _ _ i _ hei hidxi
  have htj := plogTermAt_lookup base0 _ _ j _ hej hidxj
  have hle := hm _ _ _ _ (by omega) hti htj
  constructor <;> word
end EtcdGrove
end Perennial
