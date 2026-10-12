/-
A new write transaction's predicate (`ownWriteTx`), built from what `beginRWTx` leaves
(`DBWriter.lean`'s `wtxInit`), the database's logger (persistent) and the facts of the
current tree (`treeStrict`).
-/
module

public import Proof.go_etcd_io.bbolt.DBWriter
public import Proof.go_etcd_io.bbolt.WriteTxLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- The current meta (the one `db.meta()` picks). -/
abbrev curMeta (v0 v1 : Meta) : Meta := if metaPick v0 v1 then v1 else v0

/-- The writer's view, from `beginRWTx`'s. -/
def wViewOf (dbl : Loc) (w : Reader) (data : Loc) (ps : Nat) (lg : GoInterface) (dl : Loc)
    (fli : GoInterface) : WView := ⟨dbl, data, ps, w.pages, w.q, lg, dl, fli, w.hwm⟩

/-- The new write transaction's records: its struct, its meta copy, no dirty page, the root
bucket (the transaction's field `root`) with its header copy at `ibl` and no node. -/
def wtxInitT (txl dbl ml ibl : Loc) (pm bm nm : GoMap) (v0 v1 : Meta) : WTx :=
  let t := txInitOf { (zero_val Tx) with writable' := true } txl dbl ml ibl pm bm nm
  ⟨t, txMetaOf true v0 v1, ∅, ∅,
    {[structFieldRef Tx go!"root" txl := ⟨t.root', (curMeta v0 v1).root', ∅, ∅, ∅, [], Src.view⟩]}⟩

theorem txMetaOf_pgid (v0 v1 : Meta) : (txMetaOf true v0 v1).pgid' = (curMeta v0 v1).pgid' := by
  unfold txMetaOf; simp

/-- The write transaction `beginRWTx` begins, as `ownWriteTx`. The facts are the database's:
the current tree strict, its root page not 0 and the high-water mark at least 2, the view's
locations and page size. -/
theorem ownWriteTx_init (dbl txl : Loc) (w : Reader) (data : Loc) (ps : Nat) (v0 v1 : Meta)
    (lg : GoInterface) (dl : Loc) (fli : GoInterface)
    (hhwmw : w.hwm = uint.nat (curMeta v0 v1).pgid')
    (hstrict : treeStrict w.pages (uint.nat (curMeta v0 v1).pgid')
      (uint.nat (curMeta v0 v1).root'.root'))
    (hroot : (curMeta v0 v1).root'.root' ≠ W64 0) (hhwm : 2 ≤ uint.nat (curMeta v0 v1).pgid')
    (hdata : data.locCar ≠ 0) (hps : 80 ≤ ps ∧ ps < 2 ^ 32)
    (hbound : ∀ id pg, w.pages !! id = some pg → id * ps < 281474976710655) (hdbl : dbl ≠ null)
    (hlg : lg = interface.nil ∨ lg = discardIface dl) :
    wtxInit dbl txl w data ps v0 v1 ∗ structFieldRef DB go!"logger" dbl ↦□ lg ∗
      (globalAddr discardLogger ↦□ dl : IProp GF) ∗
      structFieldRef DB go!"freelist" dbl ↦{DFrac.own halfQ} fli ⊢
    ∃ T, ownWriteTx (wViewOf dbl w data ps lg dl fli) txl T := by
  iintro ⟨Hi, #Hlg, #Hdl, Hfl⟩
  unfold wtxInit
  icases Hi with ⟨%ml, %ibl, %pm, %bm, %nm, Ht, Hml, Hibl, Hpm, Hbm, Hnm, Hdata, #Hps, Hpv⟩
  icases (TxW_split_root _ _ _).1 $$ Ht with ⟨Hroot, Hrest⟩
  iexists wtxInitT txl dbl ml ibl pm bm nm v0 v1
  unfold ownWriteTx ownWriteTxG wView
  simp only [wtxInitT, wViewOf, txInitOf, newBucketOf]
  iframe Hrest Hml Hpm Hdata Hpv Hfl
  iframe #
  isplitl [Hroot Hibl Hbm Hnm]
  · isplitl []
    · iapply BigSepM.bigSepM_empty.2; iempintro
    iapply (bigSepM_gsingleton _ _ _).2
    unfold bktOwn pageOwn
    simp only [txInitOf, newBucketOf]
    iframe
    isplitl []
    · simp only [ite_true]; itrivial
    iapply BigSepM.bigSepM_empty.2; iempintro
  ipureintro
  refine ⟨hlg, ⟨hdata, hps.1, hps.2, hbound, hstrict.2⟩, ?_⟩
  refine ⟨by simp [txInitOf], by simp [txInitOf], hdbl, rfl, by rw [txMetaOf_pgid]; exact hhwm, by rw [txMetaOf_pgid]; simp [wViewOf, hhwmw],
    by rw [GMap.lookup_singleton]; rfl, ?_⟩
  intro bl B hB
  rw [GMap.lookup_singleton_Some] at hB
  obtain ⟨-, rfl⟩ := hB
  refine ⟨by simp [txInitOf, newBucketOf], ?_, by simp⟩
  rw [txMetaOf_pgid]
  have hlt : uint.nat (curMeta v0 v1).root'.root' < uint.nat (curMeta v0 v1).pgid' := by
    cases hstrict.1 with
    | page _ _ hlt _ _ _ => exact hlt
  unfold bktClean
  simp only
  refine ⟨fun h _ => absurd h hroot, fun _ => ⟨hlt, fun _ => hstrict.1⟩, fun _ => ⟨trivial, trivial⟩,
    fun h => absurd rfl h, by simp, fun _ => trivial, fun h => absurd h hroot, by simp, ?_, ?_⟩
  · intro l1 i1 c1 _ _ _ h; obtain ⟨r, _, h, _⟩ := h; simp at h
  · intro l i c h; obtain ⟨r, _, h, _⟩ := h; simp at h

end init

end bbolt
end EtcdGrove
end Perennial
