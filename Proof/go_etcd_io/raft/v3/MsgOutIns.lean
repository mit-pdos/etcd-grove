/-
**Inserting into the handed-out set** (raft-entsize §2 step 3, 2026-11-09): raft's `Ready` proofs
insert each message and entry object they hand out, at its content (`raftOutInv_insert`). Internal to
raft (not in `etc/api/raft.txt`): only raft's own proofs hand objects out.
-/
module

public import Proof.go_etcd_io.raft.v3.MsgOut

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Insert an object and its content into the handed-out set** (an element already in it is had
again). -/
theorem raftOutInv_insert (γ : RaftNames) (x : Sum (Loc × MsgC) (Loc × EntryC)) (E : CoPset)
    (HE : ↑(raftOutN γ) ⊆ E) :
    ⊢ raftOutInv (GF := GF) γ ={E}=∗ outSetR γ x := by
  unfold raftOutInv raftOutBody outSetR
  iintro #Hinv
  iinv Hinv with ⟨%S, >Ha, >#Hels⟩ Hclose
  by_cases hk : S.lookup (Pos.Countable.encode (outKey x)) = none
  · imod ghost_map_insert_persist (Pos.Countable.encode (outKey x)) () hk $$ Ha with ⟨Ha, #He⟩
    imod Hclose $$ [Ha] with -
    · inext
      iexists (<[Pos.Countable.encode (outKey x) := ()]> S)
      iframe Ha
      iapply (BigSepM.bigSepM_insert (Φ := fun (p : Pos) (_ : Unit) =>
        ghostMapElem (GF := GF) γ.out p DFrac.discard ()) hk).2
      iframe He Hels
    imodintro
    iexact He
  · obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.1 hk
    ihave #He := BigSepM.bigSepM_lookup (Φ := fun (p : Pos) (_ : Unit) =>
      ghostMapElem (GF := GF) γ.out p DFrac.discard ()) (m := S)
      (i := Pos.Countable.encode (outKey x)) (x := u) hu $$ Hels
    imod Hclose $$ [Ha] with -
    · inext
      iexists S
      iframe Ha Hels
    imodintro
    iexact He

/-- A message handed out: owned, with its `snapUf`, into the set at a content raft pins. -/
theorem msgOutR_intro (γ : RaftNames) (l : Loc) (dq : DFrac) (st : MsgSt) (E : CoPset)
    (HE : ↑(raftOutN γ) ⊆ E) :
    ⊢ raftOutInv (GF := GF) γ -∗ msgOwn l dq st -∗ snapUf l st ={E}=∗ msgOutR γ l dq st := by
  iintro #Hinv Hm #Hu
  icases msgOwn_snapUf_CC l dq st $$ [Hm] with ⟨%c, Hc, %Hok⟩
  · iframe Hm Hu
  imod raftOutInv_insert γ (.inl (l, c)) E HE $$ Hinv with #Ho
  imodintro
  unfold msgOutR
  iexists c
  iframe Hc Ho
  ipureintro; exact Hok

end lemmas

end EtcdGrove
end Perennial
