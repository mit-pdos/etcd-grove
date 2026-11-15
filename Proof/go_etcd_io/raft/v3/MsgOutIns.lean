/-
**Inserting into the handed-out set** (raft-entsize §2 step 3, 2026-11-09): raft's `Ready` proofs
insert each message and entry object they hand out, at its content (`raftOutInv_insert`). Internal to
raft (not in `etc/api/raft.txt`): only raft's own proofs hand objects out.
-/
module

public import Proof.go_etcd_io.raft.v3.MsgOwnZ

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
again). (out_size C2) In a cluster with a bound on proposed data, only at a content of bounded size
(`outSizeOk`), which the element then carries (`outSetR`, whence `out_size`). -/
theorem raftOutInv_insert (γ : RaftNames) (x : Sum (Loc × MsgC) (Loc × EntryC)) (E : CoPset)
    (HE : ↑(raftOutN γ) ⊆ E) (Hsz : ∀ b, γ.maxData = some b → outSizeOk x) :
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
    iframe He
    ipureintro; exact Hsz
  · obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.1 hk
    ihave #He := BigSepM.bigSepM_lookup (Φ := fun (p : Pos) (_ : Unit) =>
      ghostMapElem (GF := GF) γ.out p DFrac.discard ()) (m := S)
      (i := Pos.Countable.encode (outKey x)) (x := u) hu $$ Hels
    imod Hclose $$ [Ha] with -
    · inext
      iexists S
      iframe Ha Hels
    imodintro
    iframe He
    ipureintro; exact Hsz

/-- A message handed out: held at a content raft pins (`msgOwnZ`, out_size C3; until then owned with
its `snapUf`), into the set at that content, whose size the cluster's flag bounds. -/
theorem msgOutR_intro (γ : RaftNames) (l : Loc) (dq : DFrac) (st : MsgSt) (E : CoPset)
    (HE : ↑(raftOutN γ) ⊆ E) :
    ⊢ raftOutInv (GF := GF) γ -∗ msgOwnZ γ.maxData.isSome l dq st ={E}=∗ msgOutR γ l dq st := by
  iintro #Hinv Hm
  unfold msgOwnZ
  icases Hm with ⟨%c, Hc, %Hok⟩
  obtain ⟨Hmod, Hsent, Hsz⟩ := Hok
  imod raftOutInv_insert γ (.inl (l, c)) E HE (fun b hb => Hsz (by rw [hb]; rfl)) $$ Hinv with #Ho
  imodintro
  unfold msgOutR
  iexists c
  iframe Hc Ho
  ipureintro; exact ⟨Hmod, Hsent⟩

end lemmas

end EtcdGrove
end Perennial
