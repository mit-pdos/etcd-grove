/-
# `run`'s send callback from the transport (2026-11-22)

`StartNode` gives `newReplica` the transport's `t.Send` as `run`'s send callback (`sendSpec γ id f`,
`Defs.lean`). `kv_sendSpec`: from `Transport.Send.spec`, the transport's fixed fields and its peers,
each message `run` hands over (`msgOwn`, `sentMsg`, `msgCredits`) is one `Send` takes (`sendElem` at
`kvFacts`: the message itself, `msgOwn` being `msgPtsC` with the entries frozen; the fact `msgOkK`,
its credits made persistent in a duplicating cluster, `msgCredits_copy`, and its wire shape `MsgWf`,
`msgPtsC_wf` for the lengths of its slices and `sentMsg_shape` for its type).

`kv_sendSpec_pt` (2026-11-24, G5): the same from a peer transport's `ptSend` (`PeerTransport.lean`),
for the interface value's `Send` (`start` hands `t.Send` of its `peerTransport`).
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Transport__Send
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.PeerTransport
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Facts

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [Net.NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

/-- A pure consequence kept with its premise. -/
theorem keep_pure {P : IProp GF} {φ : Prop} (h : P ⊢ ⌜φ⌝) : P ⊢ P ∗ ⌜φ⌝ :=
  (and_intro .rfl h).trans persistent_and_sep_mp

/-- A Go slice's length is below `2^63`. -/
theorem len63 {α : Type} (vs : List α) (s : GoSlice)
    (h : vs.length = sint.nat s.len ∧ 0 ≤ sint.Z s.len) : (vs.length : Int) < 2 ^ 63 := by
  word

/-- A configuration's lists, at `csOptA`, are of Go slices' lengths. -/
theorem csOptA_wf (p : Loc) (dq : DFrac) (c : ConfStateM) :
    csOptA (GF := GF) p dq c ⊢ ⌜ConfWf c⌝ := by
  iintro Hc
  iunfold csOptA at Hc
  icases Hc with (%Hc0 | Hc | Hc)
  · ipureintro
    rw [Hc0.2]
    unfold ConfWf
    simp
  · iNamed Hc
    ihave %H1 := ownSlice_len $$ Hv
    ihave %H2 := ownSlice_len $$ Hl
    ihave %H3 := ownSlice_len $$ Ho
    ihave %H4 := ownSlice_len $$ Hn
    ipureintro
    exact ⟨len63 _ _ H1, len63 _ _ H2, len63 _ _ H3, len63 _ _ H4⟩
  · iNamed Hc
    ihave %H1 := ownSlice_len $$ Hv
    ihave %H2 := ownSlice_len $$ Hl
    ihave %H3 := ownSlice_len $$ Ho
    ihave %H4 := ownSlice_len $$ Hn
    ipureintro
    exact ⟨len63 _ _ H1, len63 _ _ H2, len63 _ _ H3, len63 _ _ H4⟩

/-- A snapshot, owned, is one `getSnapshot` reads back (`SnapWf`). -/
theorem ownSnapM_wf (p : Loc) (dq : DFrac) (sv : SnapshotM) :
    ownSnapM (GF := GF) p dq sv ⊢ ⌜SnapWf sv⌝ := by
  iintro Hsn
  iunfold ownSnapM at Hsn
  iNamed Hsn
  ihave %Hd' := ownSlice_len $$ Hd
  iunfold smOpt at Hm
  icases Hm with (%Hm0 | Hm)
  · ipureintro
    refine ⟨?_, len63 _ _ Hd'⟩
    rw [Hm0.2]
    unfold ConfWf
    simp
  · iNamed Hm
    ihave %Hc := csOptA_wf _ _ _ $$ Hc
    ipureintro
    exact ⟨Hc, len63 _ _ Hd'⟩

/-- **A message's slices are of Go slices' lengths**: its entries' data, its entry list, its context,
and its snapshot's data and configuration lists. -/
theorem msgPtsC_lens (l : Loc) (dq dqe : DFrac) (cap : Bool) (st : MsgSt) :
    msgPtsC (GF := GF) l dq dqe cap st ⊢
      ⌜(∀ e ∈ st.ents, MsgEntWf e) ∧ (st.ents.length : Int) < 2 ^ 63 ∧
        (st.ctx.length : Int) < 2 ^ 63 ∧ ∀ s, st.snap = some s → SnapWf s⌝ := by
  iintro H
  iNamed H
  ihave %Hesl := ownSlice_len $$ Hes
  ihave %Hcsl := ownSlice_len $$ Hcs
  ihave %Hl2 := BigSepL2.bigSepL2_length $$ Hents
  have key : ∀ (p : Loc) (e : EntryM), entRO (GF := GF) p e ⊢ ⌜MsgEntWf e⌝ := by
    intro p e
    unfold entRO entPts
    iintro H
    iNamed H
    ihave %h := ownSlice_len $$ Hd
    ipureintro; exact len63 _ _ h
  ihave %Hp := (BigSepL2.bigSepL2_mono_of_forall (fun {_ x1 x2} => key x1 x2)).trans
    BigSepL2.bigSepL2_pure_intro $$ Hents
  ihave %Hsn : ⌜∀ s, st.snap = some s → SnapWf s⌝ $$ [Hsn]
  · cases hs : st.snap with
    | none => ipureintro; intro s h; cases h
    | some sv =>
      simp only [snapOpt]
      ihave %H := ownSnapM_wf _ _ _ $$ Hsn
      ipureintro
      intro s h
      cases h
      exact H
  have He63 := len63 _ _ Hesl
  ipureintro
  refine ⟨?_, by rw [← Hl2]; exact He63, len63 _ _ Hcsl, Hsn⟩
  intro e he
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
  exact Hp k (els[k]'(by omega)) st.ents[k] (List.getElem?_eq_getElem (by omega))
    (List.getElem?_eq_getElem hk)

/-- A type raft sends is one raftpb names (`getMsg`'s check). -/
theorem sentShape_known (t : w32) (h : t ∈ sentShapeTypes) :
    (raftpb.msgTypeNames !! (W32 (sint.Z t))).isSome ∧ 0 ≤ sint.Z t := by
  simp only [sentShapeTypes, sentTypes, List.mem_append, List.mem_cons, List.not_mem_nil,
    _root_.or_false] at h
  rcases h with (h | h | h | h | h | h | h | h | h | h | h | h) | (h | h) <;> subst h <;>
    exact ⟨by rfl, by decide⟩

/-- **A sent message, owned, is one the transport takes** (see the file header). -/
theorem sendElem_of_sent (γ : KdNames) (cf : List w8 → Prop) (id : w64) (q : QMsg)
    (hdup : γ.r.cluster.dup = true) :
    msgOwn (GF := GF) q.loc (readyDq q.st) q.st ∗ sentMsg γ.r.cluster kdRaftN id q.st ∗
      msgCredits γ.r.cluster kdRaftN q.st ⊢ sendElem (kvFacts γ cf) q.loc := by
  iintro ⟨Hm, #Hs, Hcr⟩
  ihave #Hcr := msgCredits_copy γ.r.cluster kdRaftN q.st hdup $$ Hcr
  ihave %Hsh := sentMsg_shape γ.r.cluster kdRaftN id q.st $$ Hs
  icases keep_pure (msgPtsC_lens _ _ _ _ _) $$ Hm with ⟨Hm, %Hl⟩
  unfold sendElem
  iexists readyDq q.st, DFrac.discard, false, q.st, id
  iframe Hm
  simp only [kvFacts]
  unfold msgOkK
  iframe Hs Hcr
  ipureintro
  obtain ⟨Hk, Hk0⟩ := sentShape_known _ Hsh.1.1
  exact ⟨Hk, Hk0, Hl.1, Hl.2.1, Hl.2.2.1, Hl.2.2.2⟩

/-- **`t.Send` is `run`'s send callback** (see the file header). -/
theorem kv_sendSpec (wp_Send : Transport.Send.spec (GF := GF) (hG := hG)) (γ : KdNames)
    (cf : List w8 → Prop) (id : w64) (t : Loc) (n : NodeH) (hdup : γ.r.cluster.dup = true) :
    isTransportCore (GF := GF) (kvFacts γ cf) t γ.r.cluster kdRaftN id n ∗ isPeers (kvFacts γ cf) t ⊢
      sendSpec γ id (methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Transport.ty)
        go!"Send" #t) := by
  iintro ⟨#Ht, #Hp⟩
  unfold sendSpec
  iintro !> %msl %ms %Φ !> ⟨Hpkg, Hsl, Hms⟩ HΦ
  ihave Hel : [∗list] m ∈ ms.map QMsg.loc, sendElem (kvFacts γ cf) m $$ [Hms]
  · rw [BigSepL.bigSepL_map]
    iapply BigSepL.bigSepL_mono _ $$ Hms
    intro k q _
    exact sendElem_of_sent γ cf id q hdup
  iapply wp_Send (kvFacts γ cf) t γ.r.cluster kdRaftN id n msl (DFrac.own 1) (ms.map QMsg.loc)
    $$ [$Hpkg $Ht $Hp $Hsl $Hel]
  inext
  iintro -
  iapply HΦ
  itrivial

/-- `run`'s send callback from a peer transport's `Send` (see the file header). -/
theorem kv_sendSpec_pt (γ : KdNames) (cf : List w8 → Prop) (id : w64) (i : GoInterfaceOk)
    (hdup : γ.r.cluster.dup = true) :
    ptSend (GF := GF) (kvFacts γ cf) (interface.ok i) ⊢
      sendSpec γ id (methods i.ty go!"Send" i.v) := by
  iintro Hs
  iunfold ptSend at Hs
  icases Hs with ⟨%i', %Heq, #Hs⟩
  injection Heq with Heq
  subst Heq
  unfold sendSpec
  iintro !> %msl %ms %Φ !> ⟨Hpkg, Hsl, Hms⟩ HΦ
  ihave Hel : [∗list] m ∈ ms.map QMsg.loc, sendElem (kvFacts γ cf) m $$ [Hms]
  · rw [BigSepL.bigSepL_map]
    iapply BigSepL.bigSepL_mono _ $$ Hms
    intro k q _
    exact sendElem_of_sent γ cf id q hdup
  wp_apply Hs $$ %msl %(DFrac.own 1) %(ms.map QMsg.loc) [$Hpkg $Hsl $Hel] as -
  iapply HΦ
  itrivial

end lemmas

end kvraft
end EtcdGrove
end Perennial
