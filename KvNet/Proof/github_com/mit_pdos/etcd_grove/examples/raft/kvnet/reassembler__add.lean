/-
The proof of `KvNet/Spec/.../kvnet/reassembler__add.lean` (kvudp, phase 2: `notes/kvudp-proof-plan.md`).
The sender's messages in progress are read at their names (`ownPartials_names`); the one of the
fragment's name is carved out of the list (found, or a new one appended), the chunk is stored in its
empty slot (`slots_set`; non-nil: the fragment's chunk is nonempty), and once every slot holds its
chunk, the chunks, which agree by `udpMsgAt` with the body recorded under the name, make that body
(`chunks_flatten`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.reassembler__add
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Stats__add

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net Udp go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [HasExt udpExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [net_sem : net.Assumptions] [net_udp_sem : net.UdpFieldAssumptions]

local notation "KMsgID" => github_com.mit_pdos.etcd_grove.examples.raft.kvnet.msgID

/-- `ownPartial` at a known name. -/
private def ownPartialK (F : KvFacts GF) (γu : UdpNames) (src : w64) (p : Loc) (mid : KMsgID) :
    IProp GF :=
  iprop(∃ (cs : GoSlice) (chs : List GoSlice) (hv tp : w32) (got : List Bool),
    p.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.«partial», go!"id"] ↦ mid ∗
    p.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.«partial», go!"chunks"] ↦ cs ∗
    p.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.«partial», go!"have"] ↦ hv ∗
    p.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.«partial», go!"top"] ↦ tp ∗
    cs ↦* chs ∗ ⌜got.length = chs.length ∧ uint.nat hv = (got.filter (fun x => x)).length⌝ ∗
    [∗list] i ↦ c ∈ chs,
      chunkSlot F γu (src, mid.boot', mid.seq') chs.length i c ∗ ⌜(got[i]? = some true) ↔ c ≠ slice.nil⌝)

private theorem ownPartial_K (F : KvFacts GF) (γu : UdpNames) (src : w64) (p : Loc) :
    ownPartial F γu src p ⊣⊢ ∃ mid, ownPartialK F γu src p mid := by
  unfold ownPartial ownPartialK
  constructor
  · iintro ⟨%mid, %cs, %chs, %hv, %tp, %got, H⟩
    iexists mid, cs, chs, hv, tp, got
    iexact H
  · iintro ⟨%mid, %cs, %chs, %hv, %tp, %got, H⟩
    iexists mid, cs, chs, hv, tp, got
    iexact H

/-- A message in progress of a list, at its known name. -/
private def ownPK (F : KvFacts GF) (γu : UdpNames) (src : w64) (mids : List KMsgID) (j : Nat)
    (p : Loc) : IProp GF :=
  iprop(∃ m, ⌜mids[j]? = some m⌝ ∗ ownPartialK F γu src p m)

/-- The names of a list of messages in progress. -/
private theorem ownPartials_names (F : KvFacts GF) (γu : UdpNames) (src : w64) (ps : List Loc) :
    ([∗list] p ∈ ps, ownPartial F γu src p) ⊢
      ∃ mids : List KMsgID, ⌜mids.length = ps.length⌝ ∗
        [∗list] j ↦ p ∈ ps, ownPK F γu src mids j p := by
  induction ps with
  | nil =>
    iintro -
    iexists []
    isplitr
    · ipureintro; rfl
    iapply BigSepL.bigSepL_nil.2; iempintro
  | cons x xs ih =>
    iintro ⟨Hx, Hxs⟩
    icases (ownPartial_K F γu src x).1 $$ Hx with ⟨%m, Hx⟩
    icases ih $$ Hxs with ⟨%mids, %Hl, Hxs⟩
    iexists m :: mids
    isplitr
    · ipureintro; simp [Hl]
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hx]
    · iunfold ownPK; iexists m; iframe Hx; ipureintro; rfl
    have hs : ∀ k y, ownPK F γu src (m :: mids) (k + 1) y = ownPK F γu src mids k y := by
      intro k y; unfold ownPK; simp
    simp only [hs]
    iexact Hxs

private theorem ownPartials_of_names (F : KvFacts GF) (γu : UdpNames) (src : w64) (mids : List KMsgID)
    (ps : List Loc) :
    ([∗list] j ↦ p ∈ ps, ownPK F γu src mids j p) ⊢ [∗list] p ∈ ps, ownPartial F γu src p := by
  apply BigSepL.bigSepL_mono_of_forall
  intro k x
  iintro H
  iunfold ownPK at H
  icases H with ⟨%m, -, H⟩
  iapply (ownPartial_K F γu src x).2
  iexists m; iexact H

/-- A list of messages in progress with one carved out, put back. -/
private theorem ownPartials_restore (F : KvFacts GF) (γu : UdpNames) (src : w64) (ps : List Loc)
    (mids : List KMsgID) (jp : Nat) (p : Loc) (m : KMsgID) (hj : ps[jp]? = some p)
    (hm : mids[jp]? = some m) :
    ownPartialK F γu src p m ∗ ([∗list] j ↦ q ∈ ps, if j = jp then emp else ownPK F γu src mids j q) ⊢
      [∗list] q ∈ ps, ownPartial F γu src q := by
  iintro ⟨Hp, Hl⟩
  iapply ownPartials_of_names F γu src mids ps
  iapply (BigSepL.bigSepL_delete_cond hj).2
  iframe Hl
  iunfold ownPK
  iexists m
  iframe Hp
  ipureintro; exact hm

private theorem count_set_true (l : List Bool) (i : Nat) (h : l[i]? = some false) :
    ((l.set i true).filter (fun x => x)).length = (l.filter (fun x => x)).length + 1 := by
  induction l generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h; simp
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      simp only [List.set_cons_succ]
      cases x <;> simp [ih i h]

/-- A chunk stored in an empty slot: the slots of the message in progress, with the slot taken. -/
private theorem slots_set (F : KvFacts GF) (γu : UdpNames) (key : MsgKey) (chs : List GoSlice)
    (got : List Bool) (idx : Nat) (c' : GoSlice) (hc' : c' ≠ slice.nil) (hi : idx < chs.length)
    (hg : got.length = chs.length) :
    ([∗list] i ↦ c ∈ chs, chunkSlot F γu key chs.length i c ∗ ⌜got[i]? = some true ↔ c ≠ slice.nil⌝) ∗
      chunkSlot F γu key chs.length idx c' ⊢
    [∗list] i ↦ c ∈ chs.set idx c', chunkSlot F γu key (chs.set idx c').length i c ∗
      ⌜(got.set idx true)[i]? = some true ↔ c ≠ slice.nil⌝ := by
  iintro ⟨Hs, Hc⟩
  rw [List.length_set]
  ihave Hs := (BigSepL.bigSepL_mono (l := chs)
    (Ψ := fun i c => iprop(chunkSlot F γu key chs.length i c ∗
      ⌜i ≠ idx → ((got.set idx true)[i]? = some true ↔ c ≠ slice.nil)⌝))
    (fun {k x} _ => by
      iintro ⟨H1, %H2⟩
      iframe H1
      ipureintro
      intro hne
      rw [List.getElem?_set_ne (Ne.symm hne)]
      exact H2)) $$ Hs
  have hlk : chs[idx]? = some chs[idx] := List.getElem?_eq_getElem hi
  icases BigSepL.bigSepL_insert_acc hlk $$ Hs with ⟨-, Hset⟩
  ihave Hs := Hset $$ %c' [Hc]
  · iframe Hc; ipureintro; intro h; exact absurd rfl h
  iapply (BigSepL.bigSepL_mono (l := chs.set idx c') (fun {k x} hk => by
    iintro ⟨H1, %H2⟩
    iframe H1
    ipureintro
    by_cases hki : k = idx
    · subst hki
      rw [List.getElem?_set_self hi] at hk
      cases hk
      rw [List.getElem?_set_self (by omega)]
      simp [hc']
    · exact H2 hki)) $$ Hs

private theorem slots_pure (F : KvFacts GF) (γu : UdpNames) (key : MsgKey) (chs : List GoSlice)
    (got : List Bool) (i : Nat) (c : GoSlice) (h : chs[i]? = some c) :
    ([∗list] i ↦ c ∈ chs, chunkSlot F γu key chs.length i c ∗ ⌜got[i]? = some true ↔ c ≠ slice.nil⌝) ⊢
    ([∗list] i ↦ c ∈ chs, chunkSlot F γu key chs.length i c ∗ ⌜got[i]? = some true ↔ c ≠ slice.nil⌝) ∗
      ⌜got[i]? = some true ↔ c ≠ slice.nil⌝ := by
  iintro Hs
  icases (BigSepL.bigSepL_lookup_acc h).1 $$ Hs with ⟨⟨Hc, %Hp⟩, Hback⟩
  isplitl
  · ihave Hs := Hback $$ %c [Hc]
    · iframe Hc; ipureintro; exact Hp
    have hlt : i < chs.length := (List.getElem?_eq_some_iff.mp h).1
    have : chs.set i c = chs := by
      rw [List.getElem?_eq_getElem hlt] at h
      rw [← Option.some.inj h, List.set_getElem_self]
    rw [this]; iexact Hs
  ipureintro; exact Hp

private theorem carved_disj (F : KvFacts GF) (γu : UdpNames) (src : w64) (ps : List Loc)
    (mids : List KMsgID) (jp : Nat) (p : Loc) (hj : ps[jp]? = some p) :
    ([∗list] j ↦ q ∈ ps, if j = jp then emp else ownPK F γu src mids j q) ⊢
      [∗list] q ∈ ps, (⌜q = p⌝ ∨ ownPartial F γu src q) := by
  apply BigSepL.bigSepL_mono
  intro k x hk
  by_cases hkj : k = jp
  · subst hkj
    rw [hj] at hk; cases hk
    simp only [↓reduceIte]
    iintro -
    ileft; ipureintro; trivial
  · simp only [hkj, ↓reduceIte]
    iintro H
    iright
    iunfold ownPK at H
    icases H with ⟨%m, -, H⟩
    iapply (ownPartial_K F γu src x).2
    iexists m; iexact H

/-- A new message in progress: every slot empty. -/
private theorem slots_empty (F : KvFacts GF) (γu : UdpNames) (key : MsgKey) (n m : Nat) :
    ⊢ [∗list] i ↦ c ∈ List.replicate m (zero_val GoSlice),
        chunkSlot F γu key n i c ∗ ⌜(List.replicate m false)[i]? = some true ↔ c ≠ slice.nil⌝ := by
  apply BigSepL.bigSepL_intro
  intro k x hk
  have hx : x = zero_val GoSlice := List.eq_of_mem_replicate (List.mem_of_getElem? hk)
  have hkm : k < m := by
    have := (List.getElem?_eq_some_iff.mp hk).1; simpa using this
  have hz : zero_val GoSlice = slice.nil := rfl
  subst hx
  iintro -
  isplitl
  · iunfold chunkSlot; ileft; ipureintro; exact hz
  ipureintro
  rw [List.getElem?_replicate_of_lt hkm, hz]
  simp

/-- A new message in progress appended to its sender's list, carved out. -/
private theorem carved_snoc (F : KvFacts GF) (γu : UdpNames) (src : w64) (ps : List Loc)
    (mids : List KMsgID) (p : Loc) (m : KMsgID) (hl : mids.length = ps.length) :
    ([∗list] j ↦ q ∈ ps, ownPK F γu src mids j q) ⊢
      [∗list] j ↦ q ∈ ps ++ [p], if j = ps.length then emp else ownPK F γu src (mids ++ [m]) j q := by
  iintro H
  iapply BigSepL.bigSepL_snoc.2
  isplitl
  · iapply (BigSepL.bigSepL_mono (fun {k x} hk => by
      have hlt : k < ps.length := (List.getElem?_eq_some_iff.mp hk).1
      have hne : k ≠ ps.length := by omega
      simp only [hne, ↓reduceIte]
      unfold ownPK
      rw [List.getElem?_append_left (by omega)])) $$ H
  simp only [↓reduceIte]
  iempintro

/-- A map of owned slices, at one key: the slice there (nil if none), and the map back with any
slice at that key. -/
private theorem bigSepM_slice_acc (Ψ : w64 → GoSlice → IProp GF) (M : GMap w64 GoSlice) (k : w64)
    (h0 : ⊢ Ψ k (zero_val GoSlice)) :
    ([∗map] k ↦ v ∈ M, Ψ k v) ⊢
      Ψ k ((M !! k).getD (zero_val GoSlice)) ∗ ∀ x, Ψ k x -∗ [∗map] k ↦ v ∈ <[k := x]> M, Ψ k v := by
  iintro HM
  cases h : M !! k with
  | none =>
    simp only [Option.getD_none]
    isplitl []
    · iapply h0
    iintro %x Hx
    iapply (BigSepM.bigSepM_insert h).2
    iframe Hx HM
  | some v =>
    simp only [Option.getD_some]
    icases (BigSepM.bigSepM_delete h).1 $$ HM with ⟨Hv, HM⟩
    iframe Hv
    iintro %x Hx
    iapply BigSepM.bigSepM_insert_delete.2
    iframe Hx HM

/-- The same, read only. -/
private theorem bigSepM_slice_acc_ro (Ψ : w64 → GoSlice → IProp GF) (M : GMap w64 GoSlice) (k : w64)
    (h0 : ⊢ Ψ k (zero_val GoSlice)) :
    ([∗map] k ↦ v ∈ M, Ψ k v) ⊢
      Ψ k ((M !! k).getD (zero_val GoSlice)) ∗ (Ψ k ((M !! k).getD (zero_val GoSlice)) -∗
        [∗map] k ↦ v ∈ M, Ψ k v) := by
  iintro HM
  cases h : M !! k with
  | none =>
    simp only [Option.getD_none]
    isplitl []
    · iapply h0
    iintro -
    iexact HM
  | some v =>
    simp only [Option.getD_some]
    iapply (BigSepM.bigSepM_lookup_acc h).1 $$ HM

set_option maxHeartbeats 4000000 in
theorem reassembler.add.wp_proof
    (wp_add : Stats.add.spec (GF := GF) (hG := hG)) :
    reassembler.add.spec (GF := GF) (hG := hG) := by
  intro F γu r d dg
  wp_start as ⟨Hr, Hd, %Hkind, #Hfok⟩
  ihave #Hfok' := Hfok
  iunfold udpFragOk at Hfok'
  icases Hfok' with ⟨%B, #HB, #HBok, %HfragB⟩
  iunfold ownReassembler at Hr
  icases Hr with ⟨%pm, %dm, %lm, %sts, %P, %D, %Ls, #Hpm, #Hdm, #Hlm, #Hsts, #Hs, HP, HD, HLs, HPs, HDs⟩
  iunfold dgOwn at Hd
  icases Hd with ⟨%Hdeq, Hch⟩
  obtain ⟨Hdk, Hdsrc, Hddst, Hdboot, Hdseq, Hdidx, Hdtot⟩ := Hdeq
  try wp_auto
  -- the completed names: a duplicate is dropped
  wp_apply (wp_map_lookup1 (K := w64) (V := GoSlice) go.uint64 _ dm D d.from' (DFrac.own 1)) $$ HD as HD
  icases bigSepM_slice_acc_ro _ D d.from' ?_ $$ HDs with ⟨⟨%ds, Hds, Hdsc⟩, HDs⟩
  · iexists []
    isplitl
    · iapply ownSlice_nil
    · iapply ownSliceCap_nil
  generalize (D !! d.from').getD (zero_val GoSlice) = dsl
  try wp_auto
  ihave %Hdsl := ownSlice_len $$ Hds
  ihave IH : iprop(∃ (k : w64) (xv : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.doneMsg),
      "i" ∷ i_ptr ↦ k ∗ "x" ∷ x_ptr ↦ xv ∗ "Hds" ∷ dsl ↦* ds ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (ds.length : Int)⌝) $$ [i x Hds]
  · iexists W64 0, _
    iframe i x Hds
    ipureintro; exact ⟨by decide, by word⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat k < ds.length := by rw [Hdsl.1]; word
    obtain ⟨xd, Hxd⟩ : ∃ q, ds[sint.nat k]? = some q := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z dsl.len := ⟨Hk.1, Hif⟩
    simp only [Hbnd', _root_.and_self]
    wp_apply wp_load_slice_index dsl (sint.Z k) _ (DFrac.own 1) xd Hk.1 $$ [Hds] as Hds
    · iframe Hds; ipureintro; exact Hxd
    try wp_auto
    have Hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    wp_if_destruct
    all_goals try wp_if_destruct
    all_goals try wp_auto
    all_goals first
      | (-- not this name
         wp_for_post
         iframe
         iexists k + W64 1, xd
         iframe
         ipureintro; exact ⟨by word, by word⟩)
      | (-- a duplicate of a completed message
         wp_apply wp_add sts (W64 26) (by decide) (by decide) $$ [$Hpkg $Hs]
         try wp_auto
         cases xd.snap'
         all_goals try wp_auto
         all_goals wp_for_post
         all_goals
           ihave HDs := HDs $$ [Hds Hdsc]
           · iexists ds; iframe
           iapply HΦ
           isplitl
           · iunfold ownReassembler
             iexists pm, dm, lm, sts, P, D, Ls
             iframe Hpm Hdm Hlm Hsts Hs
             iframe
           ileft; ipureintro; rfl)
  -- the messages in progress of the sender: the one of this name, if any (the last)
  ihave HDs := HDs $$ [Hds Hdsc]
  · iexists ds; iframe
  try wp_auto
  wp_apply (wp_map_lookup1 (K := w64) (V := GoSlice) go.uint64 _ pm P d.from' (DFrac.own 1)) $$ HP as HP
  icases bigSepM_slice_acc _ P d.from' ?_ $$ HPs with ⟨⟨%ps, Hps, Hpsc, Hown⟩, HPs⟩
  · iexists []
    isplitl
    · iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    iapply BigSepL.bigSepL_nil.2; iempintro
  generalize hpsl : (P !! d.from').getD (zero_val GoSlice) = psl at *
  icases ownPartials_names F γu d.from' ps $$ Hown with ⟨%mids, %Hmids, Hown⟩
  try clear Hif
  try wp_auto
  ihave %Hpsl := ownSlice_len $$ Hps
  ihave IH : iprop(∃ (k : w64) (xv pv : Loc),
      "i" ∷ i_ptr ↦ k ∗ "x" ∷ x_ptr ↦ xv ∗ "p" ∷ p_ptr ↦ pv ∗ "Hps" ∷ psl ↦* ps ∗
      "Hown" ∷ ([∗list] j ↦ q ∈ ps, ownPK F γu d.from' mids j q) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (ps.length : Int)⌝ ∗
      "%Hfound" ∷ ⌜pv = null ∨ ∃ jp : Nat, ps[jp]? = some pv ∧
        mids[jp]? = some ({ boot' := d.boot', seq' := d.seq' } : KMsgID)⌝) $$ [i x p Hps Hown]
  · iexists W64 0, _, _
    iframe i x p Hps Hown
    ipureintro; exact ⟨⟨by decide, by word⟩, Or.inl rfl⟩
  wp_for IH
  wp_if_destruct
  · have Hif' : sint.Z k < sint.Z psl.len :=
      Hif
    have Hlt : sint.nat k < ps.length := by rw [Hpsl.1]; word
    obtain ⟨q, Hq⟩ : ∃ q, ps[sint.nat k]? = some q := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z psl.len := ⟨Hk.1, Hif'⟩
    simp only [Hbnd', _root_.and_self]
    wp_apply wp_load_slice_index psl (sint.Z k) _ (DFrac.own 1) q Hk.1 $$ [Hps] as Hps
    · iframe Hps; ipureintro; exact Hq
    icases (BigSepL.bigSepL_lookup_acc Hq).1 $$ Hown with ⟨Hq, Hown⟩
    iunfold ownPK at Hq
    icases Hq with ⟨%m, %Hm, Hq⟩
    iunfold ownPartialK at Hq
    icases Hq with ⟨%cs, %chs, %hv, %tp, %got, Hqid, Hqrest⟩
    try wp_auto
    have Hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    have Hset : ps.set (sint.nat k) q = ps := by
      rw [List.getElem?_eq_getElem Hlt] at Hq
      rw [← Option.some.inj Hq, List.set_getElem_self]
    wp_if_destruct
    all_goals try wp_if_destruct
    all_goals try wp_auto
    all_goals
      ihave Hown := Hown $$ %q [Hqid Hqrest]
      · iunfold ownPK; iexists m
        isplitr
        · ipureintro; exact Hm
        iunfold ownPartialK; iexists cs, chs, hv, tp, got; iframe
      rw [Hset]
      wp_for_post
      iframe
    all_goals first
      | (iexists k + W64 1, q, q
         iframe
         ipureintro
         refine ⟨⟨by word, by word⟩, Or.inr ⟨sint.nat k, Hq, ?_⟩⟩
         rw [Hm]; congr 1; cases m; simp_all; done)
      | (iexists k + W64 1, q, pv
         iframe
         ipureintro; exact ⟨⟨by word, by word⟩, Hfound⟩)
  try wp_auto
  -- the message in progress of this name: found, or a new one
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ r_ptr ↦ r ∗ d_ptr ↦ d ∗
      id_ptr ↦ ({ boot' := d.boot', seq' := d.seq' } : KMsgID) ∗
      ∃ (psl : GoSlice) (ps : List Loc) (mids : List KMsgID) (jp : Nat) (pv : Loc),
        ps_ptr ↦ psl ∗ p_ptr ↦ pv ∗ psl ↦* ps ∗ ownSliceCap Loc psl (DFrac.own 1) ∗
        pm ↦$ <[d.from' := psl]>P ∗
        ([∗list] j ↦ q ∈ ps, if j = jp then emp else ownPK F γu d.from' mids j q) ∗
        ownPartialK F γu d.from' pv ({ boot' := d.boot', seq' := d.seq' } : KMsgID) ∗
        ⌜ps[jp]? = some pv ∧ mids[jp]? = some ({ boot' := d.boot', seq' := d.seq' } : KMsgID)⌝)))
    $$ [r d id ps p Hps Hpsc HP Hown]
  · wp_if_destruct
    · -- a new message in progress
      try wp_auto
      -- the oldest evicted if there are too many
      wp_bind (If _ _ _)
      iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ r_ptr ↦ r ∗
          ∃ (psl1 : GoSlice) (ps1 : List Loc) (mids1 : List KMsgID),
            ps_ptr ↦ psl1 ∗ psl1 ↦* ps1 ∗ ownSliceCap Loc psl1 (DFrac.own 1) ∗
            ([∗list] j ↦ q ∈ ps1, ownPK F γu d.from' mids1 j q) ∗ ⌜mids1.length = ps1.length⌝)))
        $$ [r ps Hps Hpsc Hown]
      · wp_if_destruct
        · wp_apply wp_add sts (W64 30) (by decide) (by decide) $$ [$Hpkg $Hs]
          try wp_auto
          ihave %Hpsw := ownSlice_wf $$ Hps
          rw [ite_eq_left (by refine ⟨by decide, by word, by word⟩)]
          icases (ownSlice_split_all (W64 1) psl (DFrac.own 1) ps ⟨by decide, by word⟩).1 $$ Hps
            with ⟨-, Hps1⟩
          ihave Hn := ownSlice_nil (V := Loc) (GF := GF) (DFrac.own 1)
          ihave Hnc := ownSliceCap_nil (V := Loc) (GF := GF)
          try wp_auto
          wp_apply (wp_slice_append (V := Loc) slice.nil [] _ (List.drop (sint.nat (W64 1)) ps)
            (DFrac.own 1)) $$ [$Hn $Hnc $Hps1] as %psl2 ⟨Hps2, Hpsc2, -⟩
          try wp_auto
          iclear Hpsc
          icases (BigSepL.bigSepL_take_drop (n := 1)).1 $$ Hown with ⟨-, Hown⟩
          have hs : ∀ k x, ownPK F γu d.from' mids (1 + k) x = ownPK F γu d.from' (mids.drop 1) k x := by
            intro k x; unfold ownPK; simp [Nat.add_comm]
          simp only [hs, List.nil_append]
          iframe
          ipureintro; simp [Hmids]
        · try wp_auto
          iframe
          ipureintro; exact Hmids
      iintro %v ⟨%Hv, r, %psl1, %ps1, %mids1, ps, Hps, Hpsc, Hown, %Hm1⟩
      subst Hv
      try wp_auto
      irename id => Hidv
      wp_apply (wp_slice_make2 (V := GoSlice) (W64 (uint.Z d.total'))) as %csl ⟨Hcs, -⟩
      · ipureintro; word
      try wp_auto
      iStructNamed «$r0»
      ihave Hp : ownPartialK F γu d.from' «$r0_ptr» ({ boot' := d.boot', seq' := d.seq' } : KMsgID)
          $$ [id chunks have' top Hcs]
      · iunfold ownPartialK
        iexists csl, _, _, d.index', List.replicate (sint.nat (W64 (uint.Z d.total'))) false
        iframe id chunks have' top Hcs
        isplitr
        · ipureintro; simp
        rw [List.length_replicate]
        iapply slots_empty
      wp_apply wp_slice_literal
      try (isplitr; (ipureintro; rfl))
      iintro %sl1 ⟨Hsl1, -⟩
      try wp_auto
      wp_apply wp_slice_append $$ [$Hps $Hpsc $Hsl1] as %psl2 ⟨Hps, Hpsc, -⟩
      try wp_auto
      wp_apply (wp_mapInsert (K := w64) (V := GoSlice) go.uint64 pm P d.from' psl2) $$ HP as HP
      try wp_auto
      ihave Hown := carved_snoc F γu d.from' ps1 mids1 «$r0_ptr» ({ boot' := d.boot', seq' := d.seq' } : KMsgID)
        Hm1 $$ Hown
      iframe
      isplitr
      · ipureintro; rfl
      ipureintro
      constructor
      · simp
      · rw [← Hm1]; simp
    · -- found: carved out of the list
      obtain ⟨jp, Hjp, Hjm⟩ := Hfound.resolve_left Hif
      icases (BigSepL.bigSepL_delete_cond Hjp).1 $$ Hown with ⟨Hp, Hown⟩
      iunfold ownPK at Hp
      icases Hp with ⟨%m, %Hm, Hp⟩
      have Hmid : m = ({ boot' := d.boot', seq' := d.seq' } : KMsgID) := by
        rw [Hjm] at Hm; exact (Option.some.inj Hm).symm
      subst Hmid
      have HPsome : P !! d.from' = some psl := by
        cases hP : P !! d.from' with
        | none =>
          exfalso
          rw [hP] at hpsl
          simp only [Option.getD_none] at hpsl
          subst hpsl
          have : ps.length = 0 := by rw [Hpsl.1]; rfl
          rw [List.length_eq_zero_iff.mp this] at Hjp
          simp at Hjp
        | some v => rw [hP] at hpsl; simp only [Option.getD_some] at hpsl; rw [hpsl]
      ihave HP : pm ↦$ <[d.from' := psl]>P $$ [HP]
      · rw [GMap.insert_id _ _ _ HPsome]; iexact HP
      try wp_auto
      iframe
      ipureintro; exact ⟨Hjp, Hjm⟩
  iintro %v ⟨%Hv, r, d, id, %psl, %ps, %mids, %jp, %pv, ps, p, Hps, Hpsc, HP, Hown, Hp, %Hjpm⟩
  subst Hv
  obtain ⟨Hjp, Hjm⟩ := Hjpm
  clear Hfound hpsl Hmids Hpsl
  ihave %Hpsl := ownSlice_len $$ Hps
  try wp_auto
  -- the fragment's place in the message
  ihave Hp' := Hp
  iunfold ownPartialK at Hp'
  icases Hp' with ⟨%cs, %chs, %hv, %tp, %got, Hpid, Hpcs, Hphv, Hptp, Hpchs, %Hgot, Hslots⟩
  ihave %Hchl := ownSlice_len $$ Hpchs
  try wp_auto
  wp_if_destruct
  all_goals try wp_if_destruct
  all_goals try wp_auto
  all_goals first
    | (-- inconsistent with the message's total: dropped
       wp_apply wp_add sts (W64 31) (by decide) (by decide) $$ [$Hpkg $Hs]
       try wp_auto
       ihave Hp : ownPartialK F γu d.from' pv _ $$ [Hpid Hpcs Hphv Hptp Hpchs Hslots]
       · iunfold ownPartialK; iexists cs, chs, hv, tp, got
         iframe Hpid Hpcs Hphv Hptp Hpchs
         isplitr
         · ipureintro; exact Hgot
         iexact Hslots
       ihave Hl := ownPartials_restore F γu d.from' _ mids jp pv _ Hjp Hjm $$ [$Hp $Hown]
       ihave HPs := HPs $$ %psl [Hps Hpsc Hl]
       · iexists _; iframe
       iapply HΦ
       isplitl
       · iunfold ownReassembler
         iexists pm, dm, lm, sts, _, D, Ls
         iframe Hpm Hdm Hlm Hsts Hs
         iframe
       ileft; ipureintro; rfl)
    | (rename_i Htot
       have Hidx := Hif
       have Hil : uint.nat d.index' < chs.length := by rw [Hchl.1, Htot]; word
       obtain ⟨c0, Hc0⟩ : ∃ c, chs[uint.nat d.index']? = some c := ⟨_, List.getElem?_eq_getElem Hil⟩
       have Hii : (sint.Z (W64 (uint.Z d.index'))).toNat = uint.nat d.index' := by
         have : uint.Z d.index' < 2 ^ 32 := by word
         word
       rw [ite_eq_left (by refine ⟨by word, by rw [Htot]; word⟩)]
       wp_apply wp_load_slice_index cs _ chs (DFrac.own 1) c0 (by word) $$ [Hpchs] as Hpchs
       · iframe Hpchs; ipureintro; rw [Hii]; exact Hc0
       try wp_auto
       wp_if_destruct
       · -- a new fragment
         try wp_auto
         wp_bind (If _ _ _)
         iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ r_ptr ↦ r ∗ d_ptr ↦ d ∗
             p_ptr ↦ pv ∗ ∃ t : w32,
             pv.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.«partial», go!"top"] ↦ t))) $$ [Hptp r d p]
         · wp_if_destruct
           · wp_apply wp_add sts (W64 27) (by decide) (by decide) $$ [$Hpkg $Hs]
             iframe
             try (ipureintro; rfl)
           · try wp_auto
             iframe
         iintro %v ⟨%Hv, r, d, p, %tp', Hptp⟩
         subst Hv
         try wp_auto
         icases slots_pure F γu _ chs got _ _ Hc0 $$ Hslots with ⟨Hslots, %Hgi⟩
         ihave %Hchk := ownSlice_len $$ Hch
         rw [ite_eq_left (by refine ⟨by word, by rw [Htot]; word⟩)]
         wp_apply wp_store_slice_index cs _ chs d.chunk' $$ [Hpchs] as Hpchs
         · iframe Hpchs; ipureintro; refine ⟨by word, ?_⟩
           rw [Hchl.1, Htot]; word
         try wp_auto
         -- the chunk recorded in its slot
         obtain ⟨_, HtotB, HidxB, HchB⟩ := HfragB
         have Hnil : d.chunk' ≠ slice.nil := by
           intro h
           have hne := (chunkAt_length B dg.index.toNat HidxB).1
           rw [← HchB] at hne
           apply hne
           rw [h] at Hchk
           exact List.length_eq_zero_iff.mp (by rw [Hchk.1]; rfl)
         have Hn : chs.length = nChunks B := by
           rw [Hchl.1, Htot, ← HtotB, ← Hdtot]; word
         have Hgl := Hgot.1
         have Hgf : got[uint.nat d.index']? = some false := by
           have hlt : uint.nat d.index' < got.length := by omega
           rw [List.getElem?_eq_getElem hlt] at Hgi ⊢
           cases hb : got[uint.nat d.index']
           · rfl
           · rw [hb] at Hgi; exact absurd rfl (Hgi.mp rfl)
         ihave Hslot : chunkSlot F γu (d.from', d.boot', d.seq') chs.length (uint.nat d.index') d.chunk' $$ [Hch]
         · iunfold chunkSlot
           iright
           iexists dg.chunk, B
           iframe Hch HBok
           isplitl
           · have hk : dg.key = (d.from', d.boot', d.seq') := by
               unfold DgM.key; rw [Hdsrc, Hdboot, Hdseq]
             rw [← hk]; iexact HB
           ipureintro; refine ⟨Hn.symm, ?_⟩
           rw [HchB, ← Hdidx]
         ihave Hslots := slots_set F γu _ chs got (uint.nat d.index') d.chunk' Hnil Hil Hgl $$ [$Hslots $Hslot]
         rw [Hii] at *
         have Hcnt := count_set_true got (uint.nat d.index') Hgf
         have Hcle := List.length_filter_le (fun x => x) (got.set (uint.nat d.index') true)
         rw [List.length_set] at Hcle
         have Hhv1 : uint.nat (hv + W32 1) = ((got.set (uint.nat d.index') true).filter (fun x => x)).length := by
           have : uint.nat hv < 2 ^ 32 - 1 := by
             have h2 : uint.Z d.total' < 2 ^ 32 := by word
             rw [Hchl.1, Htot] at Hgl
             omega
           rw [Hcnt, ← Hgot.2]; word
         wp_if_destruct
         · -- not all the chunks yet
           ihave Hp : ownPartialK F γu d.from' pv _ $$ [Hpid Hpcs Hphv Hptp Hpchs Hslots]
           · iunfold ownPartialK
             iexists cs, chs.set (uint.nat d.index') d.chunk', hv + W32 1, tp', got.set (uint.nat d.index') true
             iframe Hpid Hpcs Hphv Hptp Hpchs
             isplitr
             · ipureintro; refine ⟨by simp [Hgl], Hhv1⟩
             iexact Hslots
           ihave Hl := ownPartials_restore F γu d.from' _ mids jp pv _ Hjp Hjm $$ [$Hp $Hown]
           ihave HPs := HPs $$ %psl [Hps Hpsc Hl]
           · iexists _; iframe
           iapply HΦ
           isplitl
           · iunfold ownReassembler
             iexists pm, dm, lm, sts, _, D, Ls
             iframe Hpm Hdm Hlm Hsts Hs
             iframe
           ileft; ipureintro; rfl
         -- complete: the message leaves the messages in progress
         have Hcomplete : ¬uint.Z (hv + W32 1) < uint.Z d.total' := Hif
         repeat clear Hif
         ihave Hdisj := carved_disj F γu d.from' ps mids jp pv Hjp $$ Hown
         ihave IH : iprop(∃ (k : w64) (rv : GoSlice) (kept : List Loc) (xl : Loc),
             "i" ∷ i_ptr ↦ k ∗ "x" ∷ x_ptr ↦ xl ∗ "rest" ∷ rest_ptr ↦ rv ∗
             "Hrv" ∷ rv ↦* kept ∗ "Hrc" ∷ ownSliceCap Loc rv (DFrac.own 1) ∗
             "Hkept" ∷ ([∗list] q ∈ kept, ownPartial F γu d.from' q) ∗
             "Hps" ∷ psl ↦* ps ∗
             "Hdisj" ∷ ([∗list] q ∈ ps.drop (sint.nat k), (⌜q = pv⌝ ∨ ownPartial F γu d.from' q)) ∗
             "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (ps.length : Int)⌝)
           $$ [i x rest Hps Hdisj]
         · iexists W64 0, slice.nil, [], _
           iframe i x rest Hps
           isplitl []
           · iapply ownSlice_nil
           isplitl []
           · iapply ownSliceCap_nil
           isplitl []
           · iapply BigSepL.bigSepL_nil.2; iempintro
           simp only [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
           iframe Hdisj
           ipureintro; exact ⟨by decide, by word⟩
         wp_for IH
         wp_if_destruct
         · have Hif' : sint.Z k < sint.Z psl.len :=
             Hif
           have Hlt : sint.nat k < ps.length := by rw [Hpsl.1]; word
           obtain ⟨q, Hq⟩ : ∃ q, ps[sint.nat k]? = some q := ⟨_, List.getElem?_eq_getElem Hlt⟩
           have Hbnd' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z psl.len := ⟨Hk.1, Hif'⟩
           simp only [Hbnd', _root_.and_self]
           wp_apply wp_load_slice_index psl (sint.Z k) _ (DFrac.own 1) q Hk.1 $$ [Hps] as Hps
           · iframe Hps; ipureintro; exact Hq
           have Hdrop : ps.drop (sint.nat k) = q :: ps.drop (sint.nat k + 1) := by
             rw [List.drop_eq_getElem_cons Hlt]
             rw [List.getElem?_eq_getElem Hlt] at Hq
             rw [Option.some.inj Hq]
           have Hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
           rw [Hdrop]
           icases Hdisj with ⟨Hq, Hdisj⟩
           try wp_auto
           wp_if_destruct
           · -- the completed one: dropped
             iclear Hq
             try wp_auto
             wp_for_post
             iframe
             iexists k + W64 1, rv, kept, _
             rw [Hk1]
             iframe
             ipureintro; exact ⟨by word, by word⟩
           · -- another message in progress: kept
             icases Hq with (%Hqp | Hq)
             · exact absurd Hqp Hif
             wp_apply wp_slice_literal
             try (isplitr; (ipureintro; rfl))
             iintro %sl1 ⟨Hsl1, -⟩
             try wp_auto
             wp_apply wp_slice_append $$ [$Hrv $Hrc $Hsl1] as %rv' ⟨Hrv, Hrc, -⟩
             wp_for_post
             iframe
             iexists k + W64 1, rv', kept ++ [q], q
             rw [Hk1]
             iframe
             isplitl []
             · iapply BigSepL.bigSepL_nil.2; iempintro
             ipureintro; exact ⟨by word, by word⟩
         repeat clear Hif
         iclear Hdisj Hps Hpsc
         try wp_auto
         wp_apply (wp_mapInsert (K := w64) (V := GoSlice) go.uint64 pm _ d.from' rv) $$ HP as HP
         rw [GMap.insert_insert] at *
         ihave HPs := HPs $$ %rv [Hrv Hrc Hkept]
         · iexists kept; iframe
         try wp_auto
         -- the body, from the chunks: every slot holds its chunk of the recorded body
         have Hallg : ∀ i, i < (got.set (uint.nat d.index') true).length →
             (got.set (uint.nat d.index') true)[i]? = some true := by
           have hcnt : ((got.set (uint.nat d.index') true).filter (fun x => x)).length =
               (got.set (uint.nat d.index') true).length := by
             have h1 := List.length_filter_le (fun x => x) (got.set (uint.nat d.index') true)
             rw [← Hhv1] at h1 ⊢
             rw [List.length_set, Hgl, Hchl.1, Htot] at h1 ⊢
             have : uint.Z d.total' < 2 ^ 32 := by word
             word
           intro i hi
           rw [List.getElem?_eq_getElem hi]
           have := List.length_filter_eq_length_iff.mp hcnt _ (List.getElem_mem hi)
           simpa using this
         have Hn' : (chs.set (uint.nat d.index') d.chunk').length = nChunks B := by
           rw [List.length_set, Hn]
         have hk : dg.key = (d.from', d.boot', d.seq') := by
           unfold DgM.key; rw [Hdsrc, Hdboot, Hdseq]
         ihave %Hcsl := ownSlice_len $$ Hpchs
         ihave Hn0 := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
         ihave Hn0c := ownSliceCap_nil (V := w8) (GF := GF)
         irename body => Hbodyv
         ihave IH : iprop(∃ (k : w64) (cv bsl : GoSlice),
             "i" ∷ i_ptr ↦ k ∗ "c" ∷ c_ptr ↦ cv ∗ "Hbodyv" ∷ body_ptr ↦ bsl ∗
             "Hb" ∷ bsl ↦* ((List.range (sint.nat k)).map (chunkAt B)).flatten ∗
             "Hbc" ∷ ownSliceCap w8 bsl (DFrac.own 1) ∗
             "Hpchs" ∷ cs ↦* chs.set (uint.nat d.index') d.chunk' ∗
             "Hslots" ∷ ([∗list] i ↦ c ∈ chs.set (uint.nat d.index') d.chunk',
               iprop(chunkSlot F γu (d.from', d.boot', d.seq') (chs.set (uint.nat d.index') d.chunk').length i c ∗
                 ⌜(got.set (uint.nat d.index') true)[i]? = some true ↔ c ≠ slice.nil⌝)) ∗
             "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ ((chs.set (uint.nat d.index') d.chunk').length : Int)⌝)
           $$ [i c Hbodyv Hpchs Hslots Hn0 Hn0c]
         · iexists W64 0, _, slice.nil
           iframe i c Hbodyv Hpchs Hslots
           simp only [show sint.nat (W64 0) = 0 from rfl, List.range_zero, List.map_nil, List.flatten_nil]
           iframe Hn0 Hn0c
           ipureintro; exact ⟨by decide, by word⟩
         wp_for IH
         wp_if_destruct
         · have Hif' : sint.Z k < sint.Z cs.len :=
             Hif
           have Hlt : sint.nat k < (chs.set (uint.nat d.index') d.chunk').length := by
             rw [Hcsl.1]; word
           obtain ⟨c, Hcq⟩ : ∃ c, (chs.set (uint.nat d.index') d.chunk')[sint.nat k]? = some c :=
             ⟨_, List.getElem?_eq_getElem Hlt⟩
           have Hbnd' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z cs.len := ⟨Hk.1, Hif'⟩
           simp only [Hbnd', _root_.and_self]
           wp_apply wp_load_slice_index cs (sint.Z k) _ (DFrac.own 1) c Hk.1 $$ [Hpchs] as Hpchs
           · iframe Hpchs; ipureintro; exact Hcq
           icases (BigSepL.bigSepL_lookup_acc Hcq).1 $$ Hslots with ⟨⟨Hsl, %Hgk⟩, Hback⟩
           have Hcnn : c ≠ slice.nil :=
             Hgk.mp (Hallg _ (by rw [List.length_set, Hgl]; rw [List.length_set] at Hlt; exact Hlt))
           iunfold chunkSlot at Hsl
           icases Hsl with (%Hcn | ⟨%bs, %bk, Hc, #Hat, #Hbok, %Hbk⟩)
           · exact absurd Hcn Hcnn
           ihave #HB' := HB
           rw [hk] at *
           iunfold udpMsgAt at Hat HB'
           ihave %Hag := ghostMapElem_agree _ _ _ _ _ _ $$ Hat HB'
           subst Hag
           obtain ⟨-, Hbsk⟩ := Hbk
           try wp_auto
           wp_apply wp_slice_append $$ [$Hb $Hbc $Hc] as %bsl' ⟨Hb, Hbc, Hc⟩
           ihave Hslots := Hback $$ %c [Hc]
           · isplitl
             · iunfold chunkSlot
               iright
               iexists bs, bk
               iframe Hc Hbok
               isplitl
               · iunfold udpMsgAt; iexact Hat
               ipureintro; exact ⟨by rw [Hn'], Hbsk⟩
             ipureintro; exact Hgk
           have Hset : (chs.set (uint.nat d.index') d.chunk').set (sint.nat k) c =
               chs.set (uint.nat d.index') d.chunk' := by
             rw [List.getElem?_eq_getElem Hlt] at Hcq
             rw [← Option.some.inj Hcq, List.set_getElem_self]
           rw [Hset]
           have Hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
           try wp_auto
           wp_for_post
           iframe
           iexists k + W64 1, c, bsl'
           rw [Hk1, List.range_succ, List.map_append, List.flatten_append]
           simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
           rw [← Hbsk]
           iframe
           ipureintro; exact ⟨by word, by word⟩
         -- all the chunks, in order: the body
         have Hkn : sint.nat k = nChunks B := by
           rw [← Hn', Hcsl.1]; word
         rw [Hkn, chunks_flatten]
         wp_if_destruct
         · wp_apply wp_add sts (W64 29) (by decide) (by decide) $$ [$Hpkg $Hs]
           try wp_auto
           iapply HΦ
           isplitl [HP HPs HD HDs HLs]
           · iunfold ownReassembler
             iexists pm, dm, lm, sts, _, D, Ls
             iframe Hpm Hdm Hlm Hsts Hs
             iframe
           iright
           isplitr
           · ipureintro; rfl
           iexists B
           iframe Hb HBok
           rw [hk]; iexact HB
         ·
           try wp_auto
           iapply HΦ
           isplitl [HP HPs HD HDs HLs]
           · iunfold ownReassembler
             iexists pm, dm, lm, sts, _, D, Ls
             iframe Hpm Hdm Hlm Hsts Hs
             iframe
           iright
           isplitr
           · ipureintro; rfl
           iexists B
           iframe Hb HBok
           rw [hk]; iexact HB
       · -- a duplicate fragment
         wp_apply wp_add sts (W64 26) (by decide) (by decide) $$ [$Hpkg $Hs]
         try wp_auto
         ihave Hp : ownPartialK F γu d.from' pv _ $$ [Hpid Hpcs Hphv Hptp Hpchs Hslots]
         · iunfold ownPartialK; iexists cs, chs, hv, tp, got
           iframe Hpid Hpcs Hphv Hptp Hpchs
           isplitr
           · ipureintro; exact Hgot
           iexact Hslots
         ihave Hl := ownPartials_restore F γu d.from' _ mids jp pv _ Hjp Hjm $$ [$Hp $Hown]
         ihave HPs := HPs $$ %psl [Hps Hpsc Hl]
         · iexists _; iframe
         iapply HΦ
         isplitl
         · iunfold ownReassembler
           iexists pm, dm, lm, sts, _, D, Ls
           iframe Hpm Hdm Hlm Hsts Hs
           iframe
         ileft; ipureintro; rfl)
end proof

end raft_kvnet
end EtcdGrove
end Perennial
