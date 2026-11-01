/-
Lean-first (no Rocq counterpart).

# The reads' slots (2026-10-30, kvreconf-final; `notes/spec-first-study/kvreconf-read-spec.md`)

`Cluster.Read` linearizes at the first change of the store's history, from the start of the call
on, after which `key` has the value it returns. It does not know that value until it returns, so
it creates a prophecy at its start (`primitive.NewProph`) and resolves it with the answer before
returning (gokv's `trusted_proph.ResolveBytes`): the prophecy's head is the answer, `ansOf`. The
read registers a slot (`readSlot`, `Defs.lean`) holding its caller's update, with the history at
its start and the prophesied answer:

- `kvr_read_start`: at the start, the slot is registered; fired at once if the key's value now is
  the answer;
- `readReg_grow` (in `kvr_propAu`'s first occurrence, the only place the history grows): each
  pending slot whose answer is the key's value in the grown history fires, by helping;
- `kvr_read_take`: after the answer `v` (`v = kvFold L key`, `L` a committed history extending
  the start), the slot cannot be pending (`L` was a history since the start whose value is the
  answer), so it fired and holds `Φ v`; its element is deleted.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.ClientLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- What a read's update may open, inside the store's invariant. -/
theorem kvrMask_sub_rkv : kvrMask ⊆ ⊤ \ ↑rkvN := fun x hx => by
  have h := Std.LawfulSet.mem_diff.mp (kvrMask_sub x hx)
  exact Std.LawfulSet.mem_diff.mpr ⟨Std.LawfulSet.diff_subset_left x h.1, h.2⟩

open Classical in
/-- The answer a read's prophecy says it returns: the string at the head of its values. -/
def ansOf (pvs : List val) : Option (List w8) :=
  if h : ∃ s : List w8, pvs.head? = some #s then some h.choose else none

end pure

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [StorageModel GF] [AllG GF]

include sem in
theorem ansOf_cons (s : List w8) (pvs : List val) : ansOf (#s :: pvs) = some s := by
  have h : ∃ s' : List w8, (#s :: pvs).head? = some #s' := ⟨s, rfl⟩
  unfold ansOf
  rw [dite_cond_eq_true (eq_true h)]
  have hc : some (#s : val) = some (#h.choose : val) := h.choose_spec
  exact congrArg some (go.intoVal_inj (V := GoString) (Option.some.inj hc)).symm

/-- **A read starts**: its slot registered at the current history `H0`, with the answer `ans` (see
the file header). -/
theorem kvr_read_start (γr : RNames) (key : List w8) (ans : Option (List w8))
    (Φ : List w8 → IProp GF) (E : CoPset) (HE : ↑rkvN ⊆ E) (HE' : kvrMask ⊆ E \ ↑rkvN) :
    ⊢ rkvInv (GF := GF) γr -∗ £ 1 -∗
      AU <{ ∃∃ (x : KVMap), rkvVal γr x }> @ kvrMask, ∅ <{ rkvVal γr x, COMM Φ (x key) }> ={E}=∗
      ∃ (γΦ : GName) (H0 : List (List w8)), γΦ ↪[γr.rds] (⟨key, H0, ans⟩ : ReadRec) ∗
        savedPredOwn γΦ DFrac.discard Φ ∗ kvLb γr H0 := by
  iintro #Hinv Hlc Hau
  unfold rkvInv rkvInvBody
  iinv Hinv with ⟨%ops, %n, %Mi, %RS, %RMi, %O, %U, >Hc, Hsl⟩ Hclose
  iunfold rkvSlots at Hsl
  icases Hsl with ⟨Hsl, Hrd⟩
  iunfold readReg at Hrd
  icases Hrd with ⟨%RD, >HRD, Hrds⟩
  iunfold kvCore at Hc
  icases Hc with ⟨Hops, Hv, HU, Hn, HMi, HRS, HRMi, HO, %Hok, %Hodm, %Hsh⟩
  icases ownCommittedOps_get_lb γr.cluster ops $$ Hops with ⟨Hops, %l, #Hl, %Hl'⟩
  imod saved_pred_alloc_cofinite Φ RD.domList DFrac.discard trivial with ⟨%γΦ, %Hfr, #Hsp⟩
  have HRD0 : RD !! γΦ = none := by
    cases h : RD !! γΦ with
    | none => rfl
    | some _ => exact absurd ((GMap.mem_dom_list RD γΦ).mpr (by rw [h]; rfl)) Hfr
  imod ghost_map_insert γΦ (⟨key, logHist ops, ans⟩ : ReadRec) HRD0 $$ HRD with ⟨HRD, Hel⟩
  ihave Hslot : |={E \ ↑rkvN}=> ghostVar γr.val (1 : Qp).half (logHist ops) ∗
      readSlot γr γΦ ⟨key, logHist ops, ans⟩ (logHist ops) $$ [Hv Hlc Hau]
  · by_cases Hfire : ans = some (kvFold (logHist ops) key)
    · -- the key's value now is the answer: the update runs now
      ihave Hau := atomic_update_mask_weaken HE' $$ Hau
      ihave Hacc := aupd_aacc $$ Hau
      unfold atomic_acc
      imod Hacc with Hacc
      isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
      icases Hacc with ⟨%x, Hx, Hucl⟩
      ihave %Hxeq := rkvVal_agree γr (logHist ops) x $$ Hv Hx
      subst Hxeq
      icases Hucl with ⟨-, Hcommit⟩
      isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
      imod Hcommit $$ Hx with HΦ
      imodintro
      iframe Hv
      unfold readSlot
      iexists Φ
      iframe Hsp
      iright
      iexists kvFold (logHist ops) key
      iframe HΦ
      ipureintro; exact Hfire
    · imodintro
      iframe Hv
      unfold readSlot
      iexists Φ
      iframe Hsp
      ileft
      iframe Hlc Hau
      ipureintro
      intro H' h1 h2
      have : H' = logHist ops := h2.eq_of_length (Nat.le_antisymm h2.length_le h1.length_le)
      subst this; exact Hfire
  imod Hslot with ⟨Hv, Hslot⟩
  imod Hclose $$ [Hops Hv HU Hn HMi HRS HRMi HO Hsl Hrds HRD Hslot] with -
  · inext
    iexists ops, n, Mi, RS, RMi, O, U
    isplitl [Hops Hv HU Hn HMi HRS HRMi HO]
    · unfold kvCore
      iframe Hops Hv HU Hn HMi HRS HRMi HO
      ipureintro; exact ⟨Hok, Hodm, Hsh⟩
    unfold rkvSlots readReg
    iframe Hsl
    iexists RD.insert γΦ ⟨key, logHist ops, ans⟩
    iframe HRD
    iapply (BigSepM.bigSepM_insert (Φ := fun k s => readSlot (GF := GF) γr k s (logHist ops))
      HRD0).2
    iframe Hslot Hrds
  imodintro
  iexists γΦ, logHist ops
  iframe Hel Hsp
  unfold kvLb
  iexists l
  iframe Hl
  ipureintro; rw [← Hl', logHist_opsOf]

/-- A read's slot as the history grows by `d`: a pending slot fires if the key's value in the
grown history is its answer (see the file header). -/
theorem readSlot_grow (γr : RNames) (k : GName) (s : ReadRec) (H : List (List w8))
    (d : List w8) (E : CoPset) (HE : kvrMask ⊆ E) :
    ⊢ ghostVar (GF := GF) γr.val (1 : Qp).half (H ++ [d]) -∗ ▷ readSlot γr k s H ={E}=∗
      ghostVar γr.val (1 : Qp).half (H ++ [d]) ∗ ▷ readSlot γr k s (H ++ [d]) := by
  iintro Hv Hs
  iunfold readSlot at Hs
  icases Hs with ⟨%Φ, #Hsp, Hst⟩
  icases Hst with (⟨>%Hpend, >Hlc, Hau⟩ | ⟨%v, Hf⟩)
  · by_cases Hfire : s.ans = some (kvFold (H ++ [d]) s.key)
    · imod lc_fupd_elim_later $$ Hlc Hau with Hau
      ihave Hau := atomic_update_mask_weaken HE $$ Hau
      ihave Hacc := aupd_aacc $$ Hau
      unfold atomic_acc
      imod Hacc with Hacc
      isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
      icases Hacc with ⟨%x, Hx, Hucl⟩
      ihave %Hxeq := rkvVal_agree γr (H ++ [d]) x $$ Hv Hx
      subst Hxeq
      icases Hucl with ⟨-, Hcommit⟩
      isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
      imod Hcommit $$ Hx with HΦ
      imodintro
      iframe Hv
      inext
      unfold readSlot
      iexists Φ
      iframe Hsp
      iright
      iexists kvFold (H ++ [d]) s.key
      iframe HΦ
      ipureintro; exact Hfire
    · imodintro
      iframe Hv
      inext
      unfold readSlot
      iexists Φ
      iframe Hsp
      ileft
      iframe Hlc Hau
      ipureintro
      intro H' h1 h2
      rcases List.prefix_concat_iff.mp h2 with h | h
      · subst h; exact Hfire
      · exact Hpend H' h1 h
  · imodintro
    iframe Hv
    inext
    unfold readSlot
    iexists Φ
    iframe Hsp
    iright
    iexists v
    iframe Hf

/-- Every read slot as the history grows by `d` (`readSlot_grow`). -/
theorem readSlots_grow (γr : RNames) (H : List (List w8)) (d : List w8) (E : CoPset)
    (HE : kvrMask ⊆ E) : ∀ RD : GMap GName ReadRec,
    ⊢ ghostVar (GF := GF) γr.val (1 : Qp).half (H ++ [d]) -∗
      ([∗map] k ↦ s ∈ RD, ▷ readSlot γr k s H) ={E}=∗
      ghostVar γr.val (1 : Qp).half (H ++ [d]) ∗ [∗map] k ↦ s ∈ RD, ▷ readSlot γr k s (H ++ [d]) := by
  intro RD
  induction RD using GMap.map_ind with
  | h0 =>
    iintro Hv -
    imodintro
    iframe Hv
    iapply BigSepM.bigSepM_empty.2
    itrivial
  | hins k s m Hk IH =>
    iintro Hv Hm
    icases (BigSepM.bigSepM_insert (Φ := fun k s => iprop(▷ readSlot (GF := GF) γr k s H))
      Hk).1 $$ Hm with ⟨Hs, Hm⟩
    imod IH $$ Hv Hm with ⟨Hv, Hm⟩
    imod readSlot_grow γr k s H d E HE $$ Hv Hs with ⟨Hv, Hs⟩
    imodintro
    iframe Hv
    iapply (BigSepM.bigSepM_insert (Φ := fun k s => iprop(▷ readSlot (GF := GF) γr k s (H ++ [d])))
      Hk).2
    iframe Hs Hm

/-- **The reads' registry as the history grows by `d`** (`kvr_propAu`'s first occurrence). -/
theorem readReg_grow (γr : RNames) (H : List (List w8)) (d : List w8) (E : CoPset)
    (HE : kvrMask ⊆ E) :
    ⊢ ghostVar (GF := GF) γr.val (1 : Qp).half (H ++ [d]) -∗ ▷ readReg γr H ={E}=∗
      ghostVar γr.val (1 : Qp).half (H ++ [d]) ∗ ▷ readReg γr (H ++ [d]) := by
  iintro Hv Hrd
  iunfold readReg at Hrd
  icases Hrd with ⟨%RD, >HRD, Hrds⟩
  ihave Hrds := (BigSepM.bigSepM_later).1 $$ Hrds
  imod readSlots_grow γr H d E HE RD $$ Hv Hrds with ⟨Hv, Hrds⟩
  ihave Hrds := (BigSepM.bigSepM_later).2 $$ Hrds
  imodintro
  iframe Hv
  inext
  unfold readReg
  iexists RD
  iframe HRD Hrds

/-- **A read takes its result** `v`, the key's value in a committed history `L` extending its
start, its answer (see the file header): under two laters (the invariant it was stored in; the
saved predicate naming it). -/
theorem kvr_read_take (γr : RNames) (γΦ : GName) (s : ReadRec) (Φ : List w8 → IProp GF)
    (L : List (List w8)) (v : List w8) (E : CoPset) (HE : ↑rkvN ⊆ E)
    (Hans : s.ans = some v) (Hst : s.start <+: L) (Hv : v = kvFold L s.key) :
    ⊢ rkvInv (GF := GF) γr -∗ γΦ ↪[γr.rds] s -∗ savedPredOwn γΦ DFrac.discard Φ -∗
      kvLb γr L ={E}=∗ ▷ ▷ Φ v := by
  iintro #Hinv Hel #Hsp #HL
  iunfold kvLb at HL
  icases HL with ⟨%l, #Hl, %HLl⟩
  unfold rkvInv rkvInvBody
  iinv Hinv with ⟨%ops, %n, %Mi, %RS, %RMi, %O, %U, >Hc, Hsl⟩ Hclose
  iunfold rkvSlots at Hsl
  icases Hsl with ⟨Hsl, Hrd⟩
  iunfold readReg at Hrd
  icases Hrd with ⟨%RD, >HRD, Hrds⟩
  iunfold kvCore at Hc
  icases Hc with ⟨Hops, Hv', HU, Hn, HMi, HRS, HRMi, HO, %Hok, %Hodm, %Hsh⟩
  ihave %Hpre := ownCommittedOps_lb_prefix γr.cluster ops l $$ [Hops Hl]
  · iframe Hops Hl
  have HLops : L <+: logHist ops := by rw [HLl]; exact logHist_le_ops l ops Hpre
  icases ghost_map_lookup $$ HRD Hel with %HRDs
  ihave Hrds := (BigSepM.bigSepM_later).1 $$ Hrds
  icases (BigSepM.bigSepM_delete (Φ := fun k s =>
    iprop(▷ readSlot (GF := GF) γr k s (logHist ops))) HRDs).1 $$ Hrds with ⟨Hs, Hrds⟩
  iunfold readSlot at Hs
  icases Hs with ⟨%Φ', #Hsp', Hst'⟩
  icases Hst' with (⟨>%Hpend, -, -⟩ | ⟨%v', >%Hv'', HQ⟩)
  · exact absurd (Hans.trans (congrArg some Hv)) (Hpend L Hst HLops)
  have Hvv : v' = v := Option.some.inj (Hv''.symm.trans Hans)
  subst Hvv
  ihave #Heq : ▷ ▷ (Φ' v' ≡ Φ v') $$ []
  · inext
    iapply saved_pred_agree γΦ DFrac.discard DFrac.discard Φ' Φ _ $$ Hsp' Hsp
  imod ghost_map_delete $$ HRD Hel with HRD
  ihave Hrds := (BigSepM.bigSepM_later).2 $$ Hrds
  imod Hclose $$ [Hops Hv' HU Hn HMi HRS HRMi HO Hsl Hrds HRD] with -
  · inext
    iexists ops, n, Mi, RS, RMi, O, U
    isplitl [Hops Hv' HU Hn HMi HRS HRMi HO]
    · unfold kvCore
      iframe Hops Hv' HU Hn HMi HRS HRMi HO
      ipureintro; exact ⟨Hok, Hodm, Hsh⟩
    unfold rkvSlots readReg
    iframe Hsl
    iexists RD.delete γΦ
    iframe HRD Hrds
  imodintro
  inext
  inext
  ihave Hiff := internalEq_iff _ _ $$ Heq
  icases Hiff with ⟨Hiff, -⟩
  iapply Hiff $$ HQ

end lemmas

end kvreconf
end EtcdGrove
end Perennial
