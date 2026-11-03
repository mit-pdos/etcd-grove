/-
Lean-first (no Rocq counterpart).

# The client's ghost lemmas (2026-11-01, kvdurable's adequacy)

kvreconf's `ClientLemmas` (`kvr_mint`, `kvr_collect`, `waiters_drop`, `rkvVal_agree`,
`rkvVal_update`), `ClientAu` (`kvr_propAu`) and `ReadSlot` (`kvr_read_start`, `readReg_grow`,
`kvr_read_take`) at kvdurable's predicates (`rkvInv`, `opSlot`, `readSlot`, `readReg`, `waitP`,
`kvLb`, `waiterOk`: the same bodies at `KdNames`, the store's invariant in `kdRkvN`, the clients'
mask `kdMask`); their proofs are kvreconf's. The lemmas of those files that name none of the store's
predicates (minting, the history's laws, `ansOf`) are used from kvreconf.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.readSeqs__next
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.ReadSlot

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open kvreconf (KVMap ReadRec MintOk MintedOp odOf logHist histStep kvFold kvApply kvNext dkey
  encodeOp)
open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- What an operation's update may open, outside raft's cluster and the store's invariant. -/
theorem kdMask_sub : kdMask ⊆ (⊤ \ ↑kdRaftN) \ ↑kdRkvN :=
  Std.LawfulSet.subset_trans Std.LawfulSet.diff_subset_left
    (Std.LawfulSet.subset_trans Std.LawfulSet.diff_subset_left
      (Std.LawfulSet.subset_trans Std.LawfulSet.diff_subset_left Std.LawfulSet.diff_subset_left))

/-- What a read's update may open, inside the store's invariant. -/
theorem kdMask_sub_rkv : kdMask ⊆ ⊤ \ ↑kdRkvN := fun x hx => by
  have h := Std.LawfulSet.mem_diff.mp (kdMask_sub x hx)
  exact Std.LawfulSet.mem_diff.mpr ⟨Std.LawfulSet.diff_subset_left x h.1, h.2⟩

end pure

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- The client's half of the history's ghost variable agrees with the invariant's. -/
theorem rkvVal_agree (γ : KdNames) (H : List (List w8)) (x : KVMap) :
    ⊢ ghostVar (GF := GF) γ.r.val (1 : Qp).half H -∗ rkvVal γ x -∗ ⌜kvFold H = x⌝ := by
  iintro Hv Hx
  unfold rkvVal
  icases Hx with ⟨%H', Hx, %Hf⟩
  ihave %Heq := ghostVar_agree γ.r.val H (1 : Qp).half H' (1 : Qp).half $$ Hv Hx
  ipureintro; rw [Heq]; exact Hf

/-- Both halves move to the history `H'`; the client's at its fold. -/
theorem rkvVal_update (γ : KdNames) (H : List (List w8)) (x : KVMap) (H' : List (List w8)) :
    ⊢ ghostVar (GF := GF) γ.r.val (1 : Qp).half H -∗ rkvVal γ x ==∗
      ghostVar γ.r.val (1 : Qp).half H' ∗ rkvVal γ (kvFold H') := by
  iintro Hv Hx
  unfold rkvVal
  icases Hx with ⟨%H0, Hx, -⟩
  imod ghostVar_update_halves H' γ.r.val H H0 $$ Hv Hx with ⟨Hv, Hx⟩
  imodintro
  iframe Hv
  iexists H'
  iframe Hx
  ipureintro; rfl

/-- **A fresh operation id mints the operation's datum**, with its slot holding the client's atomic
update and a later credit (kvreconf's `kvr_mint`). -/
theorem kd_mint (γ : KdNames) (nop : w64) (kind : w8) (key val : List w8)
    (Ψ : List w8 → IProp GF) (E : CoPset) (HE : ↑kdRkvN ⊆ E) (Hn : uint.Z nop + 1 < 2 ^ 64)
    (Hk : (key.length : Int) < 2 ^ 64) :
    ⊢ rkvInv (GF := GF) γ -∗ ghostVar γ.r.opn (1 : Qp).half nop -∗ £ 1 -∗
      opAu γ (kvNext kind key val) key Ψ ={E}=∗
      ghostVar γ.r.opn (1 : Qp).half (nop + W64 1) ∗
      ∃ γp : GName × GName, encodeOp (nop + W64 1) kind key val ↪[γ.r.ops]□ γp ∗
        savedPredOwn γp.1 DFrac.discard Ψ ∗ token γp.2 := by
  iintro #Hinv Hopn Hlc Hau
  unfold rkvInv rkvInvBody
  iinv Hinv with ⟨%ops, %n, %Mi, %RS, %RMi, %O, %U, >Hc, Hsl, Hrd⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨Hops, Hv, HU, Hn', HMi, HRS, HRMi, HO, %Hok, %Hodm, %Hsh⟩
  ihave %Heq := ghostVar_agree γ.r.opn nop (1 : Qp).half n (1 : Qp).half $$ Hopn Hn'
  subst Heq
  have Hf : (fun x => kvApply x (encodeOp (nop + W64 1) kind key val)) = kvNext kind key val :=
    funext fun x => kvreconf.kvApply_encodeOp x (nop + W64 1) kind key val Hk
  have Hdk : dkey (encodeOp (nop + W64 1) kind key val) = key := kvreconf.dkey_encodeOp _ _ _ _ Hk
  have Hid := kvreconf.opId_encodeOp (nop + W64 1) kind key val Hk
  generalize Hd : encodeOp (nop + W64 1) kind key val = d at Hf Hdk Hid ⊢
  imod saved_pred_alloc Ψ DFrac.discard trivial with ⟨%γq, #Hsp⟩
  imod token_alloc (GF := GF) with ⟨%γk, Htok⟩
  obtain ⟨HMi0, HnM, HO0, Hok'⟩ := kvreconf.mintOk_op nop Mi RS RMi O U d (γq, γk) Hok Hn Hid
  have Hdn : d ∉ logHist ops := fun h => HnM (Hodm d ((kvreconf.mem_histOf _ d).mp h))
  imod ghostVar_update_halves (nop + W64 1) γ.r.opn nop nop $$ Hopn Hn' with ⟨Hopn, Hn'⟩
  imod ghost_map_insert_persist (nop + W64 1) d HMi0 $$ HMi with ⟨HMi, -⟩
  imod ghost_map_insert_persist d ((γq, γk) : GName × GName) HO0 $$ HO with ⟨HO, #Hop⟩
  imod Hclose $$ [Hops Hv HU Hn' HMi HRS HRMi HO Hsl Hrd Hlc Hau] with -
  · inext
    iexists ops, nop + W64 1, Mi.insert (nop + W64 1) d, RS, RMi, O.insert d (γq, γk), U
    isplitl [Hops Hv HU Hn' HMi HRS HRMi HO]
    · unfold kvCore
      iframe Hops Hv HU Hn' HMi HRS HRMi HO
      ipureintro
      exact ⟨Hok', fun d' Hd' => kvreconf.mintedOp_insert _ _ _ _ HMi0 (Hodm d' Hd'), Hsh⟩
    iframe Hrd
    iapply (BigSepM.bigSepM_insert (Φ := fun d γp => opSlot (GF := GF) γ d γp (logHist ops))
      HO0).2
    iframe Hsl
    unfold opSlot
    iexists Ψ
    iframe Hsp
    ileft
    iframe Hlc
    isplitr
    · ipureintro; exact Hdn
    rw [Hf, Hdk]; iexact Hau
  imodintro
  iframe Hopn
  iexists (γq, γk)
  iframe Hop Hsp Htok

/-- **Collecting an operation's result** (kvreconf's `kvr_collect`): given the waiter's answer `v`,
the ticket buys the client's result at `v`, under two laters. -/
theorem kd_collect (γ : KdNames) (d : List w8) (γp : GName × GName) (Ψ : List w8 → IProp GF)
    (v : List w8) (E : CoPset) (HE1 : ↑kdRkvN ⊆ E) :
    ⊢ rkvInv (GF := GF) γ -∗ d ↪[γ.r.ops]□ γp -∗
      savedPredOwn γp.1 DFrac.discard Ψ -∗ token γp.2 -∗ waitP γ d v ={E}=∗ ▷ ▷ Ψ v := by
  iintro #Hinv #Hop #Hsp Htok #Hw
  iunfold waitP at Hw
  icases Hw with ⟨%l, #Hl, %Hans⟩
  obtain ⟨H1, HH1, Hd1, Hv⟩ := Hans
  unfold rkvInv rkvInvBody
  iinv Hinv with ⟨%ops, %n, %Mi, %RS, %RMi, %O, %U, >Hc, Hsl, Hrd⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨Hops, Hv', HU, Hn, HMi, HRS, HRMi, HO, %Hok, %Hodm, %Hsh⟩
  ihave %Hpre := ownCommittedOps_lb_prefix γ.r.cluster ops l $$ [Hops Hl]
  · iframe Hops Hl
  icases ghost_map_lookup $$ HO Hop with %HOd
  have Hocc : H1 ++ [d] <+: logHist ops := HH1.trans (kvreconf.logHist_le_ops l ops Hpre)
  have HdL : d ∈ logHist ops :=
    Hocc.subset (List.mem_append_right _ (List.mem_singleton_self d))
  ihave Hsl := (BigSepM.bigSepM_later).1 $$ Hsl
  icases (BigSepM.bigSepM_delete (Φ := fun d γp =>
    iprop(▷ opSlot (GF := GF) γ d γp (logHist ops))) HOd).1 $$ Hsl with ⟨Hsd, Hsl⟩
  iunfold opSlot at Hsd
  icases Hsd with ⟨%Φ', #Hsp', Hst⟩
  icases Hst with (⟨>%Hn', -, -⟩ | ⟨%H0, >%HH0, HQ⟩)
  · exact absurd HdL Hn'
  have HH0eq : H0 = H1 :=
    kvreconf.hist_prefix_before_unique _ _ _ d (kvreconf.histOf_nodup _) HH0.1 Hocc
  subst HH0eq
  subst Hv
  icases HQ with (HQ | >Htok')
  · ihave #Heq : ▷ ▷ (Φ' (kvFold (H0 ++ [d]) (dkey d)) ≡ Ψ (kvFold (H0 ++ [d]) (dkey d))) $$ []
    · inext
      iapply saved_pred_agree γp.1 DFrac.discard DFrac.discard Φ' Ψ _ $$ Hsp' Hsp
    imod Hclose $$ [Hops Hv' HU Hn HMi HRS HRMi HO Hsl Hrd Htok] with -
    · inext
      iexists ops, n, Mi, RS, RMi, O, U
      isplitl [Hops Hv' HU Hn HMi HRS HRMi HO]
      · unfold kvCore
        iframe Hops Hv' HU Hn HMi HRS HRMi HO
        ipureintro; exact ⟨Hok, Hodm, Hsh⟩
      iframe Hrd
      iapply (BigSepM.bigSepM_delete (Φ := fun d γp =>
        opSlot (GF := GF) γ d γp (logHist ops)) HOd).2
      iframe Hsl
      unfold opSlot
      iexists Φ'
      iframe Hsp'
      iright
      iexists H0
      iframe Htok
      ipureintro; exact HH0
    imodintro
    inext
    inext
    ihave Hiff := internalEq_iff _ _ $$ Heq
    icases Hiff with ⟨Hiff, -⟩
    iapply Hiff $$ HQ
  · iexfalso
    iapply token_exclusive $$ Htok Htok'

/-- A waiter dropped from the replica's waiters (`propose`, after its timeout). -/
theorem waiters_drop (γ : KdNames) (W : GMap (List w8) Loc) (d : List w8) :
    ([∗map] k ↦ c ∈ W, waiterOk (GF := GF) γ k c) ⊢
      [∗map] k ↦ c ∈ GMap.delete d W, waiterOk γ k c := by
  cases h : W !! d with
  | none =>
    rw [GMap.delete_notin W d h]
  | some x =>
    iintro H
    icases (BigSepM.bigSepM_delete (Φ := fun k c => waiterOk (GF := GF) γ k c) h).1 $$ H
      with ⟨-, H⟩
    iexact H

/-! ## The reads' slots (kvreconf's `ReadSlot`) -/

include sem in
/-- kvreconf's `ansOf_cons` (whose statement carries kvreconf's package assumptions). -/
theorem kd_ansOf_cons (s : List w8) (pvs : List val) : kvreconf.ansOf (#s :: pvs) = some s := by
  have h : ∃ s' : List w8, (#s :: pvs).head? = some #s' := ⟨s, rfl⟩
  unfold kvreconf.ansOf
  rw [dite_cond_eq_true (eq_true h)]
  have hc : some (#s : val) = some (#h.choose : val) := h.choose_spec
  exact congrArg some (go.intoVal_inj (V := GoString) (Option.some.inj hc)).symm

/-- **A read starts**: its slot registered at the current history `H0`, with the answer `ans`. -/
theorem kd_read_start (γ : KdNames) (key : List w8) (ans : Option (List w8))
    (Φ : List w8 → IProp GF) (E : CoPset) (HE : ↑kdRkvN ⊆ E) (HE' : kdMask ⊆ E \ ↑kdRkvN) :
    ⊢ rkvInv (GF := GF) γ -∗ £ 1 -∗
      AU <{ ∃∃ (x : KVMap), rkvVal γ x }> @ kdMask, ∅ <{ rkvVal γ x, COMM Φ (x key) }> ={E}=∗
      ∃ (γΦ : GName) (H0 : List (List w8)), γΦ ↪[γ.r.rds] (⟨key, H0, ans⟩ : ReadRec) ∗
        savedPredOwn γΦ DFrac.discard Φ ∗ kvLb γ H0 := by
  iintro #Hinv Hlc Hau
  unfold rkvInv rkvInvBody
  iinv Hinv with ⟨%ops, %n, %Mi, %RS, %RMi, %O, %U, >Hc, Hsl, Hrd⟩ Hclose
  iunfold readReg at Hrd
  icases Hrd with ⟨%RD, >HRD, Hrds⟩
  iunfold kvCore at Hc
  icases Hc with ⟨Hops, Hv, HU, Hn, HMi, HRS, HRMi, HO, %Hok, %Hodm, %Hsh⟩
  icases ownCommittedOps_get_lb γ.r.cluster ops $$ Hops with ⟨Hops, %l, #Hl, %Hl'⟩
  imod saved_pred_alloc_cofinite Φ RD.domList DFrac.discard trivial with ⟨%γΦ, %Hfr, #Hsp⟩
  have HRD0 : RD !! γΦ = none := by
    cases h : RD !! γΦ with
    | none => rfl
    | some _ => exact absurd ((GMap.mem_dom_list RD γΦ).mpr (by rw [h]; rfl)) Hfr
  imod ghost_map_insert γΦ (⟨key, logHist ops, ans⟩ : ReadRec) HRD0 $$ HRD with ⟨HRD, Hel⟩
  ihave Hslot : |={E \ ↑kdRkvN}=> ghostVar γ.r.val (1 : Qp).half (logHist ops) ∗
      readSlot γ γΦ ⟨key, logHist ops, ans⟩ (logHist ops) $$ [Hv Hlc Hau]
  · by_cases Hfire : ans = some (kvFold (logHist ops) key)
    · -- the key's value now is the answer: the update runs now
      ihave Hau := atomic_update_mask_weaken HE' $$ Hau
      ihave Hacc := aupd_aacc $$ Hau
      unfold atomic_acc
      imod Hacc with Hacc
      isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
      icases Hacc with ⟨%x, Hx, Hucl⟩
      ihave %Hxeq := rkvVal_agree γ (logHist ops) x $$ Hv Hx
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
    unfold readReg
    iframe Hsl
    iexists RD.insert γΦ ⟨key, logHist ops, ans⟩
    iframe HRD
    iapply (BigSepM.bigSepM_insert (Φ := fun k s => readSlot (GF := GF) γ k s (logHist ops))
      HRD0).2
    iframe Hslot Hrds
  imodintro
  iexists γΦ, logHist ops
  iframe Hel Hsp
  unfold kvLb
  iexists l
  iframe Hl
  ipureintro; rw [← Hl', kvreconf.logHist_opsOf]

/-- A read's slot as the history grows by `d`: a pending slot fires if the key's value in the
grown history is its answer. -/
theorem readSlot_grow (γ : KdNames) (k : GName) (s : ReadRec) (H : List (List w8))
    (d : List w8) (E : CoPset) (HE : kdMask ⊆ E) :
    ⊢ ghostVar (GF := GF) γ.r.val (1 : Qp).half (H ++ [d]) -∗ ▷ readSlot γ k s H ={E}=∗
      ghostVar γ.r.val (1 : Qp).half (H ++ [d]) ∗ ▷ readSlot γ k s (H ++ [d]) := by
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
      ihave %Hxeq := rkvVal_agree γ (H ++ [d]) x $$ Hv Hx
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
theorem readSlots_grow (γ : KdNames) (H : List (List w8)) (d : List w8) (E : CoPset)
    (HE : kdMask ⊆ E) : ∀ RD : GMap GName ReadRec,
    ⊢ ghostVar (GF := GF) γ.r.val (1 : Qp).half (H ++ [d]) -∗
      ([∗map] k ↦ s ∈ RD, ▷ readSlot γ k s H) ={E}=∗
      ghostVar γ.r.val (1 : Qp).half (H ++ [d]) ∗ [∗map] k ↦ s ∈ RD, ▷ readSlot γ k s (H ++ [d]) := by
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
    icases (BigSepM.bigSepM_insert (Φ := fun k s => iprop(▷ readSlot (GF := GF) γ k s H))
      Hk).1 $$ Hm with ⟨Hs, Hm⟩
    imod IH $$ Hv Hm with ⟨Hv, Hm⟩
    imod readSlot_grow γ k s H d E HE $$ Hv Hs with ⟨Hv, Hs⟩
    imodintro
    iframe Hv
    iapply (BigSepM.bigSepM_insert (Φ := fun k s => iprop(▷ readSlot (GF := GF) γ k s (H ++ [d])))
      Hk).2
    iframe Hs Hm

/-- **The reads' registry as the history grows by `d`** (`kd_propAu`'s first occurrence). -/
theorem readReg_grow (γ : KdNames) (H : List (List w8)) (d : List w8) (E : CoPset)
    (HE : kdMask ⊆ E) :
    ⊢ ghostVar (GF := GF) γ.r.val (1 : Qp).half (H ++ [d]) -∗ ▷ readReg γ H ={E}=∗
      ghostVar γ.r.val (1 : Qp).half (H ++ [d]) ∗ ▷ readReg γ (H ++ [d]) := by
  iintro Hv Hrd
  iunfold readReg at Hrd
  icases Hrd with ⟨%RD, >HRD, Hrds⟩
  ihave Hrds := (BigSepM.bigSepM_later).1 $$ Hrds
  imod readSlots_grow γ H d E HE RD $$ Hv Hrds with ⟨Hv, Hrds⟩
  ihave Hrds := (BigSepM.bigSepM_later).2 $$ Hrds
  imodintro
  iframe Hv
  inext
  unfold readReg
  iexists RD
  iframe HRD Hrds

/-- **A read takes its result** `v`, the key's value in a committed history `L` extending its
start, its answer: under two laters. -/
theorem kd_read_take (γ : KdNames) (γΦ : GName) (s : ReadRec) (Φ : List w8 → IProp GF)
    (L : List (List w8)) (v : List w8) (E : CoPset) (HE : ↑kdRkvN ⊆ E)
    (Hans : s.ans = some v) (Hst : s.start <+: L) (Hv : v = kvFold L s.key) :
    ⊢ rkvInv (GF := GF) γ -∗ γΦ ↪[γ.r.rds] s -∗ savedPredOwn γΦ DFrac.discard Φ -∗
      kvLb γ L ={E}=∗ ▷ ▷ Φ v := by
  iintro #Hinv Hel #Hsp #HL
  iunfold kvLb at HL
  icases HL with ⟨%l, #Hl, %HLl⟩
  unfold rkvInv rkvInvBody
  iinv Hinv with ⟨%ops, %n, %Mi, %RS, %RMi, %O, %U, >Hc, Hsl, Hrd⟩ Hclose
  iunfold readReg at Hrd
  icases Hrd with ⟨%RD, >HRD, Hrds⟩
  iunfold kvCore at Hc
  icases Hc with ⟨Hops, Hv', HU, Hn, HMi, HRS, HRMi, HO, %Hok, %Hodm, %Hsh⟩
  ihave %Hpre := ownCommittedOps_lb_prefix γ.r.cluster ops l $$ [Hops Hl]
  · iframe Hops Hl
  have HLops : L <+: logHist ops := by rw [HLl]; exact kvreconf.logHist_le_ops l ops Hpre
  icases ghost_map_lookup $$ HRD Hel with %HRDs
  ihave Hrds := (BigSepM.bigSepM_later).1 $$ Hrds
  icases (BigSepM.bigSepM_delete (Φ := fun k s =>
    iprop(▷ readSlot (GF := GF) γ k s (logHist ops))) HRDs).1 $$ Hrds with ⟨Hs, Hrds⟩
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
    unfold readReg
    iframe Hsl
    iexists RD.delete γΦ
    iframe HRD Hrds
  imodintro
  inext
  inext
  ihave Hiff := internalEq_iff _ _ $$ Heq
  icases Hiff with ⟨Hiff, -⟩
  iapply Hiff $$ HQ

/-! ## The update `node.Propose` takes (kvreconf's `ClientAu`) -/

/-- A slot of another datum keeps its state as the history grows by `d`. -/
theorem opSlot_grow (γ : KdNames) (d' d : List w8) (γp : GName × GName) (H : List (List w8))
    (Hne : d' ≠ d) :
    ⊢ opSlot (GF := GF) γ d' γp H -∗ opSlot γ d' γp (H ++ [d]) := by
  unfold opSlot
  iintro ⟨%Φ, #Hsp, Hst⟩
  iexists Φ
  iframe Hsp
  icases Hst with (⟨%Hn, Hlc, Hau⟩ | ⟨%H0, %Hp, HQ⟩)
  · ileft
    iframe Hlc Hau
    ipureintro
    simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨Hn, Hne⟩
  · iright
    iexists H0
    iframe HQ
    ipureintro
    exact ⟨Hp.1.trans (List.prefix_append _ _), Hp.2⟩

/-- **The update `node.Propose` takes** for the operation's datum `d`, whose slot is `γp`
(kvreconf's `kvr_propAu`). -/
theorem kd_propAu (γ : KdNames) (d : List w8) (γp : GName × GName) :
    ⊢ rkvInv (GF := GF) γ -∗ d ↪[γ.r.ops]□ γp -∗
      □ AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps γ.r.cluster ops }>
          @ ⊤ \ ↑kdRaftN, ∅
        <{ ∀∀ (t : w64), ownCommittedOps γ.r.cluster (ops ++ [(⟨t, W32 0, d⟩ : LogEntry)]),
           COMM True }> := by
  iintro #Hinv #Hop
  imodintro
  iauintro
  unfold atomic_acc rkvInv rkvInvBody
  have Hdisj := kdRkvN_kdRaftN
  iinv Hinv with ⟨%ops, %n, %Mi, %RS, %RMi, %O, %U, >Hc, Hsl, Hrd⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨Hops, Hv, HU, Hn, HMi, HRS, HRMi, HO, %Hok, %Hodm, %Hsh⟩
  icases ghost_map_lookup $$ HO Hop with %HOd
  have HMd : MintedOp Mi d := Hok.2.2.1 d γp HOd
  have Hne : d ≠ [] := kvreconf.mintedOp_ne_nil Mi d HMd
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑kdRaftN) \ ↑kdRkvN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists ops
  iframe Hops
  isplit
  · -- abort: nothing moved
    iintro Hops
    imod Hclose2 with -
    imod Hclose $$ [Hops Hv HU Hn HMi HRS HRMi HO Hsl Hrd] with -
    · inext
      iexists ops, n, Mi, RS, RMi, O, U
      iframe Hsl Hrd
      unfold kvCore
      iframe Hops Hv HU Hn HMi HRS HRMi HO
      ipureintro; exact ⟨Hok, Hodm, Hsh⟩
    imodintro
    iempintro
  · -- commit: the requested entries grow by `d`'s
    iintro %t Hops
    imod Hclose2 with -
    have Hod : odOf (⟨t, W32 0, d⟩ : LogEntry) = some d := kvreconf.odOf_normal _ rfl Hne
    have Hhist : logHist (ops ++ [⟨t, W32 0, d⟩]) = histStep (logHist ops) (some d) := by
      rw [kvreconf.logHist_snoc, Hod]
    have Hodm' : ∀ d', some d' ∈ (ops ++ [(⟨t, W32 0, d⟩ : LogEntry)]).map odOf →
        MintedOp Mi d' := by
      intro d' h
      rw [List.map_append, List.map_singleton, Hod] at h
      rcases List.mem_append.mp h with h | h
      · exact Hodm d' h
      · simp only [List.mem_singleton, Option.some.injEq] at h; subst h; exact HMd
    have Hsh' : ∀ e ∈ ops ++ [(⟨t, W32 0, d⟩ : LogEntry)], e.isConfChange →
        kvreconf.ConfShaped e := by
      intro e he hc
      rcases List.mem_append.mp he with h | h
      · exact Hsh e h hc
      · simp only [List.mem_singleton] at h; subst h
        exfalso; rcases hc with h | h <;> simp only at h <;> word
    by_cases Hm : d ∈ logHist ops
    · -- a later occurrence: the history does not move
      have Hocc : logHist (ops ++ [⟨t, W32 0, d⟩]) = logHist ops := by
        rw [Hhist, kvreconf.histStep_mem _ _ Hm]
      imod Hclose $$ [Hops Hv HU Hn HMi HRS HRMi HO Hsl Hrd] with -
      · inext
        iexists ops ++ [⟨t, W32 0, d⟩], n, Mi, RS, RMi, O, U
        rw [Hocc]
        iframe Hsl Hrd
        unfold kvCore
        rw [Hocc]
        iframe Hops Hv HU Hn HMi HRS HRMi HO
        ipureintro; exact ⟨Hok, Hodm', Hsh'⟩
      imodintro
      itrivial
    · -- the first occurrence: the client's update runs, from the slot
      have Hocc : logHist (ops ++ [⟨t, W32 0, d⟩]) = logHist ops ++ [d] := by
        rw [Hhist, kvreconf.histStep_nmem _ _ Hm]
      ihave Hsl := (BigSepM.bigSepM_later).1 $$ Hsl
      icases (BigSepM.bigSepM_delete (Φ := fun d γp =>
        iprop(▷ opSlot (GF := GF) γ d γp (logHist ops))) HOd).1 $$ Hsl with ⟨Hsd, Hsl⟩
      iunfold opSlot at Hsd
      icases Hsd with ⟨%Φ, #Hsp, Hst⟩
      icases Hst with (⟨>%Hn', >Hlc, Hau⟩ | ⟨%H0, >%Hp, -⟩)
      · imod lc_fupd_elim_later $$ Hlc Hau with Hau
        iunfold opAu at Hau
        ihave Hau := atomic_update_mask_weaken kdMask_sub $$ Hau
        ihave Hacc := aupd_aacc $$ Hau
        unfold atomic_acc
        imod Hacc with Hacc
        isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
        icases Hacc with ⟨%x, Hx, Hucl⟩
        ihave %Hxeq := rkvVal_agree γ (logHist ops) x $$ Hv Hx
        subst Hxeq
        have Hf : kvFold (logHist ops ++ [d]) = kvApply (kvFold (logHist ops)) d :=
          kvreconf.kvFold_snoc _ _
        imod rkvVal_update γ (logHist ops) (kvFold (logHist ops)) (logHist ops ++ [d])
          $$ Hv Hx with ⟨Hv, Hx⟩
        icases Hucl with ⟨-, Hcommit⟩
        isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
        rw [Hf]
        imod Hcommit $$ [Hx] with HΦ
        · rw [← Hf]; iexact Hx
        -- the reads' slots fire whose answer the grown history gives (helping)
        imod readReg_grow γ (logHist ops) d _ kdMask_sub $$ Hv Hrd with ⟨Hv, Hrd⟩
        imod Hclose $$ [Hops Hv HU Hn HMi HRS HRMi HO Hsl Hrd HΦ] with -
        · inext
          iexists ops ++ [⟨t, W32 0, d⟩], n, Mi, RS, RMi, O, U
          rw [Hocc]
          isplitl [Hops Hv HU Hn HMi HRS HRMi HO]
          · unfold kvCore
            rw [Hocc]
            iframe Hops Hv HU Hn HMi HRS HRMi HO
            ipureintro; exact ⟨Hok, Hodm', Hsh'⟩
          isplitl [Hsl HΦ]
          · iapply (BigSepM.bigSepM_delete (Φ := fun d' γp' =>
              opSlot (GF := GF) γ d' γp' (logHist ops ++ [d])) HOd).2
            isplitl [HΦ]
            · unfold opSlot
              iexists Φ
              iframe Hsp
              iright
              iexists logHist ops
              isplitr
              · ipureintro; exact ⟨List.prefix_refl _, Hm⟩
              ileft
              rw [Hf]
              iexact HΦ
            iapply BigSepM.bigSepM_impl $$ Hsl
            imodintro
            iintro %k %v %Hkv Hs
            have Hne' : k ≠ d := (Iris.Std.LawfulPartialMap.get?_delete_some_iff.mp Hkv).1.symm
            iapply opSlot_grow γ k d v (logHist ops) Hne' $$ Hs
          iframe Hrd
        imodintro
        itrivial
      · exact absurd (Hp.1.subset (List.mem_append_right _ (List.mem_singleton_self d))) Hm

/-- `kd_propAu` in the form `node.Propose` takes it. -/
theorem kd_propAu_dup (γ : KdNames) (d : List w8) (γp : GName × GName) :
    ⊢ rkvInv (GF := GF) γ -∗ d ↪[γ.r.ops]□ γp -∗
      □?γ.r.cluster.dup AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps γ.r.cluster ops }>
          @ ⊤ \ ↑kdRaftN, ∅
        <{ ∀∀ (t : w64), ownCommittedOps γ.r.cluster (ops ++ [(⟨t, W32 0, d⟩ : LogEntry)]),
           COMM True }> := by
  iintro #Hinv #Hop
  iapply intuitionisticallyIf_of_intuitionistically
  iapply kd_propAu γ d γp $$ Hinv Hop

end lemmas

end kvdurable
end EtcdGrove
end Perennial
