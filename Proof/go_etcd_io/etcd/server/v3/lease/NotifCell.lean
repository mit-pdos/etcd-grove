/-
The expiry notifier's cell (prove-ps2-newlessor3, 2026-11-21; `InvLessor.lean`, "The expiry
notifier's cell"). Lean-first (no Rocq counterpart).

A writer under `le.mu`'s write lock takes the cell (`notif_wopen`: the whole field, the notifier)
and gives it back (`notif_wclose`, at any notifier: `Promote`, `Demote` and `Recover` replace it);
the expiry loop under the read lock takes it with its token (`notif_ropen`) and gives it back at
the same notifier (`notif_rclose`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.LessorLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lease

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- (Perennial has no `Timeless` instance of `ownSliceCap`; local, `notes/perennial-changes.md`.) -/
instance ownSliceCap_timeless' {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (s : GoSlice)
    (dq : DFrac) : Timeless (ownSliceCap (GF := GF) V s dq) := by
  rw [ownSliceCap_unseal]; unfold ownSliceCapDef; infer_instance

instance lwtAt_timeless (p : Loc) (id k : w64) (q : Qp) : Timeless (lwtAt (GF := GF) p id k q) := by
  unfold lwtAt; infer_instance

instance queueAt_timeless (s : GoSlice) (xs : List (Loc × w64)) (q : Qp) :
    Timeless (queueAt (GF := GF) s xs q) := by
  unfold queueAt
  have : Timeless (iprop([∗list] k ↦ x ∈ xs, lwtAt (GF := GF) x.1 x.2 (W64 k) q) : IProp GF) :=
    BigSepL.bigSepL_timeless fun _ => inferInstance
  infer_instance

instance notifierAtM_timeless (np : Loc) (q : Qp) (M : GMap w64 Loc) :
    Timeless (notifierAtM (GF := GF) np q M) := by
  unfold notifierAtM; infer_instance

instance notifierAt_timeless (np : Loc) (q : Qp) : Timeless (notifierAt (GF := GF) np q) := by
  unfold notifierAt; infer_instance

instance notifCell_timeless (lp : Loc) (γx γy γk : GName) :
    Timeless (notifCell (GF := GF) lp γx γy γk) := by
  unfold notifCell; infer_instance

/-- **A writer takes the cell**: with `le.mu`'s whole share (half the field, the whole `γx`), the
whole field and the notifier it points to. -/
theorem notif_wopen (lp : Loc) (γl : GName) (np : Loc) (E : CoPset) (hE : ↑notifN ⊆ E) :
    lF go!"leaseExpiredNotifier" lp ↦{DFrac.own (1 : Qp).half} np ∗ notifShare (GF := GF) lp γl 1 ⊢
      |={E}=> lF go!"leaseExpiredNotifier" lp ↦ np ∗ notifierAt np 1 ∗ notifTaken lp γl false := by
  iintro ⟨Hf, Hs⟩
  iunfold notifShare at Hs
  icases Hs with ⟨%γr, #Hp, Hx, #Hinv⟩
  iinv Hinv with >Hc Hclose
  iunfold notifCell at Hc
  icases Hc with (⟨%np', %k, Hf', Hn, Hk⟩ | ⟨-, Hx'⟩ | ⟨-, -, Hx'⟩)
  · ihave ⟨%Heq, Hf⟩ := ptsto_halves_combine _ np np' $$ [$Hf $Hf']
    subst Heq
    imod ghostVar_update false _ k $$ Hk with Hk
    icases (ghostVar_split_half _ 1 false).1 $$ Hk with ⟨Hk1, Hk2⟩
    imod Hclose $$ [Hk1 Hx] with -
    · inext; iunfold notifCell; iright; ileft; iframe Hk1 Hx
    imodintro
    iframe Hf Hn
    iunfold notifTaken
    iexists γr
    iframe Hp Hk2 Hinv
  · ihave %H := ghostVar_valid_2 _ _ _ _ _ $$ Hx Hx'
    exact absurd H.1 (Qp_one_add_not_le 1)
  · ihave %H := ghostVar_valid_2 _ _ _ _ _ $$ Hx Hx'
    exact absurd H.1 (Qp_one_add_not_le _)

/-- **A writer gives the cell back**, at any notifier `np` the field points to. -/
theorem notif_wclose (lp : Loc) (γl : GName) (np : Loc) (E : CoPset) (hE : ↑notifN ⊆ E) :
    lF go!"leaseExpiredNotifier" lp ↦ np ∗ notifierAt (GF := GF) np 1 ∗ notifTaken lp γl false ⊢
      |={E}=> lF go!"leaseExpiredNotifier" lp ↦{DFrac.own (1 : Qp).half} np ∗ notifShare lp γl 1 := by
  iintro ⟨Hf, Hn, Ht⟩
  iunfold notifTaken at Ht
  icases Ht with ⟨%γr, #Hp, Hk, #Hinv⟩
  iinv Hinv with >Hc Hclose
  iunfold notifCell at Hc
  icases Hc with (⟨%np', %k, -, -, Hk'⟩ | ⟨Hk', Hx⟩ | ⟨Hk', -, -⟩)
  · ihave %H := ghostVar_valid_2 _ _ _ _ _ $$ Hk' Hk
    exact absurd H.1 (Qp_one_add_not_le _)
  · ihave Hk := (ghostVar_split_half _ 1 _).2 $$ [$Hk $Hk']
    icases ptsto_halves_split _ np $$ Hf with ⟨Hf1, Hf2⟩
    imod Hclose $$ [Hf2 Hn Hk] with -
    · inext; iunfold notifCell; ileft; iexists np, false; iframe Hf2 Hn Hk
    imodintro
    iframe Hf1
    iunfold notifShare
    iexists γr
    iframe Hp Hx Hinv
  · ihave %H := ghostVar_valid_2 _ _ _ _ _ $$ Hk Hk'
    cases H.2

/-- **The expiry loop takes the cell** under the read lock (its reader's share `rfrac` of the
field and of `γx`, and its token): the notifier the field points to, and the cell's half of the
field. -/
theorem notif_ropen (lp : Loc) (γl : GName) (np : Loc) (dq : DFrac) (E : CoPset) (hE : ↑notifN ⊆ E) :
    lF go!"leaseExpiredNotifier" lp ↦{dq} np ∗ notifShare (GF := GF) lp γl sync.rfrac ∗
      notifRTok γl ⊢
      |={E}=> lF go!"leaseExpiredNotifier" lp ↦{dq} np ∗ notifierAt np 1 ∗
        lF go!"leaseExpiredNotifier" lp ↦{DFrac.own (1 : Qp).half} np ∗ notifTaken lp γl true := by
  iintro ⟨Hf, Hs, Hr⟩
  iunfold notifShare at Hs
  icases Hs with ⟨%γr, #Hp, Hx, #Hinv⟩
  iunfold notifRTok at Hr
  icases Hr with ⟨%γr', #Hp', Hy⟩
  ihave %Hγ := lessorPinR_agree γl γr γr' $$ [$Hp $Hp']
  subst Hγ
  iinv Hinv with >Hc Hclose
  iunfold notifCell at Hc
  icases Hc with (⟨%np', %k, Hf', Hn, Hk⟩ | ⟨-, Hx'⟩ | ⟨-, Hy', -⟩)
  · icombine Hf Hf' gives %Heq
    subst Heq
    imod ghostVar_update true _ k $$ Hk with Hk
    icases (ghostVar_split_half _ 1 true).1 $$ Hk with ⟨Hk1, Hk2⟩
    imod Hclose $$ [Hk1 Hy Hx] with -
    · inext; iunfold notifCell; iright; iright; iframe Hk1 Hy Hx
    imodintro
    iframe Hf Hn Hf'
    iunfold notifTaken
    iexists γr
    iframe Hp Hk2 Hinv
  · ihave %H := ghostVar_valid_2 _ _ _ _ _ $$ Hx' Hx
    exact absurd H.1 (Qp_one_add_not_le _)
  · iexfalso
    iapply token_exclusive $$ Hy Hy'

/-- **The expiry loop gives the cell back** at the notifier it took. -/
theorem notif_rclose (lp : Loc) (γl : GName) (np : Loc) (E : CoPset) (hE : ↑notifN ⊆ E) :
    notifierAt (GF := GF) np 1 ∗
      lF go!"leaseExpiredNotifier" lp ↦{DFrac.own (1 : Qp).half} np ∗ notifTaken lp γl true ⊢
      |={E}=> notifShare lp γl sync.rfrac ∗ notifRTok γl := by
  iintro ⟨Hn, Hf, Ht⟩
  iunfold notifTaken at Ht
  icases Ht with ⟨%γr, #Hp, Hk, #Hinv⟩
  iinv Hinv with >Hc Hclose
  iunfold notifCell at Hc
  icases Hc with (⟨%np', %k, -, -, Hk'⟩ | ⟨Hk', -⟩ | ⟨Hk', Hy, Hx⟩)
  · ihave %H := ghostVar_valid_2 _ _ _ _ _ $$ Hk' Hk
    exact absurd H.1 (Qp_one_add_not_le _)
  · ihave %H := ghostVar_valid_2 _ _ _ _ _ $$ Hk Hk'
    cases H.2
  · ihave Hk := (ghostVar_split_half _ 1 _).2 $$ [$Hk $Hk']
    imod Hclose $$ [Hf Hn Hk] with -
    · inext; iunfold notifCell; ileft; iexists np, true; iframe Hf Hn Hk
    imodintro
    isplitl [Hx]
    · iunfold notifShare; iexists γr; iframe Hp Hx Hinv
    iunfold notifRTok; iexists γr; iframe Hp Hy


/-- **A registered item's time**, out of the notifier and back (the expiry loop reads and writes the
first item's `time`, `expireExists`). -/
theorem notifierAtM_time (np : Loc) (M : GMap w64 Loc) (id : w64) (p : Loc) (h : M.lookup id = some p) :
    notifierAtM (GF := GF) np 1 M ⊢
      (∃ t : _root_.Perennial.time.Time, lwF go!"time" p ↦ t) ∗
        (∀ t' : _root_.Perennial.time.Time, lwF go!"time" p ↦ t' -∗ notifierAtM np 1 M) := by
  iintro Hn
  iunfold notifierAtM at Hn
  icases Hn with ⟨%mp, %s, %xs, Hm, HM, Hq, Hqa, %Hinv⟩
  iunfold queueAt at Hqa
  icases Hqa with ⟨Hs, Hcap, Hits⟩
  have hmem : (p, id) ∈ xs := (Hinv.2 id p).1 h
  obtain ⟨n, hn, hxn⟩ := List.mem_iff_getElem.mp hmem
  have hxn' : xs[n]? = some (p, id) := by rw [List.getElem?_eq_getElem hn, hxn]
  icases (BigSepL.bigSepL_lookup_acc hxn').1 $$ Hits with ⟨Hx, Hits⟩
  iunfold lwtAt at Hx
  icases Hx with ⟨#Hid, ⟨%t, Ht⟩, Hix⟩
  isplitl [Ht]
  · iexists t; iexact Ht
  iintro %t' Ht'
  ihave Hits := Hits $$ %(p, id) [Hid Ht' Hix]
  · iunfold lwtAt; iframe Hid Hix; iexists t'; iexact Ht'
  rw [list_set_lookup_self xs n _ hxn']
  iunfold notifierAtM
  iexists mp, s, xs
  iframe
  iunfold queueAt
  iframe
  ipureintro; exact Hinv

end lemmas

end lease
end EtcdGrove
end Perennial
