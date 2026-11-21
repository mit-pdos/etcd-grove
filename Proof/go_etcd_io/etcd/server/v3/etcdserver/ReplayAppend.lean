/- The whole Ready update, combining suffix replacement with term grouping. -/
module
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.replayTerms__appendEntries

@[expose] public section
noncomputable section
namespace Perennial
namespace EtcdGrove
open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- A run straddling the replacement index contributes its lower half. -/
def replayRetain (runs : List replayTermRun) (n : Nat) (first : w64) : List replayTermRun :=
  match runs[n]? with
  | some x => if uint.nat x.first' < uint.nat first then
        runs.take n ++ [{ x with last' := first - W64 1 }] else runs.take n
  | none => runs.take n

def replayCutIndex (runs : List replayTermRun) (first : w64) (n : Nat) : Prop :=
  n ≤ runs.length ∧
    (∀ i x, n ≤ i → runs[i]? = some x → uint.nat first ≤ uint.nat x.last') ∧
    (n = 0 ∨ ∃ x, runs[n - 1]? = some x ∧ uint.nat x.last' < uint.nat first)

theorem replayTerms.appendEntries_nonempty (r ents : GoSlice) (runs : List replayTermRun)
    (ls : List Loc) (first : EntryModel) (es : List EntryModel)
    (ordered : (first :: es).Pairwise fun a b => uint.nat a.term ≤ uint.nat b.term)
    (getIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (getTerm : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
       r ↦*□ runs ∗ ents ↦*□ ls ∗ entriesAt ls (first :: es) }}
      (App (Val (r @!! replayTerms.ty @!! go!"appendEntries")) (Val #ents))
    {{ (out : GoSlice), RET #out; ∃ n : Nat, ⌜replayCutIndex runs first.index n⌝ ∗
       out ↦*□ (first :: es).foldl replayAddEntry (replayRetain runs n first.index) }} := by
  wp_start as ⟨#Hold, #Hsl, #Hall⟩
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Hrows := Hall
  iunfold entriesAt at Hrows
  icases Hrows with ⟨%hlen, #Hrow⟩
  have hp : 0 < ls.length := by simp only [List.length_cons] at hlen; omega
  ihave %hslen := ownSlice_len ents _ ls $$ Hsl
  have hne : ents.len ≠ W64 0 := by word
  have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z ents.len := by constructor <;> word
  have he := List.getElem?_eq_getElem hp
  icases ownSlice_elem_acc (sint.Z (W64 0)) ls[0] ents DFrac.discard ls (by decide) he $$ Hsl with ⟨#Hptr, -⟩
  ihave #Hfirst := Hrow $$ %(0 : Nat) %(ls[0]) %first %he %rfl
  (try wp_auto)
  simp only [hne, decide_false]
  (try wp_auto)
  (try simp only [hb])
  (try wp_auto)
  wp_apply wp_entryAt_GetIndex getIndex ls[0] first $$ [$Hpb $Hfirst]
  (try wp_auto)
  wp_bind (App (App (App (Val doFor) _) _) _)
  have htrim := fun Ψ => replayTrimLoop_wp (GF := GF) r_ptr n_ptr first_ptr r first.index runs Ψ
  unfold replayTrimLoop at htrim
  iapply (htrim _)
  iframe
  iframe Hold
  iintro %k Hr Hn Hf %hcut
  obtain ⟨h0, hn, hremoved, hlast⟩ := hcut
  ihave %hrlen := ownSlice_len r _ runs $$ Hold
  have hkl : sint.nat k ≤ sint.nat r.len := by rw [← hrlen.1]; exact hn
  change (sint.Z k).toNat ≤ (sint.Z r.len).toNat at hkl
  have hk : 0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z r.len := by omega
  ihave ⟨#Hpre, Hcap⟩ := replayTerms_prefix r runs k hk $$ Hold
  ihave %hrwf := ownSlice_wf r _ runs $$ Hold
  have hfc : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z k ∧ sint.Z k ≤ sint.Z k ∧ sint.Z k ≤ sint.Z r.cap := by
    have : sint.Z (W64 0) = 0 := by decide
    omega
  (try wp_auto)
  simp only [hfc, ↓reduceIte]
  (try wp_auto)
  wp_join iprop(∃ sl : GoSlice, out_ptr ↦ sl ∗ sl ↦*□ replayRetain runs (sint.nat k) first.index ∗
      ownSliceCap replayTermRun sl (DFrac.own 1)) at next
    with [out Hr Hn Hf Hcap] as ⟨%base, Hout, #Hbase, HbaseCap⟩
  · by_cases hlt : sint.Z k < sint.Z r.len
    · have hklt : sint.nat k < runs.length := by word
      let x := runs[sint.nat k]
      have hx : runs[sint.nat k]? = some x := List.getElem?_eq_getElem hklt
      icases ownSlice_elem_acc (sint.Z k) x r DFrac.discard runs h0 hx $$ Hold with ⟨#Hx, -⟩
      iStructNamed Hx
      (try wp_auto)
      (try simp only [hlt, _root_.decide_true, ↓reduceIte])
      (try wp_auto)
      (try simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z r.len from ⟨h0, hlt⟩, ↓reduceIte])
      (try wp_auto)
      by_cases hpart : uint.Z x.first' < uint.Z first.index
      · simp only [hpart, _root_.decide_true, ↓reduceIte]
        have hi : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z r.len := ⟨h0, hlt⟩
        (try wp_auto)
        (try simp only [hi, ↓reduceIte])
        (try wp_auto)
        (try simp only [hi, ↓reduceIte])
        (try wp_auto)
        (try simp only [hi, ↓reduceIte])
        (try wp_auto)
        let cut := replayTermRun.mk x.first' (first.index - W64 1) x.term'
        wp_apply wp_slice_literal (V := replayTermRun) [cut]
        isplitr; · ipureintro; rfl
        iintro %added ⟨Hadded, -⟩
        (try wp_auto)
        wp_apply wp_slice_append_persistent (V := replayTermRun) _ _ _ _ (DFrac.own 1)
          $$ [$Hpre $Hcap $Hadded] as %sl ⟨#Hsl', Hcap', -⟩
        (try wp_auto)
        isplitr; · ipureintro; rfl
        iexists sl
        have hc : uint.nat x.first' < uint.nat first.index := by word
        simp only [replayRetain, hx, hc, ↓reduceIte]
        iframe Hsl' Hcap'; iframe
      · simp only [hpart, decide_false, ↓reduceIte]
        (try wp_auto)
        isplitr; · ipureintro; rfl
        iexists slice.fullSlice r replayTermRun (W64 0) k k
        have hc : ¬ uint.nat x.first' < uint.nat first.index := by word
        simp only [replayRetain, hx, hc, ↓reduceIte]
        iframe Hpre Hcap; iframe
    · (try wp_auto)
      (try simp only [hlt, decide_false, ↓reduceIte])
      (try wp_auto)
      isplitr; · ipureintro; rfl
      iexists slice.fullSlice r replayTermRun (W64 0) k k
      have hz : sint.nat k = runs.length := by word
      have hnone : runs[sint.nat k]? = none := by simp [hz]
      simp only [replayRetain, hnone]
      iframe Hpre Hcap; iframe
  · (try wp_auto)
    ihave HI : (∃ (out ents : GoSlice) (ptrs : List Loc) (xs : List EntryModel) (acc : List replayTermRun),
        "Hout" ∷ out_ptr ↦ out ∗ "He" ∷ ents_ptr ↦ ents ∗ "#Hacc" ∷ out ↦*□ acc ∗
        "Hcap" ∷ ownSliceCap replayTermRun out (DFrac.own 1) ∗
        "#Hptrs" ∷ ents ↦*□ ptrs ∗ "#Hxs" ∷ entriesAt ptrs xs ∗
        "%horder" ∷ ⌜xs.Pairwise (fun a b => uint.nat a.term ≤ uint.nat b.term)⌝ ∗
        "%hequiv" ∷ ⌜xs.foldl replayAddEntry acc = (first :: es).foldl replayAddEntry
          (replayRetain runs (sint.nat k) first.index)⌝ : IProp GF) $$ [Hout ents HbaseCap]
    · iexists base, ents, ls, first :: es, replayRetain runs (sint.nat k) first.index
      iframe Hout Hbase HbaseCap Hsl Hall; iframe
      isplitr; · ipureintro; exact ordered
      ipureintro; rfl
    wp_for HI
    ihave %hs := ownSlice_len ents _ ptrs $$ Hptrs
    ihave #Hrows' := Hxs
    iunfold entriesAt at Hrows'
    icases Hrows' with ⟨%hl, #Hat⟩
    cases xs with
    | nil =>
      have hz : ¬ sint.Z (W64 0) < sint.Z ents.len := by simp only [List.length_nil] at hl; word
      (try wp_auto)
      simp only [hz, decide_false, ↓reduceIte]
      (try wp_auto)
      (try simp only [intoVal_eq_iff, Bool.false_eq_true, decide_false, _root_.decide_true, ↓reduceIte])
      (try wp_auto)
      iapply HΦ
      iexists sint.nat k
      isplitr; · ipureintro; exact ⟨hn, hremoved, hlast⟩
      simp only [List.foldl_nil] at hequiv
      rw [← hequiv]; iexact Hacc
    | cons e xs =>
      have hlen : 0 < ptrs.length := by simp only [List.length_cons] at hl; omega
      have hpos : sint.Z (W64 0) < sint.Z ents.len := by word
      have hfirst : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z ents.len := ⟨by decide, hpos⟩
      have hend : 0 ≤ sint.Z (ents.len - W64 1) ∧ sint.Z (ents.len - W64 1) < sint.Z ents.len := by constructor <;> word
      have hlastIx : sint.nat (ents.len - W64 1) = ptrs.length - 1 := by word
      let pel := ptrs[ptrs.length - 1]
      let last := (e :: xs)[(e :: xs).length - 1]
      have hp0 := List.getElem?_eq_getElem hlen
      have hpl : ptrs[sint.nat (ents.len - W64 1)]? = some pel := by rw [hlastIx]; exact List.getElem?_eq_getElem (by omega)
      have hel : (e :: xs)[sint.nat (ents.len - W64 1)]? = some last := by rw [hlastIx, hl]; exact List.getElem?_eq_getElem (by simp)
      icases ownSlice_elem_acc (sint.Z (W64 0)) ptrs[0] ents DFrac.discard ptrs (by decide) hp0 $$ Hptrs with ⟨#Hp0, -⟩
      icases ownSlice_elem_acc (sint.Z (ents.len - W64 1)) pel ents DFrac.discard ptrs hend.1 hpl $$ Hptrs with ⟨#Hpl, -⟩
      ihave #He0 := Hat $$ %(0 : Nat) %(ptrs[0]) %e %hp0 %rfl
      ihave #Hel := Hat $$ %(sint.nat (ents.len - W64 1)) %pel %last %hpl %hel
      (try wp_auto)
      (try simp only [hpos, _root_.decide_true, ↓reduceIte])
      (try wp_auto)
      (try simp only [hfirst])
      (try wp_auto)
      wp_apply wp_entryAt_GetTerm getTerm ptrs[0] e $$ [$Hpb $He0]
      (try wp_auto)
      (try simp only [hend])
      (try wp_auto)
      wp_apply wp_entryAt_GetTerm getTerm pel last $$ [$Hpb $Hel]
      (try wp_auto)
      wp_join iprop(∃ c : w64, count_ptr ↦ c ∗ term_ptr ↦ e.term ∗ ents_ptr ↦ ents ∗
          ⌜0 < sint.Z c ∧ sint.nat c ≤ (e :: xs).length ∧
            ∀ (i : Nat) (hi : i < (e :: xs).length), i < sint.nat c → (e :: xs)[i].term = e.term⌝) at next
        with [count term He] as ⟨%c, Hcount, Hterm, He, %hc⟩
      · by_cases same : last.term = e.term
        · simp only [same, _root_.decide_true, Bool.not_true]
          (try wp_auto)
          isplitr; · ipureintro; rfl
          iexists ents.len; iframe
          ipureintro
          refine ⟨by word, by omega, fun i hi _ => ?_⟩
          exact replayBatch_sameTerm (e :: xs) (by simp) horder same i hi
        · simp only [same, decide_false, Bool.not_false]
          (try wp_auto)
          wp_bind (App (App (App (Val doFor) _) _) _)
          have hscan := fun Ψ => replayCountLoop_wp (GF := GF) ents_ptr count_ptr term_ptr
            ents ptrs (e :: xs) (by simp) e.term rfl same getTerm Ψ
          unfold replayCountLoop at hscan
          iapply (hscan _)
          iframe Hpb Hptrs Hxs; iframe
          iintro %c' He Hc Ht %hfound
          obtain ⟨hpos', hlt', -, hall⟩ := hfound
          (try wp_auto)
          isplitr; · ipureintro; rfl
          iexists c'; iframe
          ipureintro; exact ⟨hpos', Nat.le_of_lt hlt', hall⟩
      · obtain ⟨hcpos, hcb, hall⟩ := hc
        have hind : sint.nat c - 1 < (e :: xs).length := by word
        have hsub : sint.nat (c - W64 1) = sint.nat c - 1 := by word
        have hbnd : 0 ≤ sint.Z (c - W64 1) ∧ sint.Z (c - W64 1) < sint.Z ents.len := by
          have hs' : sint.nat c ≤ sint.nat ents.len := by rw [← hs.1, hl]; exact hcb
          change (sint.Z c).toNat ≤ (sint.Z ents.len).toNat at hs'
          constructor <;> word
        let ptrLast := ptrs[sint.nat c - 1]
        let entryLast := (e :: xs)[sint.nat c - 1]
        have hptrLast : ptrs[sint.nat (c - W64 1)]? = some ptrLast := by rw [hsub]; exact List.getElem?_eq_getElem (by omega)
        have hentLast : (e :: xs)[sint.nat (c - W64 1)]? = some entryLast := by rw [hsub]; exact List.getElem?_eq_getElem hind
        icases ownSlice_elem_acc (sint.Z (c - W64 1)) ptrLast ents DFrac.discard ptrs hbnd.1 hptrLast $$ Hptrs with ⟨#HptrLast, -⟩
        ihave #HentLast := Hat $$ %(sint.nat (c - W64 1)) %ptrLast %entryLast %hptrLast %hentLast
        (try wp_auto)
        (try simp only [hfirst])
        (try wp_auto)
        wp_apply wp_entryAt_GetIndex getIndex ptrs[0] e $$ [$Hpb $He0]
        (try wp_auto)
        (try simp only [hbnd])
        (try wp_auto)
        wp_apply wp_entryAt_GetIndex getIndex ptrLast entryLast $$ [$Hpb $HentLast]
        (try wp_auto)
        let fresh := replayTermRun.mk e.index entryLast.index e.term
        ihave %hlenout := ownSlice_len out _ acc $$ Hacc
        ihave %hcapout := ownSlice_wf out _ acc $$ Hacc
        wp_join iprop(∃ (sl : GoSlice) (pre : List replayTermRun) (newRun : replayTermRun),
            out_ptr ↦ sl ∗ sl ↦*□ pre ∗ ownSliceCap replayTermRun sl (DFrac.own 1) ∗ run_ptr ↦ newRun ∗
            ⌜pre ++ [newRun] = replayJoin acc fresh⌝) at next
          with [Hout Hcap run n Hterm] as ⟨%sl, %pre, %newRun, Hout, #Hpre', Hcap', Hrun, %hjoin⟩
        · by_cases ha : acc = []
          · have hz : ¬ sint.Z (W64 0) < sint.Z out.len := by rw [ha] at hlenout; simp at hlenout; word
            simp only [hz, decide_false, ↓reduceIte]
            (try wp_auto)
            isplitr; · ipureintro; rfl
            iexists out, acc, fresh
            iframe Hout Hacc Hcap run
            ipureintro; simp [ha, replayJoin]
          · obtain ⟨pre, prev, hac⟩ : ∃ pre prev, acc = pre ++ [prev] :=
              ⟨acc.dropLast, acc.getLast ha, (List.dropLast_concat_getLast ha).symm⟩
            have haLen : acc.length = pre.length + 1 := by simp [hac]
            have hp : sint.Z (W64 0) < sint.Z out.len := by word
            have hidx : sint.nat (out.len - W64 1) = pre.length := by word
            have hprev : acc[sint.nat (out.len - W64 1)]? = some prev := by rw [hac, hidx]; simp
            have hi : 0 ≤ sint.Z (out.len - W64 1) ∧ sint.Z (out.len - W64 1) < sint.Z out.len := by constructor <;> word
            icases ownSlice_elem_acc (sint.Z (out.len - W64 1)) prev out DFrac.discard acc hi.1 hprev $$ Hacc with ⟨#Hprev, -⟩
            iStructNamedSuffix Hprev "Prev"
            simp only [hp, _root_.decide_true, ↓reduceIte]
            (try wp_auto)
            simp only [hi, ↓reduceIte]
            (try wp_auto)
            by_cases same : prev.term' = e.term
            · simp only [same, _root_.decide_true, ↓reduceIte]
              icases typedPointsto_not_null_dup _ _ _ $$ run with ⟨run, %hnn⟩
              iStructNamedSuffix run "Run"
              (try wp_auto)
              (try simp only [hi])
              (try wp_auto)
              have hslice : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (out.len - W64 1) ∧
                  sint.Z (out.len - W64 1) ≤ sint.Z (out.len - W64 1) ∧ sint.Z (out.len - W64 1) ≤ sint.Z out.cap := by
                have : sint.Z (W64 0) = 0 := by decide
                omega
              (try simp only [hslice, ↓reduceIte])
              (try wp_auto)
              ihave ⟨#Hcut, HcutCap⟩ := replayTerms_prefix out acc (out.len - W64 1) ⟨hi.1, Int.le_of_lt hi.2⟩ $$ Hacc
              have htake : acc.take (sint.nat (out.len - W64 1)) = pre := by rw [hac, hidx]; simp
              ihave Hrun : run_ptr ↦ ({ fresh with first' := prev.first' } : replayTermRun) $$ [firstRun lastRun termRun]
              · iapply typedPointsto_combine _ _ _ hnn
                simp only [TypedPointsto.typedPointstoDef]
                iframe
              isplitr; · ipureintro; rfl
              iexists _, pre, { fresh with first' := prev.first' }
              rw [htake]
              iframe Hcut HcutCap Hrun; iframe
              ipureintro; rw [hac, replayJoin_snoc]; simp [fresh, same]
            · simp only [same, decide_false, ↓reduceIte]
              (try wp_auto)
              isplitr; · ipureintro; rfl
              iexists out, acc, fresh
              iframe Hout Hacc Hcap run
              ipureintro; rw [hac, replayJoin_snoc]; simp [fresh, same]
        · (try wp_auto)
          wp_apply wp_slice_literal (V := replayTermRun) [newRun]
          isplitr; · ipureintro; rfl
          iintro %added ⟨Hadded, -⟩
          (try wp_auto)
          wp_apply wp_slice_append_persistent (V := replayTermRun) sl pre _ _ (DFrac.own 1)
            $$ [$Hpre' $Hcap' $Hadded] as %out' ⟨#Hacc', Hcap', -⟩
          (try wp_auto)
          ihave %hwf := ownSlice_wf ents _ ptrs $$ Hptrs
          have hns : sint.nat c ≤ sint.nat ents.len := by rw [← hs.1, hl]; exact hcb
          change (sint.Z c).toNat ≤ (sint.Z ents.len).toNat at hns
          have hbnd' : 0 ≤ sint.Z c ∧ sint.Z c ≤ sint.Z ents.len ∧ sint.Z ents.len ≤ sint.Z ents.cap := by omega
          (try simp only [hbnd', ↓reduceIte])
          (try wp_auto)
          icases (ownSlice_slice c ents.len ents DFrac.discard ptrs ⟨hbnd'.1, hbnd'.2.1, Int.le_refl _⟩).1 $$ Hptrs
            with ⟨-, #Hmid, -⟩
          have hsub' : subslice (sint.nat c) (sint.nat ents.len) ptrs = ptrs.drop (sint.nat c) := by
            unfold subslice; rw [← hs.1, List.take_length]
          ihave #Hrest := entriesAt_drop ptrs (e :: xs) (sint.nat c) $$ Hxs
          wp_for_post
          iframe
          iexists out', _, ptrs.drop (sint.nat c), (e :: xs).drop (sint.nat c), pre ++ [newRun]
          rw [hsub']
          iframe Hacc' Hcap' Hmid Hrest; iframe
          isplitr
          · ipureintro; exact horder.sublist (List.drop_sublist _ _)
          ipureintro
          rw [hjoin, ← hequiv]
          exact replayFold_group acc e xs (sint.nat c) (by word) hcb hall

end EtcdGrove
end Perennial
