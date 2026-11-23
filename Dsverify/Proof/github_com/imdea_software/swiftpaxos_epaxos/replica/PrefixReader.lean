/-
`prefixReader.Read` (package-internal): the `io.Reader` `&prefixReader{first, conn}` that
`clientListener` buffers returns the bytes `first` (already read from the connection) and then
the connection's bytes. Over `Net/` (not the lab's: hand-maintained, notes/dsv-epaxos.md): its
contract is Perennial's `io.readerOk` with the connection's `Pre` (a non-empty buffer), stream
state `prI` (a prefix of what the connection's reader has received, `recvTokL`, from `first` on)
and errors `connReadE` (`net.conn_readerOk`'s); `prRd` is the marshal layer's `BufRd` over it,
with the stream fact `▷ protoPrefix`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Specs
public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos_epaxos.replica

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]

/-- The stream state of the prefix reader `pr` over the connection `c` (end `true` of `cid`,
protocol `P`) whose first bytes are `first`: `R` returned so far; `k` of the first bytes given,
then `Rc` read from the connection (only once all of `first` is given). -/
def prI (pr : Loc) (c : GoInterface) (cid : Nat) (P : Proto GF) (first : List w8)
    (R : List w8) : IProp GF :=
  iprop(∃ (sl : GoSlice) (k : Nat) (Rc : List w8),
    structFieldRef replica.prefixReader go!"first" pr ↦ sl ∗
    structFieldRef replica.prefixReader go!"conn" pr ↦□ c ∗
    sl ↦* first.drop k ∗ recvTokL (Gg := hG.goose_globalGS) cid true P (first ++ Rc) ∗
    ⌜k ≤ first.length ∧ R = first.take k ++ Rc ∧ (Rc ≠ [] → k = first.length)⌝)

/-- What the prefix reader returned is a prefix of what the connection received, a step later. -/
theorem prI_proto (pr : Loc) (c : GoInterface) (cid : Nat) (P : Proto GF) (first R : List w8) :
    prI pr c cid P first R ⊢ prI pr c cid P first R ∗ ▷ protoPrefix P cid R := by
  unfold prI
  iintro ⟨%sl, %k, %Rc, Hf, #Hc, Hs, Hr, %Hk⟩
  ihave ⟨Hr, #Hp⟩ := recvTokL_proto cid true P (first ++ Rc) $$ Hr
  isplitl [Hf Hs Hr]
  · iexists sl, k, Rc; iframe; iframe #; ipureintro; exact Hk
  iapply later_mono (protoPrefix_le ?_) $$ Hp
  rw [Hk.2.1]
  rcases Classical.em (Rc = []) with h | h
  · subst h; simpa using List.take_prefix k first
  · rw [Hk.2.2 h, List.take_of_length_le (Nat.le_refl _)]; exact List.prefix_refl _

theorem copy_data_eq (bs rest : List w8) :
    (rest.take bs.length ++ bs.drop rest.length) =
      rest.take bs.length ++ bs.drop (rest.take bs.length).length := by
  rcases Nat.le_total bs.length rest.length with h | h
  · rw [List.length_take, Nat.min_eq_left h, List.drop_of_length_le h,
      List.drop_of_length_le (Nat.le_refl _)]
  · rw [List.length_take, Nat.min_eq_right h]

/-- The prefix reader `&prefixReader{first, conn}` as an `io.Reader`. -/
abbrev prIface (pr : Loc) : GoInterfaceOk := ⟨go.GoType.PointerType replica.prefixReader.ty, #pr⟩

/-- `prefixReader.Read` meets `io.readerOk` (see the file header). -/
theorem prefixReader_readerOk [_root_.Perennial.io.Assumptions] [net.Assumptions] [net.FieldAssumptions]
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (pr t : Loc) (cid : Nat) (a : GoString) (la ra eof ed : GoInterface) (P : Proto GF)
    (first : List w8) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.replica ∗
      isPkgInit (PROP := IProp GF) pkg_id.io ∗ net.connAt (GF := GF) t cid true a la ra ∗
      globalAddr io.EOF ↦□ eof ∗ globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ⊢
      io.readerOk (prIface pr) (fun _ m => 0 < m)
        (prI pr (interface.ok (net.connIface t)) cid P first) (net.connReadE eof la ra ed) := by
  iintro ⟨#Hpkg, #Hio, #Hc, #Heof, #Hed⟩
  unfold io.readerOk
  iintro !> %R %b %bs
  iintro !> %Φ ⟨%hpos, HI, Hb⟩ HΦ
  unfold prI
  icases HI with ⟨%sl, %k, %Rc, Hf, #Hcn, Hs, Hr, %Hk⟩
  dsimp only [prIface]
  wp_method_call
  wp_call
  wp_auto
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  have hZ : sint.Z sl.len = ((first.drop k).length : Int) := by
    rw [Hsl.1]
    first | (exact (Int.toNat_of_nonneg Hsl.2).symm) | (simp [sint.nat]; omega) | word
  rcases Nat.lt_or_ge k first.length with hk | hk
  · -- some of the first bytes are left: copy them
    have hRc : Rc = [] := by
      rcases Classical.em (Rc = []) with h | h
      · exact h
      · exact absurd (Hk.2.2 h) (by omega)
    subst hRc
    have hpos' : 0 < (first.drop k).length := by simp; omega
    rw [show decide (sint.Z (W64 0) < sint.Z sl.len) = true by
      simp only [decide_eq_true_eq]; rw [show sint.Z (W64 0) = 0 by decide]; omega]
    wp_auto
    wp_apply wp_slice_copy_int (V := w8) b bs sl (first.drop k) (DFrac.own 1) $$ [$Hb $Hs]
      as %n ⟨%Hn, Hb, Hs⟩
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
    have hb : 0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧ sint.Z sl.len ≤ sint.Z sl.len := by
      refine ⟨?_, ?_, Int.le_refl _⟩ <;> omega
    rw [ite_eq_left_iff.mpr (fun h => absurd ⟨hb.1, hb.2.1, Hwf.2⟩ h)]
    icases (ownSlice_slice (V := w8) n sl.len sl _ _ hb).1 $$ Hs with ⟨-, Hs, -⟩
    wp_auto
    have hnW : n = W64 (((first.drop k).take bs.length).length : Int) := by
      have hlen : ((first.drop k).take bs.length).length = min bs.length (first.drop k).length := by
        simp only [List.length_take]
      rw [hlen]
      apply BitVec.eq_of_toInt_eq
      have h1 : min bs.length (first.drop k).length < 2 ^ 63 := by
        have := Hsl.1; have : (first.drop k).length < 2 ^ 63 := by rw [this]; word
        omega
      rw [show (W64 ((min bs.length (first.drop k).length : Nat) : Int)).toInt =
        ((min bs.length (first.drop k).length : Nat) : Int) by word]
      exact Hn
    rw [hnW]
    iapply HΦ
    iexists (first.drop k).take bs.length
    isplitr
    · ipureintro
      refine ⟨?_, by simp only [List.length_take]; exact Nat.min_le_left _ _⟩
      have h2 : ((first.drop k).take bs.length).length < 2 ^ 63 := by
        have : (first.drop k).length < 2 ^ 63 := by rw [Hsl.1]; word
        simp only [List.length_take]; omega
      word
    isplitl [Hb]
    · rw [← copy_data_eq]; iexact Hb
    isplitl [Hf Hs Hr]
    · iexists _, k + ((first.drop k).take bs.length).length, []
      iframe; iframe #
      isplitl [Hs]
      · have hl : sint.nat sl.len = (first.drop k).length := Hsl.1.symm
        have hn : sint.nat (W64 (((first.drop k).take bs.length).length : Int)) =
            ((first.drop k).take bs.length).length := by
          have h1 : ((first.drop k).take bs.length).length ≤ (first.drop k).length := by simp; omega
          have h2 : (first.drop k).length < 2 ^ 63 := by rw [Hsl.1]; word
          word
        rw [hn, hl]
        unfold subslice
        rw [List.take_of_length_le (Nat.le_refl _), List.drop_drop]
        iexact Hs
      ipureintro
      refine ⟨by simp; omega, ?_, fun h => absurd rfl h⟩
      rw [Hk.2.1]
      simp only [List.append_nil, List.length_take]
      rw [List.take_add]
      congr 1
      exact List.take_eq_take_min
    isplitl
    · unfold io.errAt; ileft; ipureintro; rfl
    ipureintro; exact io.ptrTyped_nil
  · -- all the first bytes are given: read from the connection
    have hk' : k = first.length := by have := Hk.1; omega
    subst hk'
    rw [show decide (sint.Z (W64 0) < sint.Z sl.len) = false by
      simp only [decide_eq_false_iff_not]; rw [show sint.Z (W64 0) = 0 by decide, hZ]; simp]
    wp_auto
    ihave #Hcr := net.conn_readerOk wp_Read t cid true a la ra eof ed P $$ [Hio Hc Heof Hed]
    · iframe #
    iunfold io.readerOk at Hcr
    iunfold net.connIface at Hcr
    wp_bind (App (Val #(methods (go.GoType.PointerType net.TCPConn.ty) go!"Read" #t)) (Val #b))
    iapply Hcr $$ [Hr Hb]
    · iframe Hr Hb; ipureintro; exact hpos
    iintro !> %n %err ⟨%ys, %Hys, Hb, Hr, #He, %Hpt⟩
    wp_auto
    iapply HΦ
    iexists ys
    iframe Hb
    isplitr
    · ipureintro; exact Hys
    isplitl [Hf Hs Hr]
    · iexists sl, first.length, Rc ++ ys
      rw [← List.append_assoc]
      iframe; iframe #
      ipureintro
      refine ⟨Nat.le_refl _, by rw [Hk.2.1]; simp, fun _ => rfl⟩
    have hR : R ++ ys = first ++ Rc ++ ys := by rw [Hk.2.1]; simp
    rw [hR]
    iframe He
    ipureintro; exact Hpt

/-- The marshal layer's reader bundle of `clientListener`'s `bufio.NewReader(&prefixReader{first,
conn})` (see the file header; its contract is `prefixReader_readerOk`). -/
def prRd (pr t : Loc) (cid : Nat) (eof la ra ed : GoInterface) (P : Proto GF) (first : List w8) :
    BufRd GF where
  ri := prIface pr
  Pre := fun _ m => 0 < m
  S := prI pr (interface.ok (net.connIface t)) cid P first
  E := net.connReadE eof la ra ed
  F := fun r => iprop(▷ protoPrefix P cid r)
  F_pers := fun _ => inferInstance
  F_of := fun r => prI_proto pr _ cid P first r
  F_pre := fun x y => later_mono (protoPrefix_le (List.prefix_append x y))
  Pre_pos := fun _ _ h => h

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
