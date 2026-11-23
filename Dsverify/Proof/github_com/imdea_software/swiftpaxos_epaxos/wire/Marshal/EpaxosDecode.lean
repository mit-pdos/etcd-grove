/-
Pure facts for the epaxos decoders (internal to the wire package): reading a stream that is a
prefix of an encoding, component by component.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Marshal.EpaxosCommon

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open model

theorem pfx_skip {α} {P P' t rest : List α} (hl : P.length = P'.length) (h : P ++ t <+: P' ++ rest) :
    t <+: rest := prefix_skip P P' t rest hl h

theorem pfx_assoc {α} {a b c : List α} (h : a ++ b <+: c) : a <+: c :=
  (List.prefix_append a b).trans h

/-- A varint read at the front of an encoded length. -/
theorem varint_head (x : w64) (n : Nat) (hn : n < 2 ^ 63) (t rest : List w8)
    (h : varintEnc x ++ t <+: encLen n ++ rest) : x = W64 (n : Int) ∧ t <+: rest := by
  obtain ⟨u, hu⟩ := h
  rw [encLen_varint _ hn, List.append_assoc] at hu
  obtain ⟨h1, h2⟩ := varintEnc_prefix _ _ _ _ hu
  exact ⟨h1, ⟨u, h2⟩⟩

theorem varint_next (n : Nat) (hn : n < 2 ^ 63) (t rest : List w8) (h : t <+: encLen n ++ rest) :
    ∃ (v : w64) (ext : List w8), True ∧ t <+: varintEnc v ++ ext :=
  ⟨W64 (n : Int), rest, trivial, by rw [← encLen_varint _ hn]; exact h⟩

theorem W64_nat_inj (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63)
    (h : W64 (a : Int) = W64 (b : Int)) : a = b := by
  have h1 := congrArg BitVec.toNat h
  simp [W64] at h1
  omega

theorem cmds_split (cs read : List WCmd) (hwf : ∀ c ∈ cs, cmdWf c) (hrd : ∀ c ∈ read, cmdWf c)
    (hi : read.length ≤ cs.length) (t rest : List w8)
    (h : (read.map encCommand).flatten ++ t <+: (cs.map encCommand).flatten ++ rest) :
    read = cs.take read.length ∧ t <+: ((cs.drop read.length).map encCommand).flatten ++ rest := by
  obtain ⟨u, hu⟩ := h
  rw [← List.take_append_drop read.length cs, List.map_append, List.flatten_append,
    List.append_assoc, List.append_assoc] at hu
  obtain ⟨h1, h2⟩ := flatten_map_prefix cmdWf encCommand
    (fun a b ha hb x y hab => encCommand_prefix a b ha hb x y hab) read (cs.take read.length) hrd
    (fun c hc => hwf c (List.mem_of_mem_take hc)) (by simp; omega) _ _ hu
  exact ⟨h1, ⟨u, h2⟩⟩

theorem cmds_next (cs read : List WCmd) (hwf : ∀ c ∈ cs, cmdWf c) (hrd : ∀ c ∈ read, cmdWf c)
    (hi : read.length < cs.length) (t rest : List w8)
    (h : (read.map encCommand).flatten ++ t <+: (cs.map encCommand).flatten ++ rest) :
    ∃ (c : WCmd) (ext : List w8), cmdWf c ∧ t <+: encCommand c ++ ext := by
  obtain ⟨-, h2⟩ := cmds_split cs read hwf hrd (by omega) t rest h
  rw [List.drop_eq_getElem_cons hi, List.map_cons, List.flatten_cons, List.append_assoc] at h2
  exact ⟨_, _, hwf _ (List.getElem_mem hi), h2⟩

theorem cmds_done (cs read : List WCmd) (hwf : ∀ c ∈ cs, cmdWf c) (hrd : ∀ c ∈ read, cmdWf c)
    (hl : read.length = cs.length) (t rest : List w8)
    (h : (read.map encCommand).flatten ++ t <+: (cs.map encCommand).flatten ++ rest) :
    read = cs ∧ t <+: rest := by
  obtain ⟨h1, h2⟩ := cmds_split cs read hwf hrd (by omega) t rest h
  rw [hl, List.drop_length, List.map_nil, List.flatten_nil, List.nil_append] at h2
  rw [hl, List.take_length] at h1
  exact ⟨h1, h2⟩

section heap
open Iris Iris.BI Iris.ProofMode
attribute [local instance] GooseGlobalGS.gooseInvGS
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics] [state.Assumptions]

/-- One more decoded command at the end of the decoded slice. -/
theorem cmds_snoc (vsd : List state.Command) (rdc : List WCmd) (hl : vsd.length = rdc.length)
    (cv : state.Command) (wc : WCmd) :
    (([∗list] k ↦ c ∈ vsd, ∃ wc', ⌜rdc[k]? = some wc'⌝ ∗ cmdOk c wc') ∗ cmdOk cv wc :
      IProp GF) ⊢
      [∗list] k ↦ c ∈ vsd ++ [cv], ∃ wc', ⌜(rdc ++ [wc])[k]? = some wc'⌝ ∗ cmdOk c wc' := by
  refine (sep_mono ?_ ?_).trans BigSepL.bigSepL_snoc.2
  · apply BigSepL.bigSepL_mono
    intro k x hx
    have hk : k < rdc.length := by
      have := (List.getElem?_eq_some_iff.mp hx).1; omega
    rw [List.getElem?_append_left hk]
  · iintro #H
    iexists wc
    iframe H
    ipureintro
    rw [List.getElem?_append_right (by omega), hl, Nat.sub_self]; rfl

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
