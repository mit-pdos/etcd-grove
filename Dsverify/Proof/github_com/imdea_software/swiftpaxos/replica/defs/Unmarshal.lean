/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/defs/Unmarshal.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`replica/defs`' and `state`'s `Unmarshal` methods (internal specs with their proofs), over an
`io.Reader` given by its `Read` spec (`bufio.readsOk rd I`, the stream read so far `R`): without
an error, the bytes read are the message's body (`Spec/swift/Wire.lean`), and the struct holds
the message.

* `Beacon.Unmarshal`, `BeaconReply.Unmarshal`: `le64 ts`;
* `Operation`, `Key`, `Value`, `Command.Unmarshal`: `encCmd c` (the value's length `< 2^16`);
* `Propose.Unmarshal`: `Msg.body (.propose seq cl c ts)`. (FINDING R-F1, fixed in fix3: the code
  now returns `Command.Unmarshal`'s error.)
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.WireWf
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos.replica.defs
public import Perennial.Proof.encoding.binary
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.defs.UnmarshalDefs

-- PORT: lab imports dropped: Harness.Proof.bufio.ReadFull

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section specs

variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF] [github_com.imdea_software.swiftpaxos.SwiftHyps GF] [github_com.imdea_software.swiftpaxos.SwiftBufioDeps GF]
variable [replica.defs.Assumptions] [state.Assumptions] [io.Assumptions]
  [errors.Assumptions]

end specs

section proofs

variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF] [github_com.imdea_software.swiftpaxos.SwiftHyps GF] [github_com.imdea_software.swiftpaxos.SwiftBufioDeps GF]
variable [replica.defs.Assumptions] [state.Assumptions] [io.Assumptions]
  [errors.Assumptions]

set_option goose.wp.extras true

set_option hygiene false in
/-- Load the 8 bytes `bs[0..7]` of the slice `Hsl`. -/
local macro "ld8" : tactic => `(tactic| (
  wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 1)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 2)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 3)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 4)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 5)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 6)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 7)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl))

theorem replica.defs.Beacon.Unmarshal.wp_proof : replica.defs.Beacon.Unmarshal.spec (GF := GF) := by
  intro t v rd I R
  wp_start as ⟨#Hrd, HI, Ht⟩
  try wp_auto
  ihave Hsl := slice_array b_ptr 8 (Perennial.zero_val (GoArray w8 8)) (by decide) $$ b
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 8 - W64 0 = W64 8 from rfl]
  rw [show (Perennial.zero_val (GoArray w8 8)).arr = List.replicate 8 (W8 0) from rfl]
  wp_apply bufio.wp_ReadAtLeast rd I R _ (List.replicate 8 (W8 0)) (W64 8) ?_ $$
    [$Hpkg $Hrd $HI $Hsl] as %n %err ⟨%data, %Hd, Hsl, HI, #He⟩
  obtain ⟨hn, hdl, herr⟩ := Hd
  rcases err with e | _
  · -- an error: returned
    wp_auto
    iapply HΦ
    iexists data
    iframe HI
    iright
    isplitr
    · ipureintro; intro h; cases h
    iexists v
    iexact Ht
  · -- no error: 8 bytes
    have h8 : data.length = 8 := by
      have := herr.1 rfl; simp at hdl; have : sint.Z (W64 8) = 8 := rfl; omega
    obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, rfl⟩ : ∃ d0 d1 d2 d3 d4 d5 d6 d7 : w8,
        data = [d0, d1, d2, d3, d4, d5, d6, d7] := by
      match data, h8 with
      | [d0, d1, d2, d3, d4, d5, d6, d7], _ => exact ⟨d0, d1, d2, d3, d4, d5, d6, d7, rfl⟩
    simp only [List.length_cons, List.length_nil, List.drop_replicate, List.append_nil] at h8
    isimp only [List.length_cons, List.length_nil, List.drop_replicate, List.append_nil,
      Nat.reduceAdd, Nat.sub_self, List.replicate_zero] at Hsl
    wp_auto
    ld8
    wp_auto
    have hle := leToU64_le [d0, d1, d2, d3, d4, d5, d6, d7] rfl
    rw [encoding.binary.leToU64_8] at hle
    iapply HΦ
    iexists _
    iframe HI
    ileft
    isplitr
    · ipureintro; rfl
    iexists _
    isplitr
    · ipureintro
      exact hle.symm
    iexact Ht

theorem replica.defs.BeaconReply.Unmarshal.wp_proof : replica.defs.BeaconReply.Unmarshal.spec (GF := GF) := by
  intro t v rd I R
  wp_start as ⟨#Hrd, HI, Ht⟩
  try wp_auto
  ihave Hsl := slice_array b_ptr 8 (Perennial.zero_val (GoArray w8 8)) (by decide) $$ b
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 8 - W64 0 = W64 8 from rfl]
  rw [show (Perennial.zero_val (GoArray w8 8)).arr = List.replicate 8 (W8 0) from rfl]
  wp_apply bufio.wp_ReadAtLeast rd I R _ (List.replicate 8 (W8 0)) (W64 8) ?_ $$
    [$Hpkg $Hrd $HI $Hsl] as %n %err ⟨%data, %Hd, Hsl, HI, #He⟩
  obtain ⟨hn, hdl, herr⟩ := Hd
  rcases err with e | _
  · -- an error: returned
    wp_auto
    iapply HΦ
    iexists data
    iframe HI
    iright
    isplitr
    · ipureintro; intro h; cases h
    iexists v
    iexact Ht
  · -- no error: 8 bytes
    have h8 : data.length = 8 := by
      have := herr.1 rfl; simp at hdl; have : sint.Z (W64 8) = 8 := rfl; omega
    obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, rfl⟩ : ∃ d0 d1 d2 d3 d4 d5 d6 d7 : w8,
        data = [d0, d1, d2, d3, d4, d5, d6, d7] := by
      match data, h8 with
      | [d0, d1, d2, d3, d4, d5, d6, d7], _ => exact ⟨d0, d1, d2, d3, d4, d5, d6, d7, rfl⟩
    simp only [List.length_cons, List.length_nil, List.drop_replicate, List.append_nil] at h8
    isimp only [List.length_cons, List.length_nil, List.drop_replicate, List.append_nil,
      Nat.reduceAdd, Nat.sub_self, List.replicate_zero] at Hsl
    wp_auto
    ld8
    wp_auto
    have hle := leToU64_le [d0, d1, d2, d3, d4, d5, d6, d7] rfl
    rw [encoding.binary.leToU64_8] at hle
    iapply HΦ
    iexists _
    iframe HI
    ileft
    isplitr
    · ipureintro; rfl
    iexists _
    isplitr
    · ipureintro
      exact hle.symm
    iexact Ht

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
