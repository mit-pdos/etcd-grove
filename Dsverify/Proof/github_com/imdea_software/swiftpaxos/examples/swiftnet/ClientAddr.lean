/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/ClientAddr.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`host(addr)` and `port(addr)` (`kit.go`): the parts of `"host:port"` around the first `":"`,
the port's digits read as a `uint64` (wrapping, as Go's arithmetic).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base
public import Perennial.Proof.strings
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace adapter

/-- `port`'s loop: the digits of `p` read in base 10 (Go's wrapping `uint64` arithmetic). -/
def portVal (p : GoString) : w64 :=
  p.foldl (fun n ch => n * W64 10 + W64 (uint.Z (ch - W8 48))) (W64 0)

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [examples.swiftnet.Assumptions]

/-- `host(addr)`: the field before the first `":"`. -/
abbrev host.spec : Prop :=
  ∀ (a h : GoString) (t : List GoString), strings.split a go!":" = h :: t →
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet }}
    (App (Val (@! examples.swiftnet.host)) (Val #a))
  {{ RET #h; True }}

/-- `port(addr)`: the second field's digits. -/
abbrev port.spec : Prop :=
  ∀ (a h p : GoString) (t : List GoString), strings.split a go!":" = h :: p :: t →
  p.length < 2 ^ 32 →
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet }}
    (App (Val (@! examples.swiftnet.port)) (Val #a))
  {{ RET #(portVal p); True }}

end specs

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [examples.swiftnet.Assumptions]

set_option goose.wp.extras true

theorem host.wp_proof : host.spec := fun a h t hs => by
  wp_start
  wp_auto
  wp_apply strings.wp_Split a go!":" (by decide) as %sl ⟨Hsl, Hcap⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  rw [hs] at Hlen
  have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := by
    obtain ⟨h1, h2⟩ := Hlen
    simp only [List.length_cons] at h1
    constructor <;> word
  simp only [hb, and_self, ↓reduceIte]
  wp_apply wp_load_slice_index sl (sint.Z (W64 0)) (strings.split a go!":") _ h hb.1 $$ [Hsl] as Hsl
  · iframe Hsl
    ipureintro
    rw [hs]; rfl
  iapply HΦ $$ %trivial

theorem port.wp_proof : port.spec := fun a h p t hs hp => by
  wp_start
  wp_auto
  wp_apply strings.wp_Split a go!":" (by decide) as %sl ⟨Hsl, Hcap⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  rw [hs] at Hlen
  have hb : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z sl.len := by
    obtain ⟨h1, h2⟩ := Hlen
    simp only [List.length_cons] at h1
    constructor <;> word
  simp only [hb, and_self, ↓reduceIte]
  wp_apply wp_load_slice_index sl (sint.Z (W64 1)) (strings.split a go!":") _ p hb.1 $$ [Hsl] as Hsl
  · iframe Hsl
    ipureintro
    rw [hs]; rfl
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗ "n" ∷ n_ptr ↦ portVal (p.take (sint.nat i)) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ p.length⌝ : IProp netDistGF) $$ [i n]
  · iexists W64 0
    iframe
    ipureintro; word
  wp_for HI
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hplen
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z (W64 (p.length : Int)) := by
      have h := go.intoVal_inj Hif
      simpa using h
    have hi : sint.nat i < p.length := by
      have : (p.length : Int) < 2 ^ 32 := by exact_mod_cast hp
      word
    list_elem p (sint.nat i) as ch
    simp only [Hi.1, ↓reduceIte, Hch_lookup]
    wp_auto
    wp_for_post
    iframe
    iexists i + W64 1
    have hsucc : sint.nat (i + W64 1) = sint.nat i + 1 := by
      have : (p.length : Int) < 2 ^ 32 := by exact_mod_cast hp
      word
    rw [hsucc, List.take_succ, Hch_lookup]
    simp only [portVal, List.foldl_append, Option.toList_some, List.foldl_cons, List.foldl_nil]
    iframe
    ipureintro
    have : (p.length : Int) < 2 ^ 32 := by exact_mod_cast hp
    constructor <;> word
  · have hlt : ¬ sint.Z i < sint.Z (W64 (p.length : Int)) := by
      intro h; apply Hif; simp only [decide_eq_true h]
    simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    have hi : sint.nat i = p.length := by
      have : (p.length : Int) < 2 ^ 32 := by exact_mod_cast hp
      word
    rw [hi, List.take_length]
    iapply HΦ $$ %trivial

end proofs

end adapter

end Perennial.github_com.imdea_software.swiftpaxos
