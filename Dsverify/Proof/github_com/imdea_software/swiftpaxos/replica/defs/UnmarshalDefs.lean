/-
The definitions, specs and lemmas of `Unmarshal.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.WireWf
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos.replica.defs
public import Perennial.Proof.encoding.binary

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

/-- `(*Beacon).Unmarshal(rd)`: the next 8 bytes, the timestamp. -/
abbrev replica.defs.Beacon.Unmarshal.spec : Prop :=
  ∀ (t : Loc) (v : replica.defs.Beacon) (rd : GoInterface) (I : List w8 → IProp GF)
    (R : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ bufio.readsOk rd I ∗ I R ∗ t ↦ v }}
    (App (Val (t @!! go.GoType.PointerType replica.defs.Beacon.ty @!! go!"Unmarshal")) (Val #rd))
  {{ (err : GoInterface), RET #err; ∃ data : List w8, I (R ++ data) ∗
      ((⌜err = interface.nil⌝ ∗ ∃ ts : w64, ⌜data = sp.le64 ts⌝ ∗
          t ↦ replica.defs.Beacon.mk ts) ∨
        (⌜err ≠ interface.nil⌝ ∗ ∃ v' : replica.defs.Beacon, t ↦ v')) }}

/-- `(*BeaconReply).Unmarshal(rd)`: the next 8 bytes, the timestamp. -/
abbrev replica.defs.BeaconReply.Unmarshal.spec : Prop :=
  ∀ (t : Loc) (v : replica.defs.BeaconReply) (rd : GoInterface) (I : List w8 → IProp GF)
    (R : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ bufio.readsOk rd I ∗ I R ∗ t ↦ v }}
    (App (Val (t @!! go.GoType.PointerType replica.defs.BeaconReply.ty @!! go!"Unmarshal")) (Val #rd))
  {{ (err : GoInterface), RET #err; ∃ data : List w8, I (R ++ data) ∗
      ((⌜err = interface.nil⌝ ∗ ∃ ts : w64, ⌜data = sp.le64 ts⌝ ∗
          t ↦ replica.defs.BeaconReply.mk ts) ∨
        (⌜err ≠ interface.nil⌝ ∗ ∃ v' : replica.defs.BeaconReply, t ↦ v')) }}

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

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
