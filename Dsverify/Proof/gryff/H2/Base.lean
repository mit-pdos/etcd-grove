/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2/Base.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2: small helpers of the EPaxos handlers

`recordCommands`, `recordInstanceMetadata`, `sync` (no-ops: `Durable` is false),
`isInitialBallot`, `(*Replica).GetStoreMetadata` / `GetCurrentValue`.

All H2 proofs are in sections with one `HeapGS` (hub request H2-R0).
-/
module

public import Dsverify.Proof.gryff.Replica2.Specs
public import Dsverify.Proof.gryff.Replica.Base
public import Dsverify.Proof.gryff.H1.Parti -- C: `GetStoreMetadata.wp` moved to Replica2/Results.lean
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB Proposal Msg Ev Out Cmd Deps)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF] -- H1-R6 / N-1
variable [strconvA : strconv.Assumptions] -- N-5
variable [sortA : Perennial.gryff.replica2.SortSliceHyp GF]


set_option goose.wp.extras true

/-- The handler's link to the replica (`e.R`, `e.R.Replica`), `Durable` false. -/
abbrev hR (h r gR : Loc) : IProp GF :=
  iprop(h.[src.gryff.EPaxosRMWHandler, go!"R"] ↦□ r ∗ r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗
    gR.[src.genericsmr.Replica, go!"Durable"] ↦□ false)

/-- `recordCommands(cmds)`: a no-op (`Durable` is false). -/
theorem wp_recordCommands (h r gR : Loc) (sl : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        h.[src.gryff.EPaxosRMWHandler, go!"R"] ↦□ r ∗ r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗
        gR.[src.genericsmr.Replica, go!"Durable"] ↦□ false }}
      (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!! go!"recordCommands"))
        (Val #sl))
    {{ RET #(); True }} := by
  wp_start as ⟨#HR, #HgR, #Hd⟩
  wp_auto
  wp_end

/-- `recordInstanceMetadata(inst)`: a no-op. -/
theorem wp_recordInstanceMetadata (h r gR : Loc) (p : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        h.[src.gryff.EPaxosRMWHandler, go!"R"] ↦□ r ∗ r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗
        gR.[src.genericsmr.Replica, go!"Durable"] ↦□ false }}
      (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!!
        go!"recordInstanceMetadata")) (Val #p))
    {{ RET #(); True }} := by
  wp_start as ⟨#HR, #HgR, #Hd⟩
  wp_auto
  wp_end

/-- `sync()`: a no-op. -/
theorem wp_sync (h r gR : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        h.[src.gryff.EPaxosRMWHandler, go!"R"] ↦□ r ∗ r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗
        gR.[src.genericsmr.Replica, go!"Durable"] ↦□ false }}
      (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!! go!"sync"))
        (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#HR, #HgR, #Hd⟩
  wp_auto
  wp_end

/-- `isInitialBallot(ballot)`. -/
theorem wp_isInitialBallot (b : w32) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff }}
      (App (Val (@! src.gryff.isInitialBallot)) (Val #b))
    {{ RET #(model.isInitialBallot b); True }} := by
  wp_start
  wp_auto
  have : decide (BitVec.sshiftRight' b (W64 4) = W32 0) = model.isInitialBallot b := rfl
  rw [this]
  wp_end

/-- `r.GetStoreMetadata(0)` (the participant's). -/
theorem wp_Replica_GetStoreMetadata (r pa : Loc) (k : Fin 3) (tag : model.Tag)
    (ong : model.AMap 32 w32) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        r.[src.gryff.Replica, go!"parti"] ↦□ pa ∗ partiOwn pa (replicaIface r) k tag ong }}
      (App (Val (r @!! go.GoType.PointerType src.gryff.Replica.ty @!! go!"GetStoreMetadata"))
        (Val #(W64 0)))
    {{ (md : Loc), RET #md; ∃ (tp : Loc) (gt : src.gryffproto.Tag), ⌜tagOf gt = tag⌝ ∗ tp ↦□ gt ∗
        md.[src.gryffcommon.StoreMetadata, go!"Tag"] ↦ tp ∗
        (md.[src.gryffcommon.StoreMetadata, go!"Tag"] ↦ tp -∗
          partiOwn pa (replicaIface r) k tag ong) }} := by
  wp_start as ⟨#Hpa, Hown⟩
  wp_auto
  wp_apply GryffParticipant.GetStoreMetadata.wp_proof $$ [$Hown] as %md Hmd
  wp_end

/-- `r.GetCurrentValue(0)`: the store's value. -/
theorem wp_Replica_GetCurrentValue (r gR : Loc) (v : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ valOwn gR v }}
      (App (Val (r @!! go.GoType.PointerType src.gryff.Replica.ty @!! go!"GetCurrentValue"))
        (Val #(W64 0)))
    {{ RET #v; valOwn gR v }} := by
  wp_start as ⟨#HgR, Hv⟩
  unfold valOwn
  icases Hv with ⟨%st, %smR, %sm, #HEx, #Hst, #Hstore, Hsm, %Hsmf⟩
  wp_auto
  wp_apply wp_map_lookup1 $$ Hsm as Hsm
  rw [show zero_val w64 = W64 0 from rfl, Hsmf.2]
  wp_end
  iexists st, smR, sm
  iframe # ∗
  ipureintro; exact Hsmf

theorem model.Tag.cmp_cases (a b : model.Tag) : a.cmp b = -1 ∨ a.cmp b = 0 ∨ a.cmp b = 1 := by
  unfold model.Tag.cmp; split
  · exact .inl rfl
  · split
    · exact .inr (.inl rfl)
    · exact .inr (.inr rfl)

/-- `a.Compare(b)` (`gryffproto.Tag`). -/
theorem wp_Tag_Compare (a : Loc) (ta tb : src.gryffproto.Tag) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗ a ↦ ta }}
      (App (Val (a @!! go.GoType.PointerType src.gryffproto.Tag.ty @!! go!"Compare")) (Val #tb))
    {{ RET #(W64 (model.Tag.cmp (tagOf ta) (tagOf tb))); a ↦ ta }} := by
  wp_start as Ha
  wp_auto
  repeat' (first | wp_if_destruct | wp_auto)
  all_goals first
    | (rw [show (tagOf ta).cmp (tagOf tb) = -1 by
          (simp_all [model.Tag.cmp, tagOf, model.slt]) <;> exact decide_eq_false (by omega)]; wp_end)
    | (rw [show (tagOf ta).cmp (tagOf tb) = 0 by
          (simp_all [model.Tag.cmp, tagOf, model.slt]) <;> exact decide_eq_false (by omega)]; wp_end)
    | (rw [show (tagOf ta).cmp (tagOf tb) = 1 by
          (simp_all [model.Tag.cmp, tagOf, model.slt]) <;> exact decide_eq_false (by omega)]; wp_end)

/-- `a.GreaterThan(b)`. -/
theorem wp_Tag_GreaterThan (a : Loc) (ta tb : src.gryffproto.Tag) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗ a ↦ ta }}
      (App (Val (a @!! go.GoType.PointerType src.gryffproto.Tag.ty @!! go!"GreaterThan"))
        (Val #tb))
    {{ RET #((tagOf ta).gt (tagOf tb)); a ↦ ta }} := by
  wp_start as Ha
  wp_auto
  wp_apply wp_Tag_Compare $$ [$Ha] as Ha
  have : decide (sint.Z (W64 0) < sint.Z (W64 ((tagOf ta).cmp (tagOf tb)))) =
      (tagOf ta).gt (tagOf tb) := by
    unfold model.Tag.gt
    rcases model.Tag.cmp_cases (tagOf ta) (tagOf tb) with h | h | h <;> rw [h] <;> rfl
  rw [this]
  wp_end

end

end Perennial.gryff.replica2
