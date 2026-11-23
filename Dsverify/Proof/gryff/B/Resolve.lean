/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/B/Resolve.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit B: the trace prophecy's resolutions (`src/gryff/proph.go`): one `ResolveU64` at a time
(`replicaProph_resolve`), the helpers (`resolveTag`, `resolveValTag`, `resolveDep`, `resolveCmds`,
`resolveDeps`) and the 24 event resolutions (`resolveSpec`'s instances, `Replica2/Specs.lean`).
-/
module

public import Dsverify.Proof.gryff.Replica2.State
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Perennial.gryff.unitB

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open model model.codec replica2
open github_com.goose_lang.primitive (ProphId)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [wire.BufioSpecs GF]

/-- A `*gryff.Replica` method value (`Replica2/Specs.lean`'s `repM`). -/
abbrev repMB (r : Loc) (f : GoString) : Expr :=
  Val (r @!! go.GoType.PointerType src.gryff.Replica.ty @!! f)

/-- One `r.proph.ResolveU64(x)`. -/
theorem wp_resolveU64 (γ : ProtoNames) (k : Fin 3) (r : Loc) (p : ProphId) (t : List Ev)
    (ws : List w64) (x : w64) :
    {{ r.[src.gryff.Replica, go!"proph"] ↦□ p ∗ replicaProph γ k p t ws }}
      (App (Val (r.[src.gryff.Replica, go!"proph"] @!!
        go.PointerType github_com.goose_lang.primitive.ProphId.ty @!! go!"ResolveU64")) (Val #x))
    {{ RET #(); replicaProph γ k p t (ws ++ [x]) }} := by
  iintro %Φ ⟨#Hl, Hp⟩ HΦ
  icases replicaProph_resolve γ k p t ws $$ Hp with ⟨%pvs, Hp, Hk⟩
  wp_apply (github_com.goose_lang.primitive.ProphId.wp_ResolveU64_ptr _ DFrac.discard) $$ [Hl Hp] as
    %pvs' ⟨-, %Heq, Hp⟩
  · iframe; iframe #
  iapply HΦ
  iapply Hk $$ %x %pvs' %Heq Hp

set_option hygiene false in
/-- One `ResolveU64` step of a resolution (the prophecy hypothesis `Hp`). -/
macro "rp_step" : tactic => `(tactic| (
  try wp_auto
  wp_apply +noauto wp_resolveU64 $$ [Hp] as Hp
  · iframe; iframe #
  try wp_auto))

theorem replicaProph_congr {γ : ProtoNames} {k : Fin 3} {p : ProphId} {tr : List Ev}
    {ws ws' : List w64} (h : ws = ws') :
    replicaProph γ k p tr ws ⊢ replicaProph γ k p tr ws' := by
  rw [h]

theorem wp_resolveTag (γ : ProtoNames) (k : Fin 3) (r : Loc) (p : ProphId) (tr : List Ev)
    (ws : List w64) (l : Loc) (dq : DFrac) (g : src.gryffproto.Tag) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        r.[src.gryff.Replica, go!"proph"] ↦□ p ∗ replicaProph γ k p tr ws ∗ l ↦{dq} g }}
      (App (repMB r go!"resolveTag") (Val #l))
    {{ RET #(); replicaProph γ k p tr (ws ++ encTag (tagOf g)) ∗ l ↦{dq} g }} := by
  unfold repMB
  wp_start as ⟨#Hl, Hp, Hg⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hg
  iStructNamed Hg
  wp_auto
  rp_step
  rp_step
  rp_step
  iapply HΦ
  isplitr [Ts Cid Rmwc]
  · iapply replicaProph_congr ?_ $$ Hp
    simp [encTag, tagOf, ofI32]
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe


theorem wp_resolveValTag (γ : ProtoNames) (k : Fin 3) (r : Loc) (p : ProphId) (tr : List Ev)
    (ws : List w64) (l : Loc) (dq : DFrac) (g : src.gryffproto.ValTag) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        r.[src.gryff.Replica, go!"proph"] ↦□ p ∗ replicaProph γ k p tr ws ∗ l ↦{dq} g }}
      (App (repMB r go!"resolveValTag") (Val #l))
    {{ RET #(); replicaProph γ k p tr (ws ++ encVT (vtOf g)) ∗ l ↦{dq} g }} := by
  unfold repMB
  wp_start as ⟨#Hl, Hp, Hg⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hg
  iStructNamed Hg
  wp_auto
  rp_step
  wp_apply wp_resolveTag $$ [Hp T] as ⟨Hp, T⟩
  · iframe; iframe #
  iapply HΦ
  isplitr [V T]
  · iapply replicaProph_congr ?_ $$ Hp
    simp [encVT, encTag, vtOf, tagOf, ofI32]
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

theorem wp_resolveDep (γ : ProtoNames) (k : Fin 3) (r : Loc) (p : ProphId) (tr : List Ev)
    (ws : List w64) (l : Loc) (dq : DFrac) (g : src.gryffproto.Dep) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        r.[src.gryff.Replica, go!"proph"] ↦□ p ∗ replicaProph γ k p tr ws ∗ l ↦{dq} g }}
      (App (repMB r go!"resolveDep") (Val #l))
    {{ RET #(); replicaProph γ k p tr (ws ++ encDep (depOf g)) ∗ l ↦{dq} g }} := by
  unfold repMB
  wp_start as ⟨#Hl, Hp, Hg⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hg
  iStructNamed Hg
  wp_auto
  rp_step
  wp_apply wp_resolveValTag $$ [Hp Vt] as ⟨Hp, Vt⟩
  · iframe; iframe #
  iapply HΦ
  isplitr [Key Vt]
  · iapply replicaProph_congr ?_ $$ Hp
    simp [encDep, depOf]
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

theorem wp_resolveRead1_g (γ : ProtoNames) (k : Fin 3) (r : Loc) (p : ProphId) (tr : List Ev)
    (ws : List w64) (l : Loc) (dq : DFrac) (g : src.gryffproto.Read1Proxied) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        r.[src.gryff.Replica, go!"proph"] ↦□ p ∗ replicaProph γ k p tr ws ∗ l ↦{dq} g }}
      (App (repMB r go!"resolveRead1") (Val #l))
    {{ RET #(); replicaProph γ k p tr (ws ++ encEv (.msg (.read1 (read1Of g)))) ∗ l ↦{dq} g }} := by
  unfold repMB
  wp_start as ⟨#Hl, Hp, Hg⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hg
  iStructNamed Hg
  wp_auto
  rp_step
  rp_step
  rp_step
  rp_step
  wp_apply wp_resolveDep $$ [Hp D] as ⟨Hp, D⟩
  · iframe; iframe #
  rp_step
  wp_apply wp_resolveValTag $$ [Hp Vt] as ⟨Hp, Vt⟩
  · iframe; iframe #
  iapply HΦ
  isplitl [Hp]
  · iapply replicaProph_congr ?_ $$ Hp
    simp [encEv, encRead1, read1Of, ofI32]
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe


/-- `Replica2/Specs.lean`'s `resolveSpec` (a resolution resolves the words of `e`). -/
def resolveSpecB (γ : GryffNames GF) (k : Fin 3) (r : Loc) (call : Expr)
    (Pre : IProp GF) (e : Ev) : Prop :=
  ∀ (p : ProphId) (t : List Ev) (ws : List w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        r.[src.gryff.Replica, go!"proph"] ↦□ p ∗ replicaProph γ.proto k p t ws ∗ Pre }}
      call
    {{ RET #(); replicaProph γ.proto k p t (ws ++ model.evCodec.enc e) ∗ Pre }}

theorem resolveRead1_proof (γ : GryffNames GF) (k : Fin 3) (r p : Loc)
    (m : model.Read1ProxiedM) :
    resolveSpecB γ k r (App (repMB r go!"resolveRead1") (Val #p)) (msgAt p (.read1 m))
      (.msg (.read1 m)) := by
  intro pr tr ws
  iintro %Φ ⟨#Hpkg, #Hl, Hp, Hm⟩ HΦ
  unfold msgAt
  icases Hm with ⟨%g, Hg, %Hgm⟩
  wp_apply wp_resolveRead1_g $$ [Hp Hg] as ⟨Hp, Hg⟩
  · iframe; iframe #
  iapply HΦ
  subst Hgm
  iframe
  iexists g
  iframe
  ipureintro; rfl


theorem wp_resolveRead2_g (γ : ProtoNames) (k : Fin 3) (r : Loc) (p : ProphId) (tr : List Ev)
    (ws : List w64) (l : Loc) (dq : DFrac) (g : src.gryffproto.Read2Proxied) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        r.[src.gryff.Replica, go!"proph"] ↦□ p ∗ replicaProph γ k p tr ws ∗ l ↦{dq} g }}
      (App (repMB r go!"resolveRead2") (Val #l))
    {{ RET #(); replicaProph γ k p tr (ws ++ encEv (.msg (.read2 (read2Of g)))) ∗ l ↦{dq} g }} := by
  unfold repMB
  wp_start as ⟨#Hl, Hp, Hg⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hg
  iStructNamed Hg
  wp_auto
  rp_step
  rp_step
  rp_step
  rp_step
  wp_apply wp_resolveValTag $$ [Hp Vt] as ⟨Hp, Vt⟩
  · iframe; iframe #
  rp_step
  iapply HΦ
  isplitl [Hp]
  · iapply replicaProph_congr ?_ $$ Hp
    simp [encEv, encRead2, read2Of, ofI32, ofU8, ofI8, encVT, encTag, encDep, vtOf, tagOf, depOf]
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

theorem resolveRead2_proof (γ : GryffNames GF) (k : Fin 3) (r p : Loc)
    (m : model.Read2ProxiedM) :
    resolveSpecB γ k r (App (repMB r go!"resolveRead2") (Val #p)) (msgAt p (.read2 m))
      (.msg (.read2 m)) := by
  intro pr tr ws
  iintro %Φ ⟨#Hpkg, #Hl, Hp, Hm⟩ HΦ
  unfold msgAt
  icases Hm with ⟨%g, Hg, %Hgm⟩
  wp_apply wp_resolveRead2_g $$ [Hp Hg] as ⟨Hp, Hg⟩
  · iframe; iframe #
  iapply HΦ
  subst Hgm
  iframe
  iexists g
  iframe
  ipureintro; rfl

theorem wp_resolveRead1Reply_g (γ : ProtoNames) (k : Fin 3) (r : Loc) (p : ProphId) (tr : List Ev)
    (ws : List w64) (l : Loc) (dq : DFrac) (g : src.gryffproto.Read1Reply) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        r.[src.gryff.Replica, go!"proph"] ↦□ p ∗ replicaProph γ k p tr ws ∗ l ↦{dq} g }}
      (App (repMB r go!"resolveRead1Reply") (Val #l))
    {{ RET #(); replicaProph γ k p tr (ws ++ encEv (.msg (.read1Reply (read1ReplyOf g)))) ∗ l ↦{dq} g }} := by
  unfold repMB
  wp_start as ⟨#Hl, Hp, Hg⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hg
  iStructNamed Hg
  wp_auto
  rp_step
  rp_step
  rp_step
  rp_step
  wp_apply wp_resolveValTag $$ [Hp Vt] as ⟨Hp, Vt⟩
  · iframe; iframe #
  iapply HΦ
  isplitl [Hp]
  · iapply replicaProph_congr ?_ $$ Hp
    simp [encEv, encRead1Reply, read1ReplyOf, ofI32, ofU8, ofI8, encVT, encTag, encDep, vtOf, tagOf, depOf]
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

theorem resolveRead1Reply_proof (γ : GryffNames GF) (k : Fin 3) (r p : Loc)
    (m : model.Read1ReplyM) :
    resolveSpecB γ k r (App (repMB r go!"resolveRead1Reply") (Val #p)) (msgAt p (.read1Reply m))
      (.msg (.read1Reply m)) := by
  intro pr tr ws
  iintro %Φ ⟨#Hpkg, #Hl, Hp, Hm⟩ HΦ
  unfold msgAt
  icases Hm with ⟨%g, Hg, %Hgm⟩
  wp_apply wp_resolveRead1Reply_g $$ [Hp Hg] as ⟨Hp, Hg⟩
  · iframe; iframe #
  iapply HΦ
  subst Hgm
  iframe
  iexists g
  iframe
  ipureintro; rfl

theorem wp_resolveRead2Reply_g (γ : ProtoNames) (k : Fin 3) (r : Loc) (p : ProphId) (tr : List Ev)
    (ws : List w64) (l : Loc) (dq : DFrac) (g : src.gryffproto.Read2Reply) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        r.[src.gryff.Replica, go!"proph"] ↦□ p ∗ replicaProph γ k p tr ws ∗ l ↦{dq} g }}
      (App (repMB r go!"resolveRead2Reply") (Val #l))
    {{ RET #(); replicaProph γ k p tr (ws ++ encEv (.msg (.read2Reply (read2ReplyOf g)))) ∗ l ↦{dq} g }} := by
  unfold repMB
  wp_start as ⟨#Hl, Hp, Hg⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hg
  iStructNamed Hg
  wp_auto
  rp_step
  rp_step
  rp_step
  iapply HΦ
  isplitl [Hp]
  · iapply replicaProph_congr ?_ $$ Hp
    simp [encEv, encRead2Reply, read2ReplyOf, ofI32, ofU8, ofI8, encVT, encTag, encDep, vtOf, tagOf, depOf]
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

theorem resolveRead2Reply_proof (γ : GryffNames GF) (k : Fin 3) (r p : Loc)
    (m : model.Read2ReplyM) :
    resolveSpecB γ k r (App (repMB r go!"resolveRead2Reply") (Val #p)) (msgAt p (.read2Reply m))
      (.msg (.read2Reply m)) := by
  intro pr tr ws
  iintro %Φ ⟨#Hpkg, #Hl, Hp, Hm⟩ HΦ
  unfold msgAt
  icases Hm with ⟨%g, Hg, %Hgm⟩
  wp_apply wp_resolveRead2Reply_g $$ [Hp Hg] as ⟨Hp, Hg⟩
  · iframe; iframe #
  iapply HΦ
  subst Hgm
  iframe
  iexists g
  iframe
  ipureintro; rfl

theorem wp_resolveWrite1_g (γ : ProtoNames) (k : Fin 3) (r : Loc) (p : ProphId) (tr : List Ev)
    (ws : List w64) (l : Loc) (dq : DFrac) (g : src.gryffproto.Write1Proxied) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        r.[src.gryff.Replica, go!"proph"] ↦□ p ∗ replicaProph γ k p tr ws ∗ l ↦{dq} g }}
      (App (repMB r go!"resolveWrite1") (Val #l))
    {{ RET #(); replicaProph γ k p tr (ws ++ encEv (.msg (.write1 (write1Of g)))) ∗ l ↦{dq} g }} := by
  unfold repMB
  wp_start as ⟨#Hl, Hp, Hg⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hg
  iStructNamed Hg
  wp_auto
  rp_step
  rp_step
  rp_step
  rp_step
  rp_step
  wp_apply wp_resolveDep $$ [Hp D] as ⟨Hp, D⟩
  · iframe; iframe #
  rp_step
  iapply HΦ
  isplitl [Hp]
  · iapply replicaProph_congr ?_ $$ Hp
    simp [encEv, encWrite1, write1Of, ofI32, ofU8, ofI8, encVT, encTag, encDep, vtOf, tagOf, depOf]
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

theorem resolveWrite1_proof (γ : GryffNames GF) (k : Fin 3) (r p : Loc)
    (m : model.Write1ProxiedM) :
    resolveSpecB γ k r (App (repMB r go!"resolveWrite1") (Val #p)) (msgAt p (.write1 m))
      (.msg (.write1 m)) := by
  intro pr tr ws
  iintro %Φ ⟨#Hpkg, #Hl, Hp, Hm⟩ HΦ
  unfold msgAt
  icases Hm with ⟨%g, Hg, %Hgm⟩
  wp_apply wp_resolveWrite1_g $$ [Hp Hg] as ⟨Hp, Hg⟩
  · iframe; iframe #
  iapply HΦ
  subst Hgm
  iframe
  iexists g
  iframe
  ipureintro; rfl

theorem wp_resolveWrite2_g (γ : ProtoNames) (k : Fin 3) (r : Loc) (p : ProphId) (tr : List Ev)
    (ws : List w64) (l : Loc) (dq : DFrac) (g : src.gryffproto.Write2Proxied) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        r.[src.gryff.Replica, go!"proph"] ↦□ p ∗ replicaProph γ k p tr ws ∗ l ↦{dq} g }}
      (App (repMB r go!"resolveWrite2") (Val #l))
    {{ RET #(); replicaProph γ k p tr (ws ++ encEv (.msg (.write2 (write2Of g)))) ∗ l ↦{dq} g }} := by
  unfold repMB
  wp_start as ⟨#Hl, Hp, Hg⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hg
  iStructNamed Hg
  wp_auto
  rp_step
  rp_step
  rp_step
  rp_step
  wp_apply wp_resolveValTag $$ [Hp Vt] as ⟨Hp, Vt⟩
  · iframe; iframe #
  rp_step
  iapply HΦ
  isplitl [Hp]
  · iapply replicaProph_congr ?_ $$ Hp
    simp [encEv, encWrite2, write2Of, ofI32, ofU8, ofI8, encVT, encTag, encDep, vtOf, tagOf, depOf]
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

theorem resolveWrite2_proof (γ : GryffNames GF) (k : Fin 3) (r p : Loc)
    (m : model.Write2ProxiedM) :
    resolveSpecB γ k r (App (repMB r go!"resolveWrite2") (Val #p)) (msgAt p (.write2 m))
      (.msg (.write2 m)) := by
  intro pr tr ws
  iintro %Φ ⟨#Hpkg, #Hl, Hp, Hm⟩ HΦ
  unfold msgAt
  icases Hm with ⟨%g, Hg, %Hgm⟩
  wp_apply wp_resolveWrite2_g $$ [Hp Hg] as ⟨Hp, Hg⟩
  · iframe; iframe #
  iapply HΦ
  subst Hgm
  iframe
  iexists g
  iframe
  ipureintro; rfl

theorem wp_resolveWrite1Reply_g (γ : ProtoNames) (k : Fin 3) (r : Loc) (p : ProphId) (tr : List Ev)
    (ws : List w64) (l : Loc) (dq : DFrac) (g : src.gryffproto.Write1Reply) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        r.[src.gryff.Replica, go!"proph"] ↦□ p ∗ replicaProph γ k p tr ws ∗ l ↦{dq} g }}
      (App (repMB r go!"resolveWrite1Reply") (Val #l))
    {{ RET #(); replicaProph γ k p tr (ws ++ encEv (.msg (.write1Reply (write1ReplyOf g)))) ∗ l ↦{dq} g }} := by
  unfold repMB
  wp_start as ⟨#Hl, Hp, Hg⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hg
  iStructNamed Hg
  wp_auto
  rp_step
  rp_step
  rp_step
  wp_apply wp_resolveValTag $$ [Hp Vt] as ⟨Hp, Vt⟩
  · iframe; iframe #
  iapply HΦ
  isplitl [Hp]
  · iapply replicaProph_congr ?_ $$ Hp
    simp [encEv, encWrite1Reply, write1ReplyOf, ofI32, ofU8, ofI8, encVT, encTag, encDep, vtOf, tagOf, depOf]
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

theorem resolveWrite1Reply_proof (γ : GryffNames GF) (k : Fin 3) (r p : Loc)
    (m : model.Write1ReplyM) :
    resolveSpecB γ k r (App (repMB r go!"resolveWrite1Reply") (Val #p)) (msgAt p (.write1Reply m))
      (.msg (.write1Reply m)) := by
  intro pr tr ws
  iintro %Φ ⟨#Hpkg, #Hl, Hp, Hm⟩ HΦ
  unfold msgAt
  icases Hm with ⟨%g, Hg, %Hgm⟩
  wp_apply wp_resolveWrite1Reply_g $$ [Hp Hg] as ⟨Hp, Hg⟩
  · iframe; iframe #
  iapply HΦ
  subst Hgm
  iframe
  iexists g
  iframe
  ipureintro; rfl

theorem wp_resolveWrite2Reply_g (γ : ProtoNames) (k : Fin 3) (r : Loc) (p : ProphId) (tr : List Ev)
    (ws : List w64) (l : Loc) (dq : DFrac) (g : src.gryffproto.Write2Reply) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        r.[src.gryff.Replica, go!"proph"] ↦□ p ∗ replicaProph γ k p tr ws ∗ l ↦{dq} g }}
      (App (repMB r go!"resolveWrite2Reply") (Val #l))
    {{ RET #(); replicaProph γ k p tr (ws ++ encEv (.msg (.write2Reply (write2ReplyOf g)))) ∗ l ↦{dq} g }} := by
  unfold repMB
  wp_start as ⟨#Hl, Hp, Hg⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hg
  iStructNamed Hg
  wp_auto
  rp_step
  rp_step
  rp_step
  rp_step
  iapply HΦ
  isplitl [Hp]
  · iapply replicaProph_congr ?_ $$ Hp
    simp [encEv, encWrite2Reply, write2ReplyOf, ofI32, ofU8, ofI8, encVT, encTag, encDep, vtOf, tagOf, depOf]
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

theorem resolveWrite2Reply_proof (γ : GryffNames GF) (k : Fin 3) (r p : Loc)
    (m : model.Write2ReplyM) :
    resolveSpecB γ k r (App (repMB r go!"resolveWrite2Reply") (Val #p)) (msgAt p (.write2Reply m))
      (.msg (.write2Reply m)) := by
  intro pr tr ws
  iintro %Φ ⟨#Hpkg, #Hl, Hp, Hm⟩ HΦ
  unfold msgAt
  icases Hm with ⟨%g, Hg, %Hgm⟩
  wp_apply wp_resolveWrite2Reply_g $$ [Hp Hg] as ⟨Hp, Hg⟩
  · iframe; iframe #
  iapply HΦ
  subst Hgm
  iframe
  iexists g
  iframe
  ipureintro; rfl

theorem wp_resolvePreAcceptOK_g (γ : ProtoNames) (k : Fin 3) (r : Loc) (p : ProphId) (tr : List Ev)
    (ws : List w64) (l : Loc) (dq : DFrac) (g : src.epaxosproto.PreAcceptOK) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        r.[src.gryff.Replica, go!"proph"] ↦□ p ∗ replicaProph γ k p tr ws ∗ l ↦{dq} g }}
      (App (repMB r go!"resolvePreAcceptOK") (Val #l))
    {{ RET #(); replicaProph γ k p tr (ws ++ encEv (.msg (.preAcceptOK (preAcceptOKOf g)))) ∗ l ↦{dq} g }} := by
  unfold repMB
  wp_start as ⟨#Hl, Hp, Hg⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hg
  iStructNamed Hg
  wp_auto
  rp_step
  rp_step
  iapply HΦ
  isplitl [Hp]
  · iapply replicaProph_congr ?_ $$ Hp
    simp [encEv, encPreAcceptOK, preAcceptOKOf, ofI32, ofU8, ofI8, encVT, encTag, encDep, vtOf, tagOf, depOf]
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

theorem resolvePreAcceptOK_proof (γ : GryffNames GF) (k : Fin 3) (r p : Loc)
    (m : model.PreAcceptOKM) :
    resolveSpecB γ k r (App (repMB r go!"resolvePreAcceptOK") (Val #p)) (msgAt p (.preAcceptOK m))
      (.msg (.preAcceptOK m)) := by
  intro pr tr ws
  iintro %Φ ⟨#Hpkg, #Hl, Hp, Hm⟩ HΦ
  unfold msgAt
  icases Hm with ⟨%g, Hg, %Hgm⟩
  wp_apply wp_resolvePreAcceptOK_g $$ [Hp Hg] as ⟨Hp, Hg⟩
  · iframe; iframe #
  iapply HΦ
  subst Hgm
  iframe
  iexists g
  iframe
  ipureintro; rfl

theorem wp_resolveAcceptReply_g (γ : ProtoNames) (k : Fin 3) (r : Loc) (p : ProphId) (tr : List Ev)
    (ws : List w64) (l : Loc) (dq : DFrac) (g : src.epaxosproto.AcceptReply) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        r.[src.gryff.Replica, go!"proph"] ↦□ p ∗ replicaProph γ k p tr ws ∗ l ↦{dq} g }}
      (App (repMB r go!"resolveAcceptReply") (Val #l))
    {{ RET #(); replicaProph γ k p tr (ws ++ encEv (.msg (.acceptReply (acceptReplyOf g)))) ∗ l ↦{dq} g }} := by
  unfold repMB
  wp_start as ⟨#Hl, Hp, Hg⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hg
  iStructNamed Hg
  wp_auto
  rp_step
  rp_step
  rp_step
  rp_step
  rp_step
  iapply HΦ
  isplitl [Hp]
  · iapply replicaProph_congr ?_ $$ Hp
    simp [encEv, encAcceptReply, acceptReplyOf, ofI32, ofU8, ofI8, encVT, encTag, encDep, vtOf, tagOf, depOf]
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

theorem resolveAcceptReply_proof (γ : GryffNames GF) (k : Fin 3) (r p : Loc)
    (m : model.AcceptReplyM) :
    resolveSpecB γ k r (App (repMB r go!"resolveAcceptReply") (Val #p)) (msgAt p (.acceptReply m))
      (.msg (.acceptReply m)) := by
  intro pr tr ws
  iintro %Φ ⟨#Hpkg, #Hl, Hp, Hm⟩ HΦ
  unfold msgAt
  icases Hm with ⟨%g, Hg, %Hgm⟩
  wp_apply wp_resolveAcceptReply_g $$ [Hp Hg] as ⟨Hp, Hg⟩
  · iframe; iframe #
  iapply HΦ
  subst Hgm
  iframe
  iexists g
  iframe
  ipureintro; rfl

theorem wp_resolvePrepare_g (γ : ProtoNames) (k : Fin 3) (r : Loc) (p : ProphId) (tr : List Ev)
    (ws : List w64) (l : Loc) (dq : DFrac) (g : src.epaxosproto.Prepare) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        r.[src.gryff.Replica, go!"proph"] ↦□ p ∗ replicaProph γ k p tr ws ∗ l ↦{dq} g }}
      (App (repMB r go!"resolvePrepare") (Val #l))
    {{ RET #(); replicaProph γ k p tr (ws ++ encEv (.msg (.prepare (prepareOf g)))) ∗ l ↦{dq} g }} := by
  unfold repMB
  wp_start as ⟨#Hl, Hp, Hg⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hg
  iStructNamed Hg
  wp_auto
  rp_step
  rp_step
  rp_step
  rp_step
  rp_step
  iapply HΦ
  isplitl [Hp]
  · iapply replicaProph_congr ?_ $$ Hp
    simp [encEv, encPrepare, prepareOf, ofI32, ofU8, ofI8, encVT, encTag, encDep, vtOf, tagOf, depOf]
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

theorem resolvePrepare_proof (γ : GryffNames GF) (k : Fin 3) (r p : Loc)
    (m : model.PrepareM) :
    resolveSpecB γ k r (App (repMB r go!"resolvePrepare") (Val #p)) (msgAt p (.prepare m))
      (.msg (.prepare m)) := by
  intro pr tr ws
  iintro %Φ ⟨#Hpkg, #Hl, Hp, Hm⟩ HΦ
  unfold msgAt
  icases Hm with ⟨%g, Hg, %Hgm⟩
  wp_apply wp_resolvePrepare_g $$ [Hp Hg] as ⟨Hp, Hg⟩
  · iframe; iframe #
  iapply HΦ
  subst Hgm
  iframe
  iexists g
  iframe
  ipureintro; rfl

theorem wp_resolveExecuted_g (γ : ProtoNames) (k : Fin 3) (r : Loc) (p : ProphId) (tr : List Ev)
    (ws : List w64) (l : Loc) (dq : DFrac) (g : src.gryffproto.Executed) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        r.[src.gryff.Replica, go!"proph"] ↦□ p ∗ replicaProph γ k p tr ws ∗ l ↦{dq} g }}
      (App (repMB r go!"resolveExecuted") (Val #l))
    {{ RET #(); replicaProph γ k p tr (ws ++ encEv (.msg (.executed (executedOf g)))) ∗ l ↦{dq} g }} := by
  unfold repMB
  wp_start as ⟨#Hl, Hp, Hg⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hg
  iStructNamed Hg
  wp_auto
  rp_step
  rp_step
  rp_step
  iapply HΦ
  isplitl [Hp]
  · iapply replicaProph_congr ?_ $$ Hp
    simp [encEv, encExecuted, executedOf, ofI32, ofU8, ofI8, encVT, encTag, encDep, vtOf, tagOf, depOf]
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

theorem resolveExecuted_proof (γ : GryffNames GF) (k : Fin 3) (r p : Loc)
    (m : model.ExecutedM) :
    resolveSpecB γ k r (App (repMB r go!"resolveExecuted") (Val #p)) (msgAt p (.executed m))
      (.msg (.executed m)) := by
  intro pr tr ws
  iintro %Φ ⟨#Hpkg, #Hl, Hp, Hm⟩ HΦ
  unfold msgAt
  icases Hm with ⟨%g, Hg, %Hgm⟩
  wp_apply wp_resolveExecuted_g $$ [Hp Hg] as ⟨Hp, Hg⟩
  · iframe; iframe #
  iapply HΦ
  subst Hgm
  iframe
  iexists g
  iframe
  ipureintro; rfl



theorem resolveRead_proof (γ : GryffNames GF) (k : Fin 3) (r l : Loc) (g : src.gryffproto.Read) :
    resolveSpecB γ k r (App (repMB r go!"resolveRead") (Val #l)) iprop(l ↦ g) (readEvOf g) := by
  intro p tr ws
  unfold repMB
  wp_start as ⟨#Hl, Hp, Hg⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hg
  iStructNamed Hg
  wp_auto
  rp_step
  rp_step
  rp_step
  rp_step
  try wp_auto
  wp_apply +noauto wp_resolveDep $$ [Hp D] as ⟨Hp, D⟩
  · iframe; iframe #
  try wp_auto
  iapply HΦ
  isplitl [Hp]
  · iapply replicaProph_congr ?_ $$ Hp
    simp [evCodec, encEv, readEvOf, ofI32, ofU8, ofI8, encVT, encTag, encDep, vtOf, tagOf, depOf]
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

theorem resolveWrite_proof (γ : GryffNames GF) (k : Fin 3) (r l : Loc) (g : src.gryffproto.Write) :
    resolveSpecB γ k r (App (repMB r go!"resolveWrite") (Val #l)) iprop(l ↦ g) (writeEvOf g) := by
  intro p tr ws
  unfold repMB
  wp_start as ⟨#Hl, Hp, Hg⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hg
  iStructNamed Hg
  wp_auto
  rp_step
  rp_step
  rp_step
  rp_step
  rp_step
  try wp_auto
  wp_apply +noauto wp_resolveDep $$ [Hp D] as ⟨Hp, D⟩
  · iframe; iframe #
  try wp_auto
  iapply HΦ
  isplitl [Hp]
  · iapply replicaProph_congr ?_ $$ Hp
    simp [evCodec, encEv, writeEvOf, ofI32, ofU8, ofI8, encVT, encTag, encDep, vtOf, tagOf, depOf]
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

theorem resolveRMW_proof (γ : GryffNames GF) (k : Fin 3) (r l : Loc) (g : src.gryffproto.RMW) :
    resolveSpecB γ k r (App (repMB r go!"resolveRMW") (Val #l)) iprop(l ↦ g) (rmwEvOf g) := by
  intro p tr ws
  unfold repMB
  wp_start as ⟨#Hl, Hp, Hg⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hg
  iStructNamed Hg
  wp_auto
  rp_step
  rp_step
  rp_step
  rp_step
  try wp_auto
  wp_apply +noauto wp_resolveDep $$ [Hp D] as ⟨Hp, D⟩
  · iframe; iframe #
  rp_step
  rp_step
  try wp_auto
  iapply HΦ
  isplitl [Hp]
  · iapply replicaProph_congr ?_ $$ Hp
    simp [evCodec, encEv, rmwEvOf, ofI32, ofU8, ofI8, encVT, encTag, encDep, vtOf, tagOf, depOf]
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

theorem resolveForceWrite_proof (γ : GryffNames GF) (k : Fin 3) (r : Loc) :
    resolveSpecB γ k r (App (repMB r go!"resolveForceWrite") (Val #())) iprop(True) .forceWrite := by
  intro p tr ws
  unfold repMB
  wp_start as ⟨#Hl, Hp, -⟩
  wp_auto
  rp_step
  try wp_auto
  iapply HΦ
  isplitl [Hp]
  · iapply replicaProph_congr ?_ $$ Hp
    simp [evCodec, encEv]
  itrivial

theorem resolveRecover_proof (γ : GryffNames GF) (k : Fin 3) (r : Loc) (q i : w32) :
    resolveSpecB γ k r (App (App (repMB r go!"resolveRecover") (Val #q)) (Val #i)) iprop(True)
      (.recover q i) := by
  intro p tr ws
  unfold repMB
  wp_start as ⟨#Hl, Hp, -⟩
  wp_auto
  rp_step
  rp_step
  rp_step
  try wp_auto
  iapply HΦ
  isplitl [Hp]
  · iapply replicaProph_congr ?_ $$ Hp
    simp [evCodec, encEv, ofI32]
  itrivial

theorem resolveExec_proof (γ : GryffNames GF) (k : Fin 3) (r : Loc) (q i : w32) :
    resolveSpecB γ k r (App (App (repMB r go!"resolveExec") (Val #q)) (Val #i)) iprop(True)
      (.exec q i) := by
  intro p tr ws
  unfold repMB
  wp_start as ⟨#Hl, Hp, -⟩
  wp_auto
  rp_step
  rp_step
  rp_step
  try wp_auto
  iapply HΦ
  isplitl [Hp]
  · iapply replicaProph_congr ?_ $$ Hp
    simp [evCodec, encEv, ofI32]
  itrivial

theorem resolveExecuteOverwrite_proof (γ : GryffNames GF) (k : Fin 3) (r l : Loc)
    (m : model.ExecuteOverwriteM) :
    resolveSpecB γ k r (App (repMB r go!"resolveExecuteOverwrite") (Val #l))
      (msgAt l (.executeOverwrite m)) (.msg (.executeOverwrite m)) := by
  intro p tr ws
  unfold repMB
  unfold msgAt
  wp_start as ⟨#Hl, Hp, ⟨%eo, %tg, Hg, #HT, %Heo⟩⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hg
  iStructNamed Hg
  wp_auto
  rp_step
  rp_step
  try wp_auto
  wp_apply +noauto wp_resolveTag $$ [Hp] as ⟨Hp, -⟩
  · iframe; iframe #
  rp_step
  rp_step
  try wp_auto
  iapply HΦ
  isplitl [Hp]
  · iapply replicaProph_congr ?_ $$ Hp
    obtain ⟨-, rfl⟩ := Heo
    simp [evCodec, encEv, encExecuteOverwrite, ofI32, encTag, tagOf]
  iexists eo, tg
  iframe #
  isplitl
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  ipureintro; exact Heo




theorem encList_flat {α : Type} (f : α → List w64) (l : List α) :
    encList f l = l.flatMap (fun a => 1 :: f a) ++ [0] := by
  induction l with
  | nil => rfl
  | cons a xs ih => simp [encList, ih]

theorem list_set_self {α : Type} (l : List α) (i : Nat) (x : α) (h : l[i]? = some x) :
    l.set i x = l := by
  induction l generalizing i with
  | nil => simp at h
  | cons a t ih =>
    cases i with
    | zero => simp at h; simp [h]
    | succ n => simp at h; simp [ih n h]

theorem take_succ_of_get {α : Type} (l : List α) (i : Nat) (x : α) (h : l[i]? = some x) :
    l.take (i + 1) = l.take i ++ [x] := by
  rw [List.take_add_one, h]; rfl

theorem wp_resolveDeps (γ : ProtoNames) (k : Fin 3) (r : Loc) (p : ProphId) (tr : List Ev)
    (ws : List w64) (a : GoArray w32 5) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        r.[src.gryff.Replica, go!"proph"] ↦□ p ∗ replicaProph γ k p tr ws }}
      (App (repMB r go!"resolveDeps") (Val #a))
    {{ RET #(); replicaProph γ k p tr (ws ++ encDeps a.arr) }} := by
  rcases a with ⟨arr⟩
  unfold repMB
  wp_start as ⟨#Hl, Hp⟩
  wp_auto
  ihave %Hlen := array_len _ _ _ _ $$ deps
  ihave HI : (∃ iv : w64, "i" ∷ i_ptr ↦ iv ∗
      "Hp" ∷ replicaProph γ k p tr (ws ++ (arr.take (sint.nat iv)).flatMap (fun x => [1, ofI32 x])) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z iv ∧ sint.Z iv ≤ 5⌝ : IProp GF) $$ [i Hp]
  · iexists W64 0
    iframe
    isplitl
    · iapply replicaProph_congr ?_ $$ Hp
      rw [show sint.nat (W64 0) = 0 from rfl]
      simp
    ipureintro; decide
  wp_for HI
  wp_if_destruct
  · have hc : sint.Z iv < 5 := by word
    rp_step
    have hlt : sint.nat iv < arr.length := by word
    list_elem arr (sint.nat iv) as x
    icases array_acc deps_ptr (sint.Z iv) _ 5 ⟨arr⟩ x (by word) (by simpa using Hx_lookup) $$ deps
      with ⟨He, Hback⟩
    rw [if_pos ⟨Hi.1, hc⟩]
    wp_auto
    rp_step
    have hn : sint.nat iv = (sint.Z iv).toNat := rfl
    have hset : arr.set (sint.Z iv).toNat x = arr := list_set_self _ _ _ (by rw [← hn]; exact Hx_lookup)
    ihave deps := Hback $$ %x He
    isimp [hset] at deps
    wp_for_post
    iframe
    iexists iv + W64 1
    iframe
    isplitl
    · iapply replicaProph_congr ?_ $$ Hp
      rw [show sint.nat (iv + W64 1) = sint.nat iv + 1 by word, take_succ_of_get _ _ _ Hx_lookup]
      simp [ofI32]
    ipureintro; word
  · rp_step
    try wp_auto
    iapply HΦ
    iapply replicaProph_congr ?_ $$ Hp
    have h5 : sint.nat iv = arr.length := by word
    rw [h5, List.take_length, encDeps, encList_flat]
    simp


theorem wp_resolveCmds (γ : ProtoNames) (k : Fin 3) (r : Loc) (p : ProphId) (tr : List Ev)
    (ws : List w64) (sl : GoSlice) (dq : DFrac) (cs : List src.state.Command) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        r.[src.gryff.Replica, go!"proph"] ↦□ p ∗ replicaProph γ k p tr ws ∗ sl ↦*{dq} cs }}
      (App (repMB r go!"resolveCmds") (Val #sl))
    {{ RET #(); replicaProph γ k p tr (ws ++ encCmds (cs.map cmdOf)) ∗ sl ↦*{dq} cs }} := by
  unfold repMB
  wp_start as ⟨#Hl, Hp, Hsl⟩
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave HI : (∃ iv : w64, "i" ∷ i_ptr ↦ iv ∗
      "Hp" ∷ replicaProph γ k p tr
        (ws ++ ((cs.take (sint.nat iv)).map cmdOf).flatMap (fun c => 1 :: encCmd c)) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z iv ∧ sint.Z iv ≤ sint.Z sl.len⌝ : IProp GF) $$ [i Hp]
  · iexists W64 0
    iframe
    isplitl
    · iapply replicaProph_congr ?_ $$ Hp
      rw [show sint.nat (W64 0) = 0 from rfl]
      simp
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · rp_step
    list_elem cs (sint.nat iv) as c
    have hn : sint.nat iv = (sint.Z iv).toNat := rfl
    icases ownSlice_elem_acc (sint.Z iv) c sl dq cs Hi.1 (by rw [← hn]; exact Hc_lookup) $$ Hsl
      with ⟨He, Hback⟩
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ He
    iStructNamed He
    simp only [Hi.1, Hif, and_self, ↓reduceIte]
    wp_auto
    rp_step
    simp only [Hi.1, Hif, and_self, ↓reduceIte]
    rp_step
    simp only [Hi.1, Hif, and_self, ↓reduceIte]
    rp_step
    simp only [Hi.1, Hif, and_self, ↓reduceIte]
    rp_step
    ihave He : typedPointsto (sliceIndexRef src.state.Command (sint.Z iv) sl) c dq $$ [Op K V OldValue]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave Hsl := Hback $$ %c He
    have hset : cs.set (sint.Z iv).toNat c = cs := list_set_self _ _ _ (by rw [← hn]; exact Hc_lookup)
    isimp [hset] at Hsl
    wp_for_post
    iframe
    iexists iv + W64 1
    iframe
    isplitl
    · iapply replicaProph_congr ?_ $$ Hp
      rw [show sint.nat (iv + W64 1) = sint.nat iv + 1 by word, take_succ_of_get _ _ _ Hc_lookup]
      simp [encCmd, cmdOf, ofU8]
    ipureintro; word
  · rp_step
    try wp_auto
    iapply HΦ
    iframe
    iapply replicaProph_congr ?_ $$ Hp
    have h5 : sint.nat iv = cs.length := by word
    rw [h5, List.take_length, encCmds, encList_flat]
    simp


theorem wp_resolvePreAccept_g (γ : ProtoNames) (k : Fin 3) (r : Loc) (p : ProphId) (tr : List Ev)
    (ws : List w64) (l : Loc) (dq dqs : DFrac) (g : wire.gryffproto.PreAccept.Msg) (s : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        r.[src.gryff.Replica, go!"proph"] ↦□ p ∗ replicaProph γ k p tr ws ∗
        l ↦{dq} wire.gryffproto.PreAccept.goVal g s ∗ s ↦*{dqs} g.Command }}
      (App (repMB r go!"resolvePreAccept") (Val #l))
    {{ RET #(); replicaProph γ k p tr (ws ++ encEv (.msg (.preAccept (preAcceptOf g)))) ∗
        l ↦{dq} wire.gryffproto.PreAccept.goVal g s ∗ s ↦*{dqs} g.Command }} := by
  unfold repMB
  wp_start as ⟨#Hl, Hp, Hg, Hcs⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hg
  iStructNamed Hg
  simp only [wire.gryffproto.PreAccept.goVal]
  wp_auto
  rp_step
  rp_step
  rp_step
  rp_step
  rp_step
  try wp_auto
  wp_apply +noauto wp_resolveCmds $$ [Hp Hcs] as ⟨Hp, Hcs⟩
  · iframe; iframe #
  rp_step
  try wp_auto
  wp_apply +noauto wp_resolveDeps $$ [Hp] as Hp
  · iframe; iframe #
  try wp_auto
  wp_apply +noauto wp_resolveValTag $$ [Hp Base] as ⟨Hp, Base⟩
  · iframe; iframe #
  try wp_auto
  iapply HΦ
  isplitl [Hp]
  · iapply replicaProph_congr ?_ $$ Hp
    simp [evCodec, encEv, encPreAccept, preAcceptOf, ofI32, ofU8, ofI8, encVT, encTag, vtOf, tagOf, depsOf]
  iframe Hcs
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef, wire.gryffproto.PreAccept.goVal]
  iframe

theorem resolvePreAccept_proof (γ : GryffNames GF) (k : Fin 3) (r p : Loc) (m : model.PreAcceptM) :
    resolveSpecB γ k r (App (repMB r go!"resolvePreAccept") (Val #p)) (msgAt p (.preAccept m))
      (.msg (.preAccept m)) := by
  intro pr tr ws
  iintro %Φ ⟨#Hpkg, #Hl, Hp, Hm⟩ HΦ
  unfold msgAt
  icases Hm with ⟨%g, %s, Hg, #Hcs, %Hgm⟩
  wp_apply wp_resolvePreAccept_g $$ [Hp Hg Hcs] as ⟨Hp, Hg, Hcs⟩
  · iframe; iframe #
  iapply HΦ
  subst Hgm
  iframe
  iexists g, s
  iframe
  ipureintro; rfl

theorem wp_resolveAccept_g (γ : ProtoNames) (k : Fin 3) (r : Loc) (p : ProphId) (tr : List Ev)
    (ws : List w64) (l : Loc) (dq dqs : DFrac) (g : wire.gryffproto.EAccept.Msg) (s : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        r.[src.gryff.Replica, go!"proph"] ↦□ p ∗ replicaProph γ k p tr ws ∗
        l ↦{dq} wire.gryffproto.EAccept.goVal g s ∗ s ↦*{dqs} g.Command }}
      (App (repMB r go!"resolveAccept") (Val #l))
    {{ RET #(); replicaProph γ k p tr (ws ++ encEv (.msg (.accept (acceptOf g)))) ∗
        l ↦{dq} wire.gryffproto.EAccept.goVal g s ∗ s ↦*{dqs} g.Command }} := by
  unfold repMB
  wp_start as ⟨#Hl, Hp, Hg, Hcs⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hg
  iStructNamed Hg
  simp only [wire.gryffproto.EAccept.goVal]
  wp_auto
  rp_step
  rp_step
  rp_step
  rp_step
  rp_step
  rp_step
  try wp_auto
  wp_apply +noauto wp_resolveDeps $$ [Hp] as Hp
  · iframe; iframe #
  try wp_auto
  wp_apply +noauto wp_resolveCmds $$ [Hp Hcs] as ⟨Hp, Hcs⟩
  · iframe; iframe #
  try wp_auto
  wp_apply +noauto wp_resolveValTag $$ [Hp Base] as ⟨Hp, Base⟩
  · iframe; iframe #
  try wp_auto
  iapply HΦ
  isplitl [Hp]
  · iapply replicaProph_congr ?_ $$ Hp
    simp [evCodec, encEv, encAccept, acceptOf, ofI32, ofU8, ofI8, encVT, encTag, vtOf, tagOf, depsOf]
  iframe Hcs
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef, wire.gryffproto.EAccept.goVal]
  iframe

theorem resolveAccept_proof (γ : GryffNames GF) (k : Fin 3) (r p : Loc) (m : model.EAcceptM) :
    resolveSpecB γ k r (App (repMB r go!"resolveAccept") (Val #p)) (msgAt p (.accept m))
      (.msg (.accept m)) := by
  intro pr tr ws
  iintro %Φ ⟨#Hpkg, #Hl, Hp, Hm⟩ HΦ
  unfold msgAt
  icases Hm with ⟨%g, %s, Hg, #Hcs, %Hgm⟩
  wp_apply wp_resolveAccept_g $$ [Hp Hg Hcs] as ⟨Hp, Hg, Hcs⟩
  · iframe; iframe #
  iapply HΦ
  subst Hgm
  iframe
  iexists g, s
  iframe
  ipureintro; rfl

theorem wp_resolveCommit_g (γ : ProtoNames) (k : Fin 3) (r : Loc) (p : ProphId) (tr : List Ev)
    (ws : List w64) (l : Loc) (dq dqs : DFrac) (g : wire.gryffproto.ECommit.Msg) (s : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        r.[src.gryff.Replica, go!"proph"] ↦□ p ∗ replicaProph γ k p tr ws ∗
        l ↦{dq} wire.gryffproto.ECommit.goVal g s ∗ s ↦*{dqs} g.Command }}
      (App (repMB r go!"resolveCommit") (Val #l))
    {{ RET #(); replicaProph γ k p tr (ws ++ encEv (.msg (.commit (commitOf g)))) ∗
        l ↦{dq} wire.gryffproto.ECommit.goVal g s ∗ s ↦*{dqs} g.Command }} := by
  unfold repMB
  wp_start as ⟨#Hl, Hp, Hg, Hcs⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hg
  iStructNamed Hg
  simp only [wire.gryffproto.ECommit.goVal]
  wp_auto
  rp_step
  rp_step
  rp_step
  try wp_auto
  wp_apply +noauto wp_resolveCmds $$ [Hp Hcs] as ⟨Hp, Hcs⟩
  · iframe; iframe #
  rp_step
  try wp_auto
  wp_apply +noauto wp_resolveDeps $$ [Hp] as Hp
  · iframe; iframe #
  try wp_auto
  wp_apply +noauto wp_resolveValTag $$ [Hp Base] as ⟨Hp, Base⟩
  · iframe; iframe #
  try wp_auto
  iapply HΦ
  isplitl [Hp]
  · iapply replicaProph_congr ?_ $$ Hp
    simp [evCodec, encEv, encCommit, commitOf, ofI32, ofU8, ofI8, encVT, encTag, vtOf, tagOf, depsOf]
  iframe Hcs
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef, wire.gryffproto.ECommit.goVal]
  iframe

theorem resolveCommit_proof (γ : GryffNames GF) (k : Fin 3) (r p : Loc) (m : model.ECommitM) :
    resolveSpecB γ k r (App (repMB r go!"resolveCommit") (Val #p)) (msgAt p (.commit m))
      (.msg (.commit m)) := by
  intro pr tr ws
  iintro %Φ ⟨#Hpkg, #Hl, Hp, Hm⟩ HΦ
  unfold msgAt
  icases Hm with ⟨%g, %s, Hg, #Hcs, %Hgm⟩
  wp_apply wp_resolveCommit_g $$ [Hp Hg Hcs] as ⟨Hp, Hg, Hcs⟩
  · iframe; iframe #
  iapply HΦ
  subst Hgm
  iframe
  iexists g, s
  iframe
  ipureintro; rfl

theorem wp_resolvePrepareReply_g (γ : ProtoNames) (k : Fin 3) (r : Loc) (p : ProphId) (tr : List Ev)
    (ws : List w64) (l : Loc) (dq dqs : DFrac) (g : wire.gryffproto.PrepareReply.Msg) (s : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        r.[src.gryff.Replica, go!"proph"] ↦□ p ∗ replicaProph γ k p tr ws ∗
        l ↦{dq} wire.gryffproto.PrepareReply.goVal g s ∗ s ↦*{dqs} g.Command }}
      (App (repMB r go!"resolvePrepareReply") (Val #l))
    {{ RET #(); replicaProph γ k p tr (ws ++ encEv (.msg (.prepareReply (prepareReplyOf g)))) ∗
        l ↦{dq} wire.gryffproto.PrepareReply.goVal g s ∗ s ↦*{dqs} g.Command }} := by
  unfold repMB
  wp_start as ⟨#Hl, Hp, Hg, Hcs⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hg
  iStructNamed Hg
  simp only [wire.gryffproto.PrepareReply.goVal]
  wp_auto
  rp_step
  rp_step
  rp_step
  rp_step
  rp_step
  rp_step
  rp_step
  rp_step
  try wp_auto
  wp_apply +noauto wp_resolveCmds $$ [Hp Hcs] as ⟨Hp, Hcs⟩
  · iframe; iframe #
  rp_step
  try wp_auto
  wp_apply +noauto wp_resolveDeps $$ [Hp] as Hp
  · iframe; iframe #
  try wp_auto
  wp_apply +noauto wp_resolveValTag $$ [Hp Base] as ⟨Hp, Base⟩
  · iframe; iframe #
  try wp_auto
  iapply HΦ
  isplitl [Hp]
  · iapply replicaProph_congr ?_ $$ Hp
    simp [evCodec, encEv, encPrepareReply, prepareReplyOf, ofI32, ofU8, ofI8, encVT, encTag, vtOf, tagOf, depsOf]
  iframe Hcs
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef, wire.gryffproto.PrepareReply.goVal]
  iframe

theorem resolvePrepareReply_proof (γ : GryffNames GF) (k : Fin 3) (r p : Loc) (m : model.PrepareReplyM) :
    resolveSpecB γ k r (App (repMB r go!"resolvePrepareReply") (Val #p)) (msgAt p (.prepareReply m))
      (.msg (.prepareReply m)) := by
  intro pr tr ws
  iintro %Φ ⟨#Hpkg, #Hl, Hp, Hm⟩ HΦ
  unfold msgAt
  icases Hm with ⟨%g, %s, Hg, #Hcs, %Hgm⟩
  wp_apply wp_resolvePrepareReply_g $$ [Hp Hg Hcs] as ⟨Hp, Hg, Hcs⟩
  · iframe; iframe #
  iapply HΦ
  subst Hgm
  iframe
  iexists g, s
  iframe
  ipureintro; rfl

theorem wp_resolvePreAcceptReply_g (γ : ProtoNames) (k : Fin 3) (r : Loc) (p : ProphId) (tr : List Ev)
    (ws : List w64) (l : Loc) (dq : DFrac) (g : src.gryffproto.PreAcceptReply) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        r.[src.gryff.Replica, go!"proph"] ↦□ p ∗ replicaProph γ k p tr ws ∗ l ↦{dq} g }}
      (App (repMB r go!"resolvePreAcceptReply") (Val #l))
    {{ RET #(); replicaProph γ k p tr (ws ++ encEv (.msg (.preAcceptReply (preAcceptReplyOf g)))) ∗
        l ↦{dq} g }} := by
  unfold repMB
  wp_start as ⟨#Hl, Hp, Hg⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hg
  iStructNamed Hg
  wp_auto
  rp_step
  rp_step
  rp_step
  rp_step
  rp_step
  rp_step
  try wp_auto
  wp_apply +noauto wp_resolveDeps $$ [Hp] as Hp
  · iframe; iframe #
  try wp_auto
  wp_apply +noauto wp_resolveValTag $$ [Hp Base] as ⟨Hp, Base⟩
  · iframe; iframe #
  try wp_auto
  iapply HΦ
  isplitl [Hp]
  · iapply replicaProph_congr ?_ $$ Hp
    simp [evCodec, encEv, encPreAcceptReply, preAcceptReplyOf, ofI32, ofU8, ofI8, encVT, encTag, vtOf, tagOf, depsOf]
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

theorem resolvePreAcceptReply_proof (γ : GryffNames GF) (k : Fin 3) (r p : Loc)
    (m : model.PreAcceptReplyM) :
    resolveSpecB γ k r (App (repMB r go!"resolvePreAcceptReply") (Val #p)) (msgAt p (.preAcceptReply m))
      (.msg (.preAcceptReply m)) := by
  intro pr tr ws
  iintro %Φ ⟨#Hpkg, #Hl, Hp, Hm⟩ HΦ
  unfold msgAt
  icases Hm with ⟨%g, Hg, %Hgm⟩
  wp_apply wp_resolvePreAcceptReply_g $$ [Hp Hg] as ⟨Hp, Hg⟩
  · iframe; iframe #
  iapply HΦ
  subst Hgm
  iframe
  iexists g
  iframe
  ipureintro; rfl


end

section bridge
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [wire.BufioSpecs GF]

theorem wp_resolveU64_test (γ : ProtoNames) (k : Fin 3) (r : Loc) (p : ProphId) (t : List Ev)
    (ws : List w64) (x : w64) :
    {{ r.[src.gryff.Replica, go!"proph"] ↦□ p ∗ replicaProph γ k p t ws }}
      (App (Val (r.[src.gryff.Replica, go!"proph"] @!!
        go.PointerType github_com.goose_lang.primitive.ProphId.ty @!! go!"ResolveU64")) (Val #x))
    {{ RET #(); replicaProph γ k p t (ws ++ [x]) }} :=
  wp_resolveU64 (hG := ⟨G, hG.goose_localGS⟩) γ k r p t ws x

end bridge

end Perennial.gryff.unitB
