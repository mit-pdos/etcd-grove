/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2c/Helpers.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2c: the statements of the helpers H2c's handlers call (proved by H2a / H2b)

No statement of these existed when H2c started (H2a: `updateCommitted`, `mergeAttributes`; H2b:
`bcastAccept`, `bcastCommit`, `replyAccept`). H2c states them here; the H2b ones are proved by
H2b's (`h2b.bcastCommit_wp`, `h2b.bcastAccept_wp`, `h2b.replyAccept_wp`, integration), the H2a
ones are H2a's own (integration).
-/
module

public import Dsverify.Proof.gryff.H2.Attr
public import Dsverify.Proof.gryff.H2b.Bcast
public import Dsverify.Proof.gryff.H3.Pure
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB Proposal Msg Ev Out Cmd Deps)
open Perennial.gryff.replica (XS rowOwn nSlots)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]
/-- An `*EPaxosRMWHandler` method value. -/
abbrev hM (h : Loc) (f : GoString) : Expr :=
  Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!! f)
end

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF] -- H1-R6 / N-1
variable [sortA : Perennial.gryff.replica2.SortSliceHyp GF]
variable [strconvA : strconv.Assumptions] -- N-5



/- `updateCommitted`, `mergeAttributes`: H2a's `wp_updateCommitted` (`H2/Attr.lean`) and
`wp_mergeAttributes` (`H2a/Merge.lean`), same statements (integration: H2c's sorry'd copies
removed; `updateCommitted`'s row premise is `0 ≤ q < 3`). -/

/-- `bcastCommit(replica, instance, cmds, seq, deps, base)` (H2b's): the model's sends, in order;
the globals `ec` / `ecs` are `epaxosRest`'s. -/
theorem wp_bcastCommit (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h pa co : Loc)
    (t : List Ev) (s : RState) (hid : s.id = rid32 k) (q i : w32) (sl : GoSlice)
    (gs : List src.state.Command) (seq : w32) (deps : GoArray w32 5)
    (base : src.gryffproto.ValTag) (os outs : List Out)
    (hb : model.bcastCommit s q i (gs.map cmdOf) seq (depsOf deps) (vtOf base) = some os)
    (hok : model.cmdsOk (gs.map cmdOf) = true) : -- H2c-R1 (`h2b.bcastCommit_wp` takes `cmdsRep`)
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ epEnv γ ρ k r gR h pa co ∗
        epaxosRest h ∗ sl ↦*□ gs ∗ pendingOuts γ ρ k r t (os ++ outs) }}
      (App (App (App (App (App (App (hM h go!"bcastCommit") (Val #q)) (Val #i)) (Val #sl))
        (Val #seq)) (Val #deps)) (Val #base))
    {{ RET #(); epaxosRest h ∗ pendingOuts γ ρ k r t outs }} := by
  iintro %Φ ⟨#Hpkg, #Henv, Hrest, #Hsl, Hpend⟩ HΦ
  iunfold epEnv at Henv
  icases Henv with ⟨#HgR, -, -, -, #HR, #Hid, #HN, -, #Hgen, #Hfix⟩
  ihave #Hbc : h2b.bcFixed γ ρ k r gR h $$ []
  · unfold h2b.bcFixed; iframe #
  ihave #Hc : cmdsRep sl (gs.map cmdOf) $$ []
  · iapply (h2b.cmdsRep_open ..).2; iexists gs; iframe Hsl; ipureintro; exact ⟨rfl, hok⟩
  wp_apply h2b.bcastCommit_wp γ ρ k r gR h t s q i seq sl (gs.map cmdOf) deps base os outs hid hb
    $$ [$Hbc $Hrest $Hc $Hpend] as ⟨Hrest, Hpend⟩
  iapply HΦ; iframe

/-- `bcastAccept(replica, instance, ballot, cmds, seq, deps, base)` (H2b's). -/
theorem wp_bcastAccept (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h pa co : Loc)
    (t : List Ev) (s : RState) (hid : s.id = rid32 k) (q i b : w32) (sl : GoSlice)
    (gs : List src.state.Command) (seq : w32) (deps : GoArray w32 5)
    (base : src.gryffproto.ValTag) (os outs : List Out)
    (hb : model.bcastAccept s q i b (gs.map cmdOf) seq (depsOf deps) (vtOf base) = some os)
    (hok : model.cmdsOk (gs.map cmdOf) = true) : -- H2c-R1 (`h2b.bcastAccept_wp` takes `cmdsRep`)
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ epEnv γ ρ k r gR h pa co ∗
        epaxosRest h ∗ sl ↦*□ gs ∗ pendingOuts γ ρ k r t (os ++ outs) }}
      (App (App (App (App (App (App (App (hM h go!"bcastAccept") (Val #q)) (Val #i)) (Val #b))
        (Val #sl)) (Val #seq)) (Val #deps)) (Val #base))
    {{ RET #(); epaxosRest h ∗ pendingOuts γ ρ k r t outs }} := by
  iintro %Φ ⟨#Hpkg, #Henv, Hrest, #Hsl, Hpend⟩ HΦ
  iunfold epEnv at Henv
  icases Henv with ⟨#HgR, -, -, -, #HR, #Hid, #HN, -, #Hgen, #Hfix⟩
  ihave #Hbc : h2b.bcFixed γ ρ k r gR h $$ []
  · unfold h2b.bcFixed; iframe #
  ihave #Hc : cmdsRep sl (gs.map cmdOf) $$ []
  · iapply (h2b.cmdsRep_open ..).2; iexists gs; iframe Hsl; ipureintro; exact ⟨rfl, hok⟩
  wp_apply h2b.bcastAccept_wp γ ρ k r gR h t s q i b seq sl (gs.map cmdOf) deps base os outs hid hb
    $$ [$Hbc $Hrest $Hc $Hpend] as ⟨Hrest, Hpend⟩
  iapply HΦ; iframe

/-- `replyAccept(replicaId, reply)` (H2b's): `SendMsg` to a peer. -/
theorem wp_replyAccept (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h pa co : Loc)
    (t : List Ev) (s : RState) (hid : s.id = rid32 k) (q : w32) (p : Loc)
    (m : model.AcceptReplyM) (o : Out) (outs : List Out)
    (hs : model.sendPeer s q (.acceptReply m) = some o) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ epEnv γ ρ k r gR h pa co ∗
        msgAt p (.acceptReply m) ∗ pendingOuts γ ρ k r t (o :: outs) }}
      (App (App (hM h go!"replyAccept") (Val #q)) (Val #p))
    {{ RET #(); msgAt p (.acceptReply m) ∗ pendingOuts γ ρ k r t outs }} := by
  obtain ⟨d, hx, hne, rfl⟩ := h3.sendPeer_some s k hid q _ o hs
  iintro %Φ ⟨#Hpkg, #Henv, Hm, Hpend⟩ HΦ
  iunfold epEnv at Henv
  icases Henv with ⟨#HgR, -, -, -, #HR, #Hid, #HN, -, #Hgen, #Hfix⟩
  ihave #Hbc : h2b.bcFixed γ ρ k r gR h $$ []
  · unfold h2b.bcFixed; iframe #
  wp_apply h2b.replyAccept_wp γ ρ k d r gR h t p m outs hne q hx $$ [$Hbc $Hm $Hpend]
    as ⟨Hm, Hpend⟩
  iapply HΦ; iframe

end

end Perennial.gryff.replica2
