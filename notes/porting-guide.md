# Porting a Rocq file of `election_proof/` to Lean

How the files already ported (`EtcdGrove/Raft/ElectionProof/{Protocol,Defs,InvBig,
InvLogger,StepLemmas}.lean`, `EtcdGrove/Raft/Base.lean`) translate Rocq. Read one of
them before starting; Perennial's own ports of the raft proofs
(`.lake/packages/perennial/Perennial/Proof/go_etcd_io/raft/v3_proof/{readonly,
protocol}.lean`) show WP proofs in the same setting.

The Rocq source is on branch `main` of this repository (checked out at
`~/etcd-grove`): `new/proof/go_etcd_io/raft/election_proof/<file>.v`.

## Files and modules

* `inv_tracker.v` → `EtcdGrove/Raft/ElectionProof/InvTracker.lean`, module
  `EtcdGrove.Raft.ElectionProof.InvTracker` (UpperCamel of the Rocq file name).
* `Require Export …election_proof.X` → `import EtcdGrove.Raft.ElectionProof.X`.
* Everything is in `namespace Perennial` / `namespace EtcdGrove`; `open Iris Iris.BI
  go_etcd_io.raft.v3` (plus `Iris.ProofMode` for proofs).
* Start the file with a `/- Port of … -/` header that keeps the Rocq file's leading
  comment (it is the design documentation), with a `Lean notes:` paragraph for anything
  that differs.
* Never import Perennial's `Perennial.Proof.go_etcd_io.raft.v3_proof.base`: this
  repository's `EtcdGrove.Raft.Base` replaces it (stronger package-init instances).

## Section variables (Rocq `Context `{hG: heapGS Σ, …}`)

```lean
section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
```

Ghost state needs `[AllG GF]` (and `[InvGS GF]` for fancy updates outside a WP).
Pure definitions need only `[FfiSyntax]` (and `[GoGlobalContext]
[GoSemanticsFunctions]` for `functions …`).

A Rocq `Axiom` (an abstract predicate, a trust-boundary triple) is a Lean `axiom`
whose binders are written out (an `axiom` does not pick up the instance section
variables it does not mention: Perennial's `etc/fidelity-review.md`, H1), e.g.
`axiom ownBigInt {GF : BundledGFunctors} : Loc → Int → IProp GF`. For a triple axiom
inside the section above, check with `#check @name` that the instance binders are
there.

## Names (Lean conventions; Perennial was renamed the same way)

| Rocq | Lean |
|---|---|
| `own_raft_phys`, `is_Storage` (iProp-valued defs) | `ownRaftPhys`, `isStorage` |
| `nstate_wf`, `is_quorum` (Prop-valued defs) | `NStateWf`, `IsQuorum` |
| lemma `own_raft_phys_agree` | `ownRaftPhys_agree` (snake, defs as written) |
| `nstate.t`, `logstate.t`, `pstate.t`, `msg.t`, `role.t`, `mtype.t` | `NState`, `LogState`, `PState`, `Msg`, `Role`, `MsgType` |
| `role.Leader`, `mtype.VoteResp` | `.leader`, `.voteResp` |
| `msg.from`/`msg.to` | `Msg.src`/`Msg.dst` |
| Go struct `raft.raft.t`, field `x.(raft.raft.Term')` | `raft`, `x.Term'` (value type is the Go name) |
| Go type descriptor `raft.raft`, `go.PointerType raft.raft` | `raft.ty`, `go.GoType.PointerType raft.ty` |
| `raftpb.Message.t`, `tracker.Progress.t` | `raftpb.Message`, `tracker.Progress` |
| `slice.t`, `loc`, `go_string`, `func.t`, `interface.t`, `interface.t_ok` | `GoSlice`, `Loc`, `GoString`, `GoFunc`, `GoInterface`, `GoInterfaceOk` |
| `interface.mk_ok t v`, `interface.nil` | `interface.mkOk t v`, `interface.nil` |
| `"Foo"%go` | `go!"Foo"` |
| `word.add a b`, `uint.Z`, `sint.Z` | `a + b`, `uint.Z`, `sint.Z` |
| `gmap K V`, `gset K`, `{[x]}`, `X ∖ Y`, `dom m` | `GMap K V`, `GSet K`, `{[x]}`, `X \ Y`, `domSet m` |
| `s <| f := v |>` | `{ s with f := v }` |
| `omap f l`, `Forall P l` | `l.filterMap f`, `∀ x ∈ l, P x` |
| `l1 ≡ₚ l2`, `l1 ⊆+ l2` | `l1 ≡ₚ l2`, `l1.Subperm l2` |
| `zero_val raftpb.Entry.t` | `zero_val raftpb.Entry` |
| `functions raft.stepLeader []` | `functions stepLeader []` |
| wp lemma `wp_raft__Step` (method `Step` of `raft`) | `raft.wp_Step` |

Perennial's Rocq → Lean name table is `.lake/packages/perennial/etc/lean-rename/
renames.tsv` (grep the Rocq name). The generated Lean code is in
`.lake/packages/perennial/Perennial/Code/go_etcd_io/raft/v3*.lean` (definitions) and
`…/GeneratedProof/…` (struct points-to instances): grep there for a type or field.

## Separation logic

| Rocq | Lean |
|---|---|
| `l ↦ v`, `l ↦{dq} v`, `l ↦□ v` | same |
| `s ↦* vs`, `s ↦*{dq} vs`, `s ↦*□ vs` | same |
| `own_slice_cap T s dq` | `ownSliceCap T s dq` |
| `m ↦$ mv`, `m ↦$□ mv` | same |
| `l.[raft.raft.t, "f"]` | `l.[raft, go!"f"]` |
| `[∗ list] x ∈ l, P x` | `[∗list] x ∈ l, P x` |
| `[∗ map] k ↦ v ∈ m, P k v` | `[∗map] k ↦ v ∈ m, P k v` |
| `[∗ set] x ∈ X, P x` | `[∗map] x ↦ _u ∈ toMap X, P x` (`toMap`, `Protocol.lean`: GSet has no `[∗set]` instance) |
| `"H" ∷ P` named conjuncts | same, inside `iprop(…)` |
| `{{{ P }}} e {{{ RET v; Q }}}` | `{{ P }} e {{ RET v; Q }}`; binders: `{{ (x : T), RET #x; Q }}` |
| `p @! (go.PointerType raft.raft) @! "poll" #a #b` | `(App (App (Val (p @!! go.GoType.PointerType raft.ty @!! go!"poll")) (Val #a)) (Val #b))` |
| `@! raft.newRaft #c` | `(App (Val #(functions newRaft [])) (Val #c))` |
| `is_pkg_init raft` | `isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3` |

Lemma names: `BigSepL.bigSepL_cons/append/singleton/nil/lookup`, `BigSepM.bigSepM_insert/
lookup/empty/impl`, `ghostMapAuth`, `k ↪[γ]□ v`, `ghost_map_insert_persist`,
`ghostMapElem_agree`, `ghostMapAuth_valid_2`; `GMap.lookup_insert_eq/ne`,
`GMap.elem_of_*`, `GMap.set_eq`; `set_solver`, `word`, `omega`.

## Tactics

| Rocq | Lean |
|---|---|
| `iIntros "H %x #Hp [H1 H2]"` | `iintro H %x #Hp ⟨H1, H2⟩` |
| `iDestruct "H" as (x) "[H1 H2]"` | `icases H with ⟨%x, H1, H2⟩` |
| `iNamed "H"` | `iNamed H` (first `icases H with ⟨%x, H⟩` the existentials) |
| `iDestruct (lem with "H") as "#H'"` | `ihave #H' := lem $$ H` |
| `iAssert P with "[H]" as "H'"` | `ihave H' : P $$ [H]` (proof of `P` is the first goal) |
| `iFrame "H"`, `iFrame "∗#"` | `iframe H`, `iframe # ∗` |
| `iExists x` | `iexists x` |
| `iSplitL "H"` / `iSplitR` | `isplitl [H]` / `isplitr` |
| `iMod (lem with "H") as "H'"` | `imod lem $$ H with H'` |
| `iModIntro`, `iPureIntro`, `iApply` | `imodintro`, `ipureintro`, `iapply` |
| `rewrite big_sepL_app` in a hypothesis | `icases (BigSepL.bigSepL_append (Φ := …)).1 $$ H with ⟨H1, H2⟩` |
| `wp_start`, `wp_auto`, `wp_apply lem as …`, `wp_for`, `wp_end` | same names; see Perennial's `docs/PERENNIAL_PROOF_REFERENCE.md` |
| `done` for `⊢ emp`-like goals | `iempintro` |

Unsolved iris goals print their context; read them. Reusable facts that would be a
Rocq `Ltac` go here as a lemma or a small macro.

## Checking a file

    export PATH=$HOME/.elan/bin:$PATH
    lake build EtcdGrove.Raft.ElectionProof.Defs        # dependencies, once
    lake env lean EtcdGrove/Raft/ElectionProof/X.lean    # the file itself

(`lake env lean` ignores the lakefile's `linter.unusedSectionVars false`, so it warns
about unused section variables: harmless.) Leave a `sorry` with a comment saying what
is missing rather than weakening a statement; never change a spec's statement to make
a proof go through without saying so in the file.

## Spec and proof files (the module discipline; notes/decisions.md)

`spec_<fn>.v` → `Spec/<fn>.lean`, `proof_<fn>.v` → `Proof/<fn>.lean` (the Rocq file
name's `<fn>`, e.g. `Spec/raft__Step.lean`); `postulates_<fn>.v` becomes the hypothesis
list of the proof theorem; `link_<fn>.v` becomes one line of `Election.lean`. Models:
`Spec/lockedRand__Intn.lean`, `Proof/lockedRand__Intn.lean` (a proof with three callee
specs), `Proof/big_NewInt.lean` (a trust-boundary axiom).

* The spec is `abbrev <T>.<M>.spec : Prop := ∀ args, premises → {{ … }} e {{ … }}`
  (an `abbrev`, so that `wp_apply h` works on a hypothesis `h : C.spec`) inside the
  standard section variables; for a function `F`, `F.spec`; for a function or a method of a type of another
  package, prefix the package (`big.NewInt.spec`, `tracker.Progress.ResetState.spec`,
  `quorum.JointConfig.IDs.spec`); a Lean keyword is quoted (`slices.«Sort».spec`). It keeps the Rocq `Definition wp_<fn>_body`'s
  comment. The Rocq binders `ext ffi … package_sem` are the section variables; the
  function's own binders are the `∀`.
* The proof is `theorem <T>.<M>.wp_proof (wp_C₁ : C₁.spec (GF := GF) (hG := hG)) … :
  <T>.<M>.spec (GF := GF) (hG := hG)`, one hypothesis per `Include` of the postulates,
  in the same order, named after the Rocq `P.wp_…` it replaces; it imports its own
  `Spec` file and its callees' `Spec` files only (never another `Proof` file). Specs of
  Perennial's library (e.g. `sync.Mutex.wp_Lock`) are used directly, as in Rocq.
  Trust-boundary triples (Rocq `Axiom` inside the functor) are `axiom <…>.wp_proof :
  <…>.spec (GF := GF) (hG := hG)`; unfinished ones (Rocq `Admitted`) are a theorem with a
  `sorry`.
* Proofs start with `intro` of the spec's binders and premises, then `wp_start as …`.
* `Election.lean` gets `theorem T.wp_M : T.M.spec (GF := GF) (hG := hG) :=
  T.M.wp_proof <callee results>`.
