/- Lean-first (no Rocq counterpart).

# `lib/grpcdriver`: the server's state

**The server** (`isDrvServer γid s`, persistent): the `*server` `s`'s mutex owns its `runs` field,
the map `m` of run counts it points to, and a list `ids` of call ids with their tokens
(`idTok γid id`, `Defs.lean`), such that every value with a nonzero count is a fresh value
`mkVal id w` of an id among `ids` (`runsOk`). An `Echo` request's spec (`echoSpec`, `Svc.lean`)
carries its value's id's token, so a second run of a value would hold two tokens of one id
(`mkVal_inj`): it does not happen, every count is `0` or `1`, and `Echo` answers `v#1`.

The errors' lemmas (`errStr_srvErrOk`, `errStr_descIs`) are in `svc/StreamDefs.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.Svc
public import Proof.errors.NewVar
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.StreamDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode EtcdGrove

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

/-- Every value with a nonzero run count is a fresh value of an id among `ids`. -/
def runsOk (m : GMap GoString w64) (ids : List w64) : Prop :=
  ∀ (v : GoString) (n : w64), m !! v = some n → n ≠ W64 0 →
    ∃ (id : w64) (w : GoString), v = mkVal id w ∧ wordOk w ∧ id ∈ ids

/-- A first run of the fresh value `mkVal id w` adds its id. -/
theorem runsOk_insert {m : GMap GoString w64} {ids : List w64} {id : w64} {w v : GoString}
    (h : runsOk m ids) (hv : v = mkVal id w) (hw : wordOk w) (n : w64) :
    runsOk (<[v := n]> m) (id :: ids) := by
  intro v' n' hl hn
  by_cases he : v' = v
  · subst he
    exact ⟨id, w, hv, hw, by simp⟩
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm he)] at hl
    obtain ⟨id', w', h1, h2, h3⟩ := h v' n' hl hn
    exact ⟨id', w', h1, h2, by simp [h3]⟩

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

/-- The server's lock invariant (see the file header). -/
def drvSrvInv (γid : GName) (s : Loc) : IProp GF :=
  iprop(∃ (mref : Loc) (m : GMap GoString w64) (ids : List w64),
    structFieldRef server go!"runs" s ↦ mref ∗ ownMap mref (DFrac.own 1) m ∗ ⌜runsOk m ids⌝ ∗
    [∗list] id ∈ ids, idTok γid id)

/-- **`s` is the driver's server** (persistent; see the file header). -/
def isDrvServer (γid : GName) (s : Loc) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver ∗
    sync.isMutex (structFieldRef server go!"mu" s) (drvSrvInv γid s))

instance isDrvServer_persistent (γid : GName) (s : Loc) :
    Persistent (isDrvServer (GF := GF) γid s) := by
  unfold isDrvServer; infer_instance

end defs

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

end Perennial
