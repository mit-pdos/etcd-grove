/- Lean-first (no Rocq counterpart).

# `osfs/bboltfs`: the definitions its top-level statement is written in

The program the example's top-level theorem is about, and the other definitions its statement
names, moved here unchanged out of `Results.lean` so that the statement
(`Spec/.../TopLevelRobustness.lean`) imports no proof (CLAUDE.md, "Import tiers").
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.BootMinibolt
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.P1Sat
public import Robustness.Statement

@[expose] public section

noncomputable section

section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace EtcdGrove

namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs

open Fs

section links

variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]

variable [go_gctx : GoGlobalContext]

variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

variable [sem : go.Semantics]

variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Assumptions]


/-- The package initializer's spec (an assumption of `bootCrashSafety`: see the file header). -/
abbrev initialize'.spec : Prop :=
  {{ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ }}
    (App (Val initialize') (Val #()))
  {{ RET #(); pkgFacts (GF := GF) }}

end links
end osfs_bboltfs
end EtcdGrove
end Perennial

end

section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace EtcdGrove

namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs

open Fs

attribute [local instance] fsExts fsExtsInterp

local instance : GooseSemantics := fsExtsSemanticsWithS AnyStep P1

local instance : ExtSemantics fsExt := fsSemWithS AnyStep P1

local instance : HasExt fsExt := fsExtsWithS_hasFs AnyStep P1

/-- `AnyStep` keeps every step. -/
theorem anyStep_keeps : StepKeeps AnyStep := by
  intro _ _ _ _ _ _ _ _ _ _ hs
  exact ⟨_, _, _, hs, trivial⟩

/-- The semantics' instances the specs need, over the semantics with P1. -/
abbrev P1Ctx (P : ∀ [GooseSemantics] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], Prop) : Prop :=
  letI := fsExtsSemanticsWithS AnyStep P1
  letI := fsSemWithS AnyStep P1
  letI := fsExtsWithS_hasFs AnyStep P1
  haveI : FsSemOk := fsSemWithS_ok AnyStep P1 anyStep_keeps
  P

end osfs_bboltfs
end EtcdGrove
end Perennial

end

section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace EtcdGrove

namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs

open Fs

attribute [local instance] fsExts fsExtsInterp

local instance : GooseSemantics := fsExtsSemanticsWithS AnyStep P1

local instance : ExtSemantics fsExt := fsSemWithS AnyStep P1

local instance : HasExt fsExt := fsExtsWithS_hasFs AnyStep P1

section adequacy

variable [GoGlobalContext] {GF : BundledGFunctors}

/-- A ghost-state instance at the local context `lctx` (the hypotheses are stated over every
instance whose Go local context is the semantics' own). -/
abbrev heapAt (hG : HeapGS .hasLC GF) (lctx : GoLocalContext) : HeapGS .hasLC GF :=
  ⟨hG.goose_globalGS, { hG.goose_localGS with goose_go_local_context := lctx }⟩

end adequacy
end osfs_bboltfs
end EtcdGrove
end Perennial

end

end
