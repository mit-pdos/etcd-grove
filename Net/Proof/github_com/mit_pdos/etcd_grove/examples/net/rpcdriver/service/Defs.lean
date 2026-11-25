/- Lean-first (no Rocq counterpart).

# `net/rpcdriver/service`: the service's representation predicate

`isSvc γid s` (persistent): the package is initialized and `s.mu` is a `sync.Mutex` whose
invariant (`svcInv`) owns `s.runs` and the map it points to, each of whose entries `id ↦ n` has
`n = 1` and holds `id`'s token `idTok γid id` (the client's exclusive token of a request id,
`Svc.lean`). So a run of `Echo` given `id`'s token finds no entry for `id` (it would hold a second
token of it), and its run counts `1`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service.Base
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Svc

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service

section addrs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- The address of `s.mu`. -/
abbrev muAddr (s : Loc) : Loc := structFieldRef service.Svc go!"mu" s

/-- The address of `s.runs`. -/
abbrev runsAddr (s : Loc) : Loc := structFieldRef service.Svc go!"runs" s

end addrs

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : service.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The lock invariant of `s.mu` (see the file header). -/
def svcInv (γid : GName) (s : Loc) : IProp GF :=
  iprop(∃ (mref : Loc) (m : GMap w64 w64), runsAddr s ↦ mref ∗ mref ↦$ m ∗
    [∗map] id ↦ n ∈ m, ⌜n = W64 1⌝ ∗ idTok γid id)

/-- The service `s` (persistent; see the file header). -/
def isSvc (γid : GName) (s : Loc) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service ∗
    sync.isMutex (muAddr s) (svcInv γid s))

instance isSvc_persistent (γid : GName) (s : Loc) : Persistent (isSvc (GF := GF) γid s) := by
  unfold isSvc; infer_instance

/-- A request id's token is exclusive. -/
theorem idTok_excl (γid : GName) (id : w64) :
    ⊢ idTok (GF := GF) γid id -∗ idTok γid id -∗ False := by
  unfold idTok
  iintro H1 H2
  icases ghostMapElem_valid_2 _ _ _ _ _ _ $$ H1 H2 with %Hv
  exfalso
  have : ((1 : Qp) + 1).val ≤ 1 := Hv.1
  simp at this
  grind

end defs

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service
end Perennial
