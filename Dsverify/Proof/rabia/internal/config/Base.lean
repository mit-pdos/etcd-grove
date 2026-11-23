/-
The package fact of `rabia.internal.config` (the lab's `config` package state, `Proof/Rabia/
PkgState.lean`, redesigned for remote's machines, notes/dsv-rabia.md): `Conf`'s points-to is in an
invariant (`confInv`), as initialized (`Conf ↦ zero`) or claimed by the machine's one `configure`
(`confClaim`, `Core/PkgState.lean`): the claimer gives up its package state (`ownGoState`,
exclusive on its machine; the boot hands it to `main` after the initialization), so a second claim
is excluded.
-/
module

public import Dsverify.GeneratedProof.rabia.internal.config
public import Net.Proof.net.Base
public import Perennial.Proof.fmt.Base
public import Proof.os.PkgInit
public import Perennial.Proof.strconv.Base
public import Perennial.Proof.strings.Base
public import Perennial.Proof.time.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace rabia.internal.config

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The namespace of `Conf`'s invariant (below the system's, `Core/Ghost.lean`'s `rabiaR`). -/
def confN : Namespace := ndot (ndot nroot "rabia") "conf"

/-- `Conf`'s invariant: as initialized, or claimed (the claimer's package state). -/
def confInv : IProp GF :=
  iprop((globalAddr Conf ↦ (zeroValDef : Config)) ∨
    ∃ σ : GMap GoString Bool, ownGoState (hG := hG.goose_localGS.goose_go_stateGS) σ)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.rabia.internal.config :=
  define_is_pkg_init (inv confN (confInv (GF := GF)))
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.rabia.internal.config :=
  build_get_is_pkg_init_wf

end def_

end rabia.internal.config
end Perennial
