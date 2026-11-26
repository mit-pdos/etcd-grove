/- Lean-first (no Rocq counterpart).

# A member's names chosen by the start: its auth names and its lessor name (#50 F7, L1 and L2)

`notes/axiom-review/f7-combined.md`, section 2 ("Usability"): `NewServer_dist` (`NewServer.specG_dist`, since F7
step 3) takes from its caller, per member, the auth names `γa` with their fresh
authorities (`authNamesFreshD γa`, with auth on) and the lessor name `γl` with half of its ghost map's
authority at `∅` and its slot (`lease.lessorSlot γl`). The start allocates them, before any machine runs,
over the global ghost state (no heap):
* `authNamesFreshG γa`: `authNamesFreshD γa`'s body at the ghost functors alone (`AllG`; the proposal's is at a
  `HeapGS`, which the start has not), equal to it at a `HeapGS` (`authNamesFreshG_iff`);
* `authNamesFreshG_alloc` (L1): fresh auth names with their authorities, from `auth.authHist_alloc`, the token
  provider's `tokAlloc`, the rights' empty map and the readiness cell's mono-nat;
* `lease.lessorSlot_alloc` (L2, `LessorSlot.lean`): a lessor name outside a given list, its half and its slot.
No axiom, no `sorry`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.MemberLessor
public import Proof.go_etcd_io.etcd.server.v3.auth.Boot
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthSrv

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode

section ghost
variable [GooseExts] {GF : BundledGFunctors} [AllG GF]

/-- **`γa`'s fresh authorities at the ghost functors alone** (`authNamesFreshD`'s body, with
`authFreshInit (.on γa)` unfolded to the rights' empty authority): what the start hands a member. -/
def authNamesFreshG (γa : auth.AuthNames) : IProp GF :=
  iprop(monoListAuthOwn γa.hist 1 [auth.bootState] ∗
    ghostVar γa.cur 1 auth.bootState ∗
    auth.tokAuth γa.tok γa.fresh ∅ ∗
    ghostMapAuth γa.fresh 1 (∅ : GMap GoString Unit) ∗
    auth.authPubAuth γa 0 ∗
    ghostVar γa.fen 1 false ∗
    ghostVar γa.fca 1 ((null : Loc), 0) ∗
    auth.capAuth γa [auth.bootState, auth.bump auth.bootState] ∗
    (∃ γ0 : GName × GName × GName, ghostVar γa.bk 1 γ0) ∗
    token γa.succ ∗
    ownTokAuth γa.rdt 0 ∗
    monoNatAuthOwn γa.rdy 1 0)

/-- **L1: the start allocates a member's auth names** with their fresh authorities. -/
theorem authNamesFreshG_alloc : ⊢ |==> ∃ γa : auth.AuthNames, authNamesFreshG (GF := GF) γa := by
  iintro
  imod (ghost_map_alloc_empty (GF := GF) (K := GoString) (V := Unit)) with ⟨%γf, Hf⟩
  imod (auth.tokAlloc (GF := GF) γf) with ⟨%γt, Ht⟩
  imod (mono_nat_own_alloc (GF := GF) 0) with ⟨%γy, Hy, -⟩
  imod (auth.authHist_alloc (GF := GF) γt γf γy [auth.bootState] auth.bootState
      [auth.bootState, auth.bump auth.bootState]
      (fun st hs => by simp at hs; subst hs; exact auth.bootState_permKeysOk))
    with ⟨%γa, %Hn, Hh, Hc1, Hc2, Hp, Hfen, Hfca, Hr, Hcap, -, Hbk, Hsucc, Hrdt⟩
  obtain ⟨ht, hf, hy⟩ := Hn
  imodintro
  iexists γa
  iunfold authNamesFreshG
  rw [ht, hf, hy]
  iframe Ht Hf Hy Hp Hfen Hfca Hcap Hbk Hsucc Hrdt
  isplitl [Hh Hr]
  · iunfold auth.authHist at Hh
    icases Hh with ⟨Hh, -⟩
    iapply (auth.authHist_full γa [auth.bootState]).2
    iframe Hh Hr
  · iunfold auth.authCurHalf at Hc1 Hc2
    iapply (ghostVar_split_half γa.cur 1 auth.bootState).2
    iframe Hc1 Hc2

end ghost

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- At a `HeapGS`, the start's `authNamesFreshG` is `NewServer_dist`'s `authNamesFreshD`. -/
theorem authNamesFreshG_iff (γa : auth.AuthNames) :
    authNamesFreshG (GF := GF) γa ⊣⊢ authNamesFreshD γa := by
  unfold authNamesFreshG authNamesFreshD authFreshInit
  exact .rfl

/-- **`NewServer_dist`'s auth names are the in-process `NewServer.specGAtA`'s** (#50 F7 S2, P-A1):
`authNamesFreshD γa` (through `authNamesFreshG`) is `srvAuthNamesFresh γa`, its conjuncts regrouped. -/
theorem authNamesFreshD_iff_srv (γa : auth.AuthNames) :
    authNamesFreshD (GF := GF) γa ⊣⊢ srvAuthNamesFresh γa := by
  refine (authNamesFreshG_iff γa).symm.trans ?_
  unfold authNamesFreshG srvAuthNamesFresh authNamesFreshTP auth.authBootFresh
  constructor
  · iintro ⟨Hh, Hc, Ht, Hf, Hp, Hfen, Hfca, Hcap, Hbk, Hs, Hr, Hy⟩
    iframe Hy Ht Hf Hh Hc Hp Hfen Hfca Hcap Hbk Hs Hr
  · iintro ⟨⟨Ht, Hf, Hh, Hc, Hp, Hfen, Hfca, Hcap, Hbk, Hs, Hr⟩, Hy⟩
    iframe Hy Ht Hf Hh Hc Hp Hfen Hfca Hcap Hbk Hs Hr

end heap

section share
variable {GF : BundledGFunctors} [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
  [GoGlobalContext] [GoLocalContext] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
  [go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
  [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
  [G : GooseGlobalGS .hasLC GF] [π : Net.NetProtoGS]

/-- **A member's lessor and auth names as the start hands them over** (#50 F7, L4; here since F7 step 2, for putget's `memberShare`;
`notes/axiom-review/f7-combined.md` §2): half of the lessor name `γl`'s ghost map's authority at `∅` with its slot
(`lease.lessorSlot_alloc`), and the auth names `γa` with their fresh authorities (`authNamesFreshG_alloc`): what the
`NewServer_dist` takes (`Hlslot`, and `Hγa` with auth on). -/
def memberNamesShare (γl : GName) (γa : EtcdGrove.auth.AuthNames) : IProp GF :=
  iprop(ghostMapAuth γl (1 : Qp).half (∅ : GMap Bool lease.LessorGV) ∗ lease.lessorSlot γl ∗ authNamesFreshG γa)

end share

end etcd_dist
end EtcdGrove
end Perennial
