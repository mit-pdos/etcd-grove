/-
The authentication example's results (`examples/authkv/authkv.go`; the auth plan's E2b), restated,
with the trust base of each printed in the build log (`#print axioms`). Lean-first (no Rocq
counterpart).

* **`authkv_Main`** (`Link.lean`'s `authkv.wp_Main`): `Main()` -- one member with the simple token
  provider, auth set up and enabled, four principals' workloads inside and outside `[a, b)`, and
  checks that panic if the server let a principal do what the auth state does not permit -- does
  not panic and returns `Ok`, `Failed` or `WatchEnded` (`Spec/.../authkv/Main.lean`). **Not proved:
  a `sorry`** (`Main.lean` lists what its proof needs).
* **`authkv_Permitted`** (`Link.lean`'s `authkv.wp_Permitted`): the program's verdict
  `Permitted(who, k)` is `permittedK who k`; and **`authkv_granted_iff`** (`Model.lean`'s
  `granted_setupSt_iff`): that is the model's verdict at the set-up's state for the workload's
  users, so the program's checks are stated in the model's terms.
* **`authkv_badToken`** (`ClientAuth.lean`'s `simpleTok_ne_badToken`): the bad principal's token
  is not one the simple provider makes; **`authkv_badToken_not_issued`** (`tokIssued_badToken`,
  the auth plan's E2c): it was issued to no one, every issued token having the simple provider's
  shape; **`authkv_token_one_user`** (`auth.tokIssued_agree`, E2c): a token is issued to one user.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Link

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section results
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

/-- **`Main` does not panic** (`Link.lean`'s `authkv.wp_Main`; not proved: a `sorry`). -/
theorem authkv_Main : authkv.Main.spec (GF := GF) (hG := hG) :=
  authkv.wp_Main

/-- **`Permitted(who, k)` is `permittedK who k`** (`Link.lean`'s `authkv.wp_Permitted`). -/
theorem authkv_Permitted : authkv.Permitted.spec (GF := GF) (hG := hG) :=
  authkv.wp_Permitted

end results

/-- **The program's verdict is the model's at the set-up's state**, for a point request of a
non-empty key by `u` or `v` with a revision (`Model.lean`'s `granted_setupSt_iff`). -/
theorem authkv_granted_iff (rev r : Nat) (op : auth.PermType) (who k : GoString) (hr : r ≠ 0)
    (hk : k ≠ []) (hw : who = go!"u" ∨ who = go!"v") :
    auth.granted (authkv.setupSt rev) ⟨who, r⟩ k [] op ↔ authkv.permittedK who k :=
  authkv.granted_setupSt_iff rev r op who k hr hk hw

/-- **The bad token is not the simple provider's** (`ClientAuth.lean`'s `simpleTok_ne_badToken`). -/
theorem authkv_badToken (pre : GoString) (idx : w64) : auth.simpleTok pre idx ≠ authkv.badToken :=
  authkv.simpleTok_ne_badToken pre idx

/-- **The bad token was issued to no one** (`ClientAuth.lean`'s `tokIssued_badToken`; E2c). -/
theorem authkv_badToken_not_issued {GF : BundledGFunctors} [AllG GF] (γa : auth.AuthNames)
    (u : GoString) : auth.tokIssued (GF := GF) γa authkv.badToken u ⊢ False :=
  authkv.tokIssued_badToken γa u

/-- **A token is issued to one user** (`Tokens.lean`'s `auth.tokIssued_agree`; E2c). -/
theorem authkv_token_one_user {GF : BundledGFunctors} [AllG GF] (γa : auth.AuthNames)
    (t u1 u2 : GoString) : auth.tokIssued (GF := GF) γa t u1 ∗ auth.tokIssued γa t u2 ⊢ ⌜u1 = u2⌝ :=
  auth.tokIssued_agree γa t u1 u2

#print axioms authkv_Main
#print axioms authkv_Permitted
#print axioms authkv_granted_iff
#print axioms authkv_badToken
#print axioms authkv_badToken_not_issued
#print axioms authkv_token_one_user

end EtcdGrove
end Perennial
