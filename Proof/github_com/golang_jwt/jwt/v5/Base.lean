/-
Package initialization and the vocabulary of `github.com/golang-jwt/jwt/v5` (types and names only;
PR etcd#21909: the JWT token provider's `info`, `server/v3/auth/jwt.go`, calls `jwt.Parse` and
reads the `*jwt.Token` it returns).

**A parsed token** (`jwtTokenRO p`): what `info` reads of the `*jwt.Token` `jwt.Parse` returns
without an error: its `Claims` and `Valid` fields, read-only; when the claims are a
`jwt.MapClaims` (the default `Parse` decodes into), the map, read-only, whose values are what
`encoding/json` decodes a JSON value into an `any` as (`jsonAnyOk`: nil, a string, a float64, or
another type: a bool, a slice, a map). That is a trust-boundary statement about golang-jwt and
`encoding/json`, which are not translated. Nothing here says that the signature was checked
or what the claims are: the proofs that use it do not need it.
-/
module

public import Code.github_com.golang_jwt.jwt.v5
public import GeneratedProof.github_com.golang_jwt.jwt.v5
public import Perennial.Proof.time.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace github_com.golang_jwt.jwt.v5

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.golang_jwt.jwt.v5 :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.golang_jwt.jwt.v5 :=
  build_get_is_pkg_init_wf

end github_com.golang_jwt.jwt.v5

end init

namespace EtcdGrove
namespace jwt

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A value `encoding/json` decodes into an `any`: nil, a string, a float64, or a value of
another type (bool, `[]any`, `map[string]any`). -/
def jsonAnyOk (v : GoInterface) : Prop :=
  v = GoInterface.nil ∨ (∃ s : GoString, v = interface.mkOk go.string #s) ∨
    (∃ f : w64, v = interface.mkOk go.float64 #f) ∨
    (∃ ii : GoInterfaceOk, v = GoInterface.ok ii ∧ ii.ty ≠ go.string ∧ ii.ty ≠ go.float64)

/-- The claims `cl` of a parsed token: when a `jwt.MapClaims`, a read-only map of JSON values. -/
def jwtClaimsOk (cl : GoInterface) : IProp GF :=
  iprop(∀ (ii : GoInterfaceOk), ⌜cl = GoInterface.ok ii ∧ ii.ty = github_com.golang_jwt.jwt.v5.MapClaims.ty⌝ -∗
    ∃ (m : Loc) (mm : GMap GoString GoInterface), ⌜ii.v = #m⌝ ∗ m ↦$□ mm ∗
      ⌜∀ k v, mm !! k = some v → jsonAnyOk v⌝)

instance jwtClaimsOk_persistent (cl : GoInterface) : Persistent (jwtClaimsOk (GF := GF) cl) := by
  unfold jwtClaimsOk; infer_instance

/-- **A parsed token** `p` (a `*jwt.Token`, not nil): its `Claims` and `Valid` read-only. -/
def jwtTokenRO (p : Loc) : IProp GF :=
  iprop(⌜p ≠ null⌝ ∗ ∃ (cl : GoInterface) (valid : Bool),
    structFieldRef github_com.golang_jwt.jwt.v5.Token go!"Claims" p ↦□ cl ∗
    structFieldRef github_com.golang_jwt.jwt.v5.Token go!"Valid" p ↦□ valid ∗ jwtClaimsOk cl)

instance jwtTokenRO_persistent (p : Loc) : Persistent (jwtTokenRO (GF := GF) p) := by
  unfold jwtTokenRO; infer_instance

end defs

end jwt
end EtcdGrove
end Perennial
