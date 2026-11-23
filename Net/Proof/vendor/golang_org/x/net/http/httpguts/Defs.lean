/-
The vocabulary of httpguts' specs (Go 1.27.3's vendored `golang.org/x/net/http/httpguts`):

* `tokenTable` (persistent): the package variable `isTokenTable` holds, for each byte `c`, whether it
  is RFC 7230's `tchar` (`fieldByte c`, `Net/Proof/net/http/Defs.lean`), as its initializer (an array
  literal, translated) sets it; nothing writes it after. httpguts has no package initialization proof
  yet: a client takes it as a premise, as net/http's `httpEnv`.
-/
module

public import Net.Proof.net.http.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace vendor.golang_org.x.net.http.httpguts

section env
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- See the file header. -/
def tokenTable : IProp GF :=
  iprop(∃ t : GoArray Bool 256, globalAddr vendor.golang_org.x.net.http.httpguts.isTokenTable ↦□ t ∗
    ⌜∀ c : w8, t.arr[c.toNat]? = some (net.http.fieldByte c)⌝)

instance tokenTable_persistent : Persistent (tokenTable (GF := GF)) := by
  unfold tokenTable; infer_instance

end env

end vendor.golang_org.x.net.http.httpguts
end Perennial
