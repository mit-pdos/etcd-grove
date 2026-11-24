/-
The vocabulary of net/url's specs (`Spec/net/url/`): the pure functions of `Proof/net/url/Escape.lean`,
net/url's package fact `urlInit` (`Proof/net/url/PkgInit.lean`: `table` holds `encTableList`), and
`unescRes s mode`, what `unescape(s, mode)` returns as Go values (the decoded string and `nil`, or
`""` and its error, an `EscapeError` or an `InvalidHostError` of the offending bytes).
-/
module

public import Proof.net.url.PkgInit

@[expose] public section

noncomputable section

namespace Perennial

namespace net.url

section defs
variable [GooseExts] [GoGlobalContext]

/-- The error value of an `UnescErr`: `EscapeError(e)` or `InvalidHostError(e)` as an `error`. -/
def unescErrV : UnescErr → GoInterface
  | .escape e => interface.mkOk EscapeError.ty #e
  | .host e => interface.mkOk InvalidHostError.ty #e

/-- `unescape(s, mode)`'s results. -/
def unescRes (s : List w8) (mode : w8) : GoString × GoInterface :=
  match unescapeF s mode with
  | .ok t => (t, interface.nil)
  | .error e => ([], unescErrV e)

end defs

section lemmas
open Iris Iris.BI Iris.ProofMode
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The table's entry for `c`, from net/url's fact. -/
theorem urlInit_table_get (c : w8) :
    isPkgInit (PROP := IProp GF) pkg_id.net.url ⊢
      ∃ t : GoArray w8 256, globalAddr table ↦□ t ∗ ⌜t.arr[c.toNat]? = some (encTable c)⌝ := by
  iintro #Hpkg
  ihave #Hu : (urlInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iunfold urlInit at Hu
  icases Hu with ⟨%t, #Ht, %Htv⟩
  iexists t
  iframe Ht
  ipureintro
  rw [Htv]; exact encTableList_get c

end lemmas

end net.url

end Perennial
