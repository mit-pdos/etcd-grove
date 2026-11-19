/-
Lean-first (no Rocq counterpart).

# An output's `Raw` is what its plain fields encode (k8s 7g step 5)

`notes/k8s-7g-scope.md` §2.3's premise "each output's `Raw` is the deep value its plain fields encode", for the
driver's unary calls (`call`'s post, the model's `ioOk`).

- `RawRel x y r` (moved from `RealBridge`, step 5): the plain-field relation (an object without the
  `Annotated` bit, a list with non-nil `Items` whose objects `encodeItems` is injective on, an error the
  store returns for the output's error kind; a client error, `EOther`, has none).
- `rawResp y`: the checker's `Response` of the output's `Raw` (`realcheck.go`'s
  `correctness.Response{Object: out.Raw.Object, Err: out.Raw.Err}`).
- `rawOk x y`: `rawResp y` has a view (`respRep`, persistent) that `RawRel x (plainOut y)` relates to the
  output's plain fields.
- `wrawOk s0 x y`: a watch that ran (not skipped, its `Watch` call not failed) received, in its `Raw`,
  events (`evsRO`) whose driver records its plain value encodes, and which mark revisions after the seeded
  revision `s0` past the initial ones (`WatchFromL`, B5's premise).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.EvRep
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealWatch

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI k8s_etcd3 k8sDeep
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input Output item)

section go
variable [GooseExts]

/-! ## The plain-field relation -/

/-- **The store's answer `r` is what the output `y`'s plain fields encode** for the unary input `x`: an
object (its plain fields; the driver's objects are never `Annotated`), a list (its encoded items, objects
`encodeItems` is injective on (`itemOk`), never a nil slice; its resource version, continue token and remaining
count), or an error: "not found", "key exists" (key
and resource version), a callback's rejection (the delete's or the update's sentinel), "invalid object" (key
and `Check`'s message, stage 7g option (C)), too large. A client error (`EOther`) has no encoding. -/
def RawRel (x : Input) (y : Output) (r : RResp) : Prop :=
  if y.Err' = W64 0 then
    if x.Kind' = W64 4 then
      ∃ its, (∀ o ∈ its, itemOk o) ∧ y.Items' = encItemsL its ∧ r = ⟨.list (some its) y.ListRV' y.Continue'
        (if y.HasRemaining' then some y.Remaining' else none), .none⟩
    else r = ⟨.obj (objOfL y), .none⟩
  else if y.Err' = W64 1 then r = ⟨.nil, .deep (.storageErr (W64 1) y.ErrKey' y.ErrRV' .nil)⟩
  else if y.Err' = W64 2 then r = ⟨.nil, .deep (.storageErr (W64 2) y.ErrKey' y.ErrRV' .nil)⟩
  else if y.Err' = W64 3 then r = ⟨.nil, if x.Kind' = W64 1 then delRejE else updRejE⟩
  else if y.Err' = W64 5 then
    r = ⟨.nil, .deep (.storageErr (W64 4) y.ErrKey' 0 (.errString y.ErrMsg'))⟩
  else if y.Err' = W64 6 then r = ⟨.nil, tooLargeE⟩
  else False

end go

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The checker's `Response` of an output's `Raw`** (`realcheck.go`: `correctness.Response{Object:
out.Raw.Object, Err: out.Raw.Err}`). -/
def rawResp (y : Output) : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response :=
  ⟨y.Raw'.Object', y.Raw'.Err'⟩

/-- **The output's `Raw` is what its plain fields encode** for the unary input `x` (persistent). -/
def rawOk (x : Input) (y : Output) : IProp GF :=
  iprop(∃ rr : RResp, respRep (rawResp y) rr ∗ ⌜RawRel x (plainOut y) rr⌝)

instance rawOk_persistent (x : Input) (y : Output) : Persistent (rawOk (GF := GF) x y) := by
  unfold rawOk; infer_instance

/-- **A watch's `Raw` events** (see the file header; persistent). -/
def wrawOk (s0 : w64) (x : Input) (y : Output) : IProp GF :=
  iprop(⌜x.Skip' = true ∨ y.WFailed' = true⌝ ∨
    ∃ rs : List REv, evsRO y.Raw'.Events' rs ∗
      ⌜k8s_etcd3.decWEventsL y.WEvents' = some (rs.map toWEvL) ∧ WatchFromL s0 x (rs.map toWEvL)⌝)

instance wrawOk_persistent (s0 : w64) (x : Input) (y : Output) :
    Persistent (wrawOk (GF := GF) s0 x y) := by
  unfold wrawOk; infer_instance

end defs

end k8s_correctness
end EtcdGrove
end Perennial
