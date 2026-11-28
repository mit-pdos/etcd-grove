/- Lean-first (no Rocq counterpart).

# The driver's table without a heap (for the deployment's start)

A service table (`GrpcSvc`) holds no heap (its entries are wire parts and ghost-level specs), but the
driver's (`drvSvc`, `Svc.lean`) is written, as its proofs are, in a section with a machine's heap
(`HeapGS`), which the deployment's start, before any machine runs, does not have. `drvSvcG` is the same
table written over the global ghost state only (`GooseGlobalGS`): the same definitions, with the
stream library's `upAt`/`upClosed` and the counter's `idTok` restated at that level. `drvSvc_eq_G`: at
a machine's heap, the two are the same term (`rfl`), so the address the start sets to serve `drvSvcG`
serves every machine's `drvSvc`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.Svc

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode EtcdGrove

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

section global
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF]

/-- `idTok`, over the global ghost state. -/
def idTokG (γid : GName) (id : w64) : IProp GF :=
  ghostMapElem (K := w64) (V := Unit) γid id (DFrac.own 1) ()

/-- A `StringValue`'s wire part (`pbStringValue`'s, `pbStringValueS`'s). -/
abbrev strWireG : ProtoWire :=
  ⟨google_golang_org.protobuf.types.known.wrapperspb.StringValue.ty, GoString, stringValueTree,
    inferInstance⟩

/-- `upAt` at a `StringValue` stream, over the global ghost state. -/
def upAtG (γ : StreamNames) (i : Nat) (m : GoString) : IProp GF := monoListIdxOwn γ.up i m

/-- `upClosed` at a `StringValue` stream, over the global ghost state. -/
def upClosedG (γ : StreamNames) (L : List GoString) : IProp GF := dghostVar γ.upEnd DFrac.discard L

def echoSpecG (γid : GName) : GrpcMd → GoString → (GoString → IProp GF) → (GoString → IProp GF) →
    IProp GF :=
  fun _ (v : GoString) (Φ : GoString → IProp GF) _ =>
    iprop(∃ (id : w64) (w : GoString), ⌜v = mkVal id w ∧ wordOk w⌝ ∗
      idTokG (GF := GF) γid id ∗ Φ (v ++ go!"#1"))

def failSpecG : GrpcMd → GoString → (GoString → IProp GF) → (GoString → IProp GF) → IProp GF :=
  fun _ (v : GoString) _ (Ψe : GoString → IProp GF) => Ψe v

def metaSpecG : GrpcMd → GoString → (GoString → IProp GF) → (GoString → IProp GF) → IProp GF :=
  fun md _ (Φ : GoString → IProp GF) _ =>
    iprop(⌜(go!",".intercalate (metadata.mdVals md mdKeyS)).length < stringValueMax⌝ ∗
      Φ (go!",".intercalate (metadata.mdVals md mdKeyS)))

def ssUpG : Nat → GoString → IProp GF := fun i _ => iprop(⌜i = 0⌝)

def ssDnG : GrpcMd → StreamNames → Nat → GoString → IProp GF := fun _ γ j m =>
  iprop(∃ v : GoString, upAtG (GF := GF) γ 0 v ∗
    ⌜j < List.length v ∧ m = List.take 1 (List.drop j v)⌝)

def csUpG : Nat → GoString → IProp GF := fun i m => iprop(⌜List.length m ≤ 1 ∧ i < 16⌝)

def csDnG : GrpcMd → StreamNames → Nat → GoString → IProp GF := fun _ γ j m =>
  iprop(⌜j = 0⌝ ∗ ∃ L : List GoString, upClosedG (GF := GF) γ L ∗ ⌜m = List.flatten L⌝)

def biUpG : Nat → GoString → IProp GF := fun _ m => iprop(⌜List.length m ≤ 1⌝)

def biDnG : GrpcMd → StreamNames → Nat → GoString → IProp GF := fun _ γ j m =>
  upAtG (GF := GF) γ j m

def strmSpecG (dn : GrpcMd → StreamNames → Nat → GoString → IProp GF) :
    GrpcMd → StreamNames → (Nat → GoString → IProp GF) → IProp GF :=
  fun md γ Dn => iprop(□ ∀ (j : Nat) (m : GoString), Dn j m -∗ dn md γ j m)

/-- **The service's table over the global ghost state** (`drvSvc`'s). -/
def drvSvcG (γid : GName) : GrpcSvc GF := fun name =>
  if name = echoName then some (.unary ⟨strWireG, strWireG, echoSpecG γid, false⟩)
  else if name = failName then some (.unary ⟨strWireG, strWireG, failSpecG, false⟩)
  else if name = metaName then some (.unary ⟨strWireG, strWireG, metaSpecG, false⟩)
  else if name = serverStreamName then
    some (.stream ⟨strWireG, strWireG, ssUpG, ssDnG, strmSpecG ssDnG⟩)
  else if name = clientStreamName then
    some (.stream ⟨strWireG, strWireG, csUpG, csDnG, strmSpecG csDnG⟩)
  else if name = bidiName then
    some (.stream ⟨strWireG, strWireG, biUpG, biDnG, strmSpecG biDnG⟩)
  else none

end global

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [pkg_wr : google_golang_org.protobuf.types.known.wrapperspb.Assumptions]

/-- **At a machine's heap, the table is the global one.** -/
theorem drvSvc_eq_G (γid : GName) :
    drvSvc (GF := GF) γid = drvSvcG (GF := GF) (Gg := hG.goose_globalGS) γid := rfl

end heap

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
